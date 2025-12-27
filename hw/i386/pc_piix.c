/*
 * QEMU PC System Emulator
 *
 * Copyright (c) 2003-2004 Fabrice Bellard
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
 * THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 * THE SOFTWARE.
 */

#include "qemu/osdep.h"
#include CONFIG_DEVICES

#include "qemu/units.h"
#include "qemu/main-loop.h" // BH用
#include "hw/char/parallel-isa.h"
#include "hw/i386/x86.h"
#include "hw/i386/pc.h"
#include "hw/i386/apic.h"
#include "hw/pci-host/i440fx.h"
#include "hw/southbridge/piix.h"
#include "hw/display/ramfb.h"
#include "hw/pci/pci.h"
#include "hw/pci/pci_ids.h"
#include "hw/usb.h"
#include "net/net.h"
#include "hw/ide/pci.h"
#include "hw/irq.h"
#include "system/kvm.h"
#include "hw/i386/kvm/clock.h"
#include "hw/sysbus.h"
#include "hw/i2c/smbus_eeprom.h"
#include "system/memory.h"
#include "hw/acpi/acpi.h"
#include "hw/vfio/types.h"
#include "qapi/error.h"
#include "qemu/error-report.h"
#include "system/xen.h"
#ifdef CONFIG_XEN
#include <xen/hvm/hvm_info_table.h>
#include "hw/xen/xen_pt.h"
#include "hw/xen/xen_igd.h"
#endif
#include "hw/xen/xen-x86.h"
#include "hw/xen/xen.h"
#include "migration/global_state.h"
#include "migration/misc.h"
#include "system/runstate.h"
#include "system/numa.h"
#include "hw/hyperv/vmbus-bridge.h"
#include "hw/mem/nvdimm.h"
#include "hw/uefi/var-service-api.h"
#include "hw/i386/acpi-build.h"
#include "target/i386/cpu.h"
#include "migration/ram.h"
#include "exec/target_page.h"

#define XEN_IOAPIC_NUM_PIRQS 128ULL

static GlobalProperty pc_piix_compat_defaults[] = {
    { TYPE_RAMFB_DEVICE, "use-legacy-x86-rom", "true" },
    { TYPE_VFIO_PCI_NOHOTPLUG, "use-legacy-x86-rom", "true" },
};
static const size_t pc_piix_compat_defaults_len =
    G_N_ELEMENTS(pc_piix_compat_defaults);

/*
 * Return the global irq number corresponding to a given device irq
 * pin. We could also use the bus number to have a more precise mapping.
 */
static int pc_pci_slot_get_pirq(PCIDevice *pci_dev, int pci_intx)
{
    int slot_addend;
    slot_addend = PCI_SLOT(pci_dev->devfn) - 1;
    return (pci_intx + slot_addend) & 3;
}

static void piix_intx_routing_notifier_xen(PCIDevice *dev)
{
    int i;

    /* Scan for updates to PCI link routes. */
    for (i = 0; i < PIIX_NUM_PIRQS; i++) {
        const PCIINTxRoute route = pci_device_route_intx_to_irq(dev, i);
        const uint8_t v = route.mode == PCI_INTX_ENABLED ? route.irq : 0;
        xen_set_pci_link_route(i, v);
    }
}
struct init_skip_gpa_list {
    uint64_t *gpa;          // Guest Physical Address を格納
    uint64_t *ram_offset;   // RAM内オフセットを格納
    size_t num;             // 現在のGPA数
    size_t capacity;        // 配列の容量
};

// 構造体インスタンスの外部宣言
extern struct init_skip_gpa_list skip_gpa_list;
// ゲストからGVAを受け取るためのグローバル変数
uint64_t data_from_guest = 0;
// ゲストからリストの先頭GPAを受け取るための変数（既存のdata_from_guestを流用可能だが、ここでは分離）
uint64_t mongo_evict_list = 0;
// MongoDBへの指令フラグ (0:なし, 1:クリア実行せよ)
extern volatile int mongo_command_flag; 
// mongoDB内の転送をスキップするキャッシュリスト構造体
#define BATCH_SIZE 510
// L1: データ本体 (4KB)
typedef struct {
    uint64_t count;
    uint64_t total_pages;
    uint64_t gpa_list[BATCH_SIZE];
} mongoDB_evict_List;

// L3: ルート目次 (4KB)
typedef struct {
    uint64_t magic;
    uint64_t total_batches;
    uint64_t l2_index_gpas[510]; // L2ページ(中間目次)へのGPAリスト
} EvictRootDirectory;

/* 作業用キューのアイテム定義 */
typedef struct EvictWorkItem {
    hwaddr root_gpa;
    QSIMPLEQ_ENTRY(EvictWorkItem) next;
} EvictWorkItem;
/* 作業用キューのヘッド定義 */
static QSIMPLEQ_HEAD(, EvictWorkItem) evict_work_queue = 
    QSIMPLEQ_HEAD_INITIALIZER(evict_work_queue);
/* キュー操作用のロック */
static QemuMutex evict_queue_lock;
static QEMUBH *evict_bh = NULL;

// 比較関数プロトタイプ (static宣言だと見えないので、ここでもstaticで同等のものを作るか、ram.cから公開するかですが、ここでは単純に再定義します)
static int compare_skip_item_local(const void *a, const void *b) {
    const RamSkipItem *ia = (const RamSkipItem *)a;
    const RamSkipItem *ib = (const RamSkipItem *)b;
    if (ia->ram_offset < ib->ram_offset) return -1;
    if (ia->ram_offset > ib->ram_offset) return 1;
    return 0;
}
// 非同期でキューに入ったアイテムの総数
static int async_pending_count;
// BH処理完了を通知するためのセマフォ
static QemuSemaphore async_bh_completion_sem;

// デバッグ用統計カウンター
/*
static uint64_t debug_total_batches_received = 0; // ハンドラが呼ばれた回数
static uint64_t debug_total_pages_processed = 0;  // リストから取り出した総ページ数
static uint64_t debug_mapping_failures = 0;       // GPA -> HVA 変換失敗数
static uint64_t debug_ramblock_failures = 0;      // HVA -> RAMBlock 変換失敗数
*/

// 時間計測マクロ
static uint64_t diff_ns(struct timespec s, struct timespec e) {
    return (uint64_t)((e.tv_sec - s.tv_sec) * 1000000000ULL + (e.tv_nsec - s.tv_nsec));
}

#define TIMER_START(ts) clock_gettime(CLOCK_MONOTONIC, &ts)
#define TIMER_END(ts) clock_gettime(CLOCK_MONOTONIC, &ts)
#define TIMER_ADD(acc, s, e) acc += diff_ns(s, e)

uint64_t time_fast_path = 0;   // I/Oハンドラの滞在時間
uint64_t time_bh_total = 0;    // BH全体の処理時間
uint64_t time_bh_read_dir = 0; // 目次(L2/L3)の読み込み時間
uint64_t time_bh_process = 0;  // L1バッチ処理(Read+Map)の時間
uint64_t total_batches_processed = 0; // 処理したバッチ数

// アドレス変換と検証を行うコールバック関数
static void hypercall_work_fn(CPUState *cpu, run_on_cpu_data data)
{
    hwaddr gpa = -1; // 失敗時のために初期化
    // KVMが有効な場合
    if (kvm_enabled()) {
        // KVM_TRANSLATE ioctl を使うための構造体を準備
        struct kvm_translation trans = {
            .linear_address = data_from_guest,
        };
        // KVMに直接アドレス変換を依頼する
        int ret = kvm_vcpu_ioctl(cpu, KVM_TRANSLATE, &trans);
        if (ret == 0 && trans.valid) {
            // 変換成功！
            gpa = trans.physical_address;
        } else {
            // 変換失敗
            gpa = -1;
        }
    // TCG (KVMなし) の場合
    } else {
        hwaddr page_gpa = cpu_get_phys_page_debug(cpu, data_from_guest);
        if (page_gpa != -1) {
            gpa = page_gpa | (data_from_guest & ~TARGET_PAGE_BITS);
        }
    }

    if (gpa != -1) {
        //GVA -> GPAの変換が成功したときのページ内容を出力
        //fprintf(stderr, "GVA: 0x%lx -> GPA: 0x%lx\n", data_from_guest, gpa);
        data_from_guest = gpa; // 次の処理のためにGPAをセット
        //hypercall_peek_work_fn(cpu, data);
        hwaddr page_len = TARGET_PAGE_SIZE;
        bool is_write = false;
        void *hva = cpu_physical_memory_map(gpa, &page_len, is_write);
        if (hva) {
            if (gpa < 0x100000) {
            cpu_physical_memory_unmap(hva, page_len, is_write, page_len);
            return; 
        }
            ram_addr_t offset_in_block;
    
            // (2) HVA から RAMBlock と「ブロック内オフセット」を取得
            RAMBlock *block = qemu_ram_block_from_host(hva, false, &offset_in_block);
    
            if (block) {
                // (3) ★重要★ GPA (gpa) ではなく、ブロック内オフセットをリストに格納
                collect_list(gpa, offset_in_block); 
            }
            cpu_physical_memory_unmap(hva, page_len, is_write, page_len);
        } else {
            fprintf(stderr, "  Failed to map GPA to HVA in hypercall_work_fn(). GPA: 0x%lx\n", gpa);
        }
    } else {
        fprintf(stderr, "  Translation to GPA failed.\n");
    }
    //print_collected_list();
}

// コールバック関数：GPAの内容を覗き見る
static void hypercall_peek_work_fn(CPUState *cpu, run_on_cpu_data data)
{
    hwaddr read_len = TARGET_PAGE_SIZE; // ページサイズ分読んでみる
    hwaddr actual_mapped_len;
    bool is_write_access = false;
    char *hva = cpu_physical_memory_map(data_from_guest, &read_len, false);
    
    if (hva) {
        actual_mapped_len = read_len;
        printf("           Guest Memory Dump (GPA: %#llx):\n", (unsigned long long)data_from_guest);
        printf("           "); // インデント
        for (int i = 0; i < actual_mapped_len; i++) {
            // unsigned charとしてバイトを読み出し、16進数2桁で表示
            printf("%02x ", (unsigned char)hva[i]);
            // 32バイトごとに改行
            if ((i + 1) % 32 == 0) {
                printf("\n           ");
            }
        }
        printf("\n");

        cpu_physical_memory_unmap(hva, actual_mapped_len, is_write_access, actual_mapped_len);
    } else {
        printf("           Failed to map GPA to HVA.\n");
    }
}

/* * ヘルパー関数: 1つのL1バッチ(510件)を処理する
 * メモリマップ -> リスト追加 -> マージ までを行う
 */
static void process_single_l1_batch(hwaddr batch_gpa)
{
    mongoDB_evict_List list_data;
    // L1バッチ構造体を読み込み
    cpu_physical_memory_read(batch_gpa, &list_data, sizeof(list_data));

    if (list_data.count == 0) return;

    // 一時保存用配列 (g_new で確保)
    RamSkipItem *batch_items = g_new(RamSkipItem, list_data.count);
    size_t valid_count = 0;

    for (uint64_t i = 0; i < list_data.count; i++) {
        hwaddr target_gpa = list_data.gpa_list[i];
        if (target_gpa == 0) continue;

        // GPA -> HVA -> RAMOffset 変換
        hwaddr page_len = TARGET_PAGE_SIZE;
        void *page_hva = cpu_physical_memory_map(target_gpa, &page_len, false);
        
        if (page_hva) {
            ram_addr_t offset_in_block;
            RAMBlock *block = qemu_ram_block_from_host(page_hva, false, &offset_in_block);
            
            if (block) {
                batch_items[valid_count].gpa = target_gpa;
                batch_items[valid_count].ram_offset = offset_in_block;
                valid_count++;
            }
            cpu_physical_memory_unmap(page_hva, page_len, false, page_len);
        }
    }

    // まとめて登録
    if (valid_count > 0) {
        qsort(batch_items, valid_count, sizeof(RamSkipItem), compare_skip_item_local);
        collect_list_bulk(batch_items, valid_count);
    }
    g_free(batch_items);
}

/* [Slow Path] Bottom Half 関数
 * ルート目次からツリーを辿り、全データを処理する
 */
static void evict_processing_bh(void *opaque)
{
    struct timespec ts_bh_start, ts_bh_end;
    struct timespec ts_tmp1, ts_tmp2;
    TIMER_START(ts_bh_start);

    while (true) {
        EvictWorkItem *item = NULL;

        qemu_mutex_lock(&evict_queue_lock);
        if (!QSIMPLEQ_EMPTY(&evict_work_queue)) {
            item = QSIMPLEQ_FIRST(&evict_work_queue);
            QSIMPLEQ_REMOVE_HEAD(&evict_work_queue, next);
        }
        qemu_mutex_unlock(&evict_queue_lock);

        if (!item) break;

        // --- 計測: 目次(Root/L2)の読み込み ---
        TIMER_START(ts_tmp1);

        // 1. ルート目次(L3)を読み込む
        EvictRootDirectory root;
        cpu_physical_memory_read(item->root_gpa, &root, sizeof(root));

        // マジックナンバー確認 (整合性チェック)
        if (root.magic == 0xCAFEBABE) {
            size_t total_batches = root.total_batches;
            size_t processed_batches = 0;

            // 2. L2(中間目次)ページを走査
            // root.l2_index_gpas には L2ページのGPAが入っている
            for (int i = 0; i < 510 && processed_batches < total_batches; i++) {
                hwaddr l2_page_gpa = root.l2_index_gpas[i];
                if (l2_page_gpa == 0) continue;

                // L2ページを読み込む
                // 1ページ(4KB)には 512個の uint64_t (L1バッチのGPA) が入る
                uint64_t l1_batch_gpas[512];
                cpu_physical_memory_read(l2_page_gpa, l1_batch_gpas, sizeof(l1_batch_gpas));

                TIMER_END(ts_tmp2);
                TIMER_ADD(time_bh_read_dir, ts_tmp1, ts_tmp2); // ここまでが目次読み込み

                // --- 計測: L1バッチ処理 (process_single_l1_batch) ---
                TIMER_START(ts_tmp1);


                // 3. L1(データバッチ)を走査
                for (int j = 0; j < 512 && processed_batches < total_batches; j++) {
                    hwaddr l1_gpa = l1_batch_gpas[j];
                    if (l1_gpa != 0) {
                        // データバッチを処理
                        process_single_l1_batch(l1_gpa);
                    }
                    processed_batches++;
                }

                TIMER_END(ts_tmp2);
                TIMER_ADD(time_bh_process, ts_tmp1, ts_tmp2); // ここまでがデータ処理
                
                // 次のループのためにタイマー再開
                TIMER_START(ts_tmp1);

            }
        } else {
            fprintf(stderr, "QEMU: Invalid Evict Root Magic\n");
        }

        g_free(item);
        // アイテムの処理が完了したことを通知 (セマフォ post)
        qemu_sem_post(&async_bh_completion_sem);
    }

    TIMER_END(ts_bh_end);
    TIMER_ADD(time_bh_total, ts_bh_start, ts_bh_end);

    // ログ出力 (毎回出すと多いので、ある程度溜まったらor完了時に出す)
    // 今回は「1回の通知」で終わる設計なので、ここで出してOKです
    /*
    printf("=== QEMU TIMING REPORT (ns) ===\n");
    printf("Fast Path (Guest Wait): %zu\n", time_fast_path);
    printf("BH Total (Background):  %zu\n", time_bh_total);
    printf("  - Dir Read Time:      %zu\n", time_bh_read_dir);
    printf("  - Batch Process Time: %zu\n", time_bh_process);
    printf("Total Batches:          %zu\n", total_batches_processed);
    printf("===============================\n");
    */

}

/* [Fast Path] I/Oポートハンドラ (0x1240)
 * ルートGPAをキューに積むだけ (超高速)
 */
static void hypercall_mongo_evict_work_fn_async(void)
{
    struct timespec ts1, ts2;
    TIMER_START(ts1);
    // グローバル変数 mongo_evict_list には、outl で送られた Root GPA が入っている前提
    hwaddr root_gpa = (hwaddr)mongo_evict_list; 

    // 作業アイテムを確保
    EvictWorkItem *item = g_new0(EvictWorkItem, 1);
    
    // ★ ここではデータの中身をコピーせず、住所(GPA)だけを持つ
    item->root_gpa = root_gpa;

    // キューに追加
    qemu_mutex_lock(&evict_queue_lock);
    QSIMPLEQ_INSERT_TAIL(&evict_work_queue, item, next);
    qemu_mutex_unlock(&evict_queue_lock);

    // BHをスケジュール (後で実行するように指示)
    qemu_bh_schedule(evict_bh);

    TIMER_END(ts2);
    TIMER_ADD(time_fast_path, ts1, ts2);
}

/* 初期化関数 (pc_init1 などで呼ぶ) */
static void init_evict_async_mechanism(void) {
    qemu_mutex_init(&evict_queue_lock);
    // BHを作成。メインスレッドで実行される
    evict_bh = qemu_bh_new(evict_processing_bh, NULL);
    // ram.c のロックも初期化
    init_skip_list_mutex();
}

/*
 * [Sync Wait] 非同期処理(BH)が完了するのを待つ関数
 * vCPUスレッドで実行されます。
 */
static void wait_for_evict_bh_completion(void)
{
    // 1. QEMUのメインループに実行権を渡し、BHを確実に実行させる
    qemu_bh_schedule(evict_bh);

    // 2. BHに積まれている全てのアイテム数を取得
    long count_to_wait = qatomic_xchg(&async_pending_count, 0); 
    
    if (count_to_wait > 0) {
        // 3. アイテムの数だけセマフォを待つ（BQLは自動で解除されます）
        for (long i = 0; i < count_to_wait; i++) {
            // qemu_sem_wait は内部で BQL を解除し、待機中にメインループを回します。
            qemu_sem_wait(&async_bh_completion_sem);
        }
    }
}

// GPA登録データ用ポート (0x1230, 0x1234) のハンドラ
static MemTxResult hypercall_data_handler(void *opaque, hwaddr addr, uint64_t val, unsigned size, MemTxAttrs attrs)
{
    if (size == 4) { // 32ビット書き込み(outl)のみ受け付ける
        if (addr == 0) { // low port (0x1230)
            data_from_guest = (data_from_guest & 0xFFFFFFFF00000000ULL) | (uint32_t)val;
        } else if (addr == 4) { // high port (0x1234)
            data_from_guest = (data_from_guest & 0x00000000FFFFFFFFULL) | (val << 32);
        }
    }
    return MEMTX_OK;
}

// GPA登録コマンド用ポート (0x1238) のハンドラ
static MemTxResult hypercall_trigger_handler(void *opaque, hwaddr addr, uint64_t val, unsigned size, MemTxAttrs attrs)
{
    CPUState *cpu = current_cpu;
    //fprintf(stderr, "QEMU: Trigger received. GVA is 0x%lx. Scheduling work...\n", data_from_guest);
    
    async_run_on_cpu(cpu, hypercall_work_fn, RUN_ON_CPU_NULL);
    bql_unlock();
    qemu_cpu_kick(cpu);
    bql_lock();
    return MEMTX_OK;
}

//  GPAの内容を覗き見る(0x1239) のハンドラ
static MemTxResult hypercall_peek_trigger_handler(void *opaque, hwaddr addr, uint64_t val,
                                                  unsigned size, MemTxAttrs attrs)
{
    CPUState *cpu = current_cpu;
    fprintf(stderr, "QEMU: Peek trigger received for GPA 0x%lx.\n", data_from_guest);
    
    async_run_on_cpu(cpu, hypercall_peek_work_fn, RUN_ON_CPU_NULL);
    bql_unlock();
    qemu_cpu_kick(cpu);
    bql_lock();
    return MEMTX_OK;
}

// mongoDBのスキップリストのGPA登録コマンド用ポート (0x1240) のハンドラ
static MemTxResult hypercall_mongo_evict_handler(void *opaque, hwaddr addr, uint64_t val, unsigned size, MemTxAttrs attrs)
{
    // data_from_guest に入っている値をリストのGPAとして保存
    mongo_evict_list = data_from_guest;
    // 非同期処理待ちのアイテム数をカウントアップ
    // これにより、同期関数（wait_for_evict_bh_completion）が呼ばれた際に「あと何回セマフォを待てば全ての処理が終わるか」を知ることができます。
    qatomic_inc(&async_pending_count);
    // 非同期版を呼ぶ（内部でキュー追加とBHスケジュールが行われる）
    hypercall_mongo_evict_work_fn_async();
    return MEMTX_OK;
}

// 読み込みハンドラ (MongoDB -> QEMU: 命令ありますか？)
static MemTxResult mongo_cmd_read(void *opaque, hwaddr addr, uint64_t *value, 
                                  unsigned size, MemTxAttrs attrs)
{
    // MongoDBが inl(0x1241) した時に呼ばれ、現在のフラグの値を返す
    /*
    printf("QEMU: MongoDB queried command flag: %d\n", mongo_command_flag);
    if(mongo_command_flag == 0) mongo_command_flag = 1;
    else if(mongo_command_flag == 1) mongo_command_flag = 0;
    */

    *value = (uint64_t)mongo_command_flag;
    
    return MEMTX_OK; // 成功ステータスを返す
}

// 書き込みハンドラ (MongoDB -> QEMU: 受け取りました/完了しました)
static MemTxResult mongo_cmd_write(void *opaque, hwaddr addr, uint64_t value, 
                                   unsigned size, MemTxAttrs attrs)
{
    // MongoDBが outl(0, 0x5004) した時に呼ばれる
    if (value == 0) {
        //printf("QEMU: MongoDB acknowledged command. Flag reset.\n");
        mongo_command_flag = 0;
    }
    
    return MEMTX_OK; // 成功ステータスを返す
}

/* * 同期ポートハンドラ
 * ゲストがここに書き込むと、QEMU側の処理完了までブロックします。
 */
static MemTxResult hypercall_mongo_evict_sync_handler(void *opaque, hwaddr addr, uint64_t val, unsigned size, MemTxAttrs attrs)
{
    // 値が 1 のときだけ同期を実行
    if (val == 1) {
        wait_for_evict_bh_completion();
    }
    return MEMTX_OK;
}

// キャッシュクリア完了通知用ハンドラ (例: ポート 0x1243)
static MemTxResult hypercall_mongo_evict_sem_handler(void *opaque, hwaddr addr, uint64_t val, unsigned size, MemTxAttrs attrs)
{
    // ゲストから '1' が書き込まれたら完了とみなす
    if (val == 1) {
        mongo_clear_status = 1;
        // 待機中のマイグレーションスレッド (ram_save_setup) を起こす
        qemu_sem_post(&mongo_clear_sem);
    }
    return MEMTX_OK;
}

// MemoryRegionOpsの定義
static const MemoryRegionOps data_ops = { .write_with_attrs = hypercall_data_handler, .endianness = DEVICE_LITTLE_ENDIAN };
static const MemoryRegionOps trigger_ops = { .write_with_attrs = hypercall_trigger_handler, .endianness = DEVICE_LITTLE_ENDIAN };
static const MemoryRegionOps peek_trigger_ops = { .write_with_attrs = hypercall_peek_trigger_handler, .endianness = DEVICE_LITTLE_ENDIAN };
static const MemoryRegionOps mongo_evict_ops = { .write_with_attrs = hypercall_mongo_evict_handler, .endianness = DEVICE_LITTLE_ENDIAN };
static const MemoryRegionOps mongo_cmd_ops = { .read_with_attrs = mongo_cmd_read, .write_with_attrs = mongo_cmd_write, .endianness = DEVICE_LITTLE_ENDIAN };
static const MemoryRegionOps mongo_sync_ops = { .write_with_attrs = hypercall_mongo_evict_sync_handler, .endianness = DEVICE_LITTLE_ENDIAN };
static const MemoryRegionOps mongo_sem_ops = { .write_with_attrs = hypercall_mongo_evict_sem_handler, .endianness = DEVICE_LITTLE_ENDIAN };

/* PC hardware initialisation */
static void pc_init1(MachineState *machine, const char *pci_type)
{
    PCMachineState *pcms = PC_MACHINE(machine);
    PCMachineClass *pcmc = PC_MACHINE_GET_CLASS(pcms);
    X86MachineState *x86ms = X86_MACHINE(machine);
    MemoryRegion *system_memory = get_system_memory();
    MemoryRegion *system_io = get_system_io();
    Object *phb;
    ISABus *isa_bus;
    Object *piix4_pm = NULL;
    qemu_irq smi_irq;
    GSIState *gsi_state;
    MemoryRegion *ram_memory;
    MemoryRegion *pci_memory = NULL;
    ram_addr_t lowmem;
    uint64_t hole64_size = 0;
    PCIDevice *pci_dev;
    DeviceState *dev;
    size_t i;

    assert(pcmc->pci_enabled);

    /*
     * Calculate ram split, for memory below and above 4G.  It's a bit
     * complicated for backward compatibility reasons ...
     *
     *  - Traditional split is 3.5G (lowmem = 0xe0000000).  This is the
     *    default value for max_ram_below_4g now.
     *
     *  - Then, to gigabyte align the memory, we move the split to 3G
     *    (lowmem = 0xc0000000).  But only in case we have to split in
     *    the first place, i.e. ram_size is larger than (traditional)
     *    lowmem.  And for new machine types (gigabyte_align = true)
     *    only, for live migration compatibility reasons.
     *
     *  - Next the max-ram-below-4g option was added, which allowed to
     *    reduce lowmem to a smaller value, to allow a larger PCI I/O
     *    window below 4G.  qemu doesn't enforce gigabyte alignment here,
     *    but prints a warning.
     *
     *  - Finally max-ram-below-4g got updated to also allow raising lowmem,
     *    so legacy non-PAE guests can get as much memory as possible in
     *    the 32bit address space below 4G.
     *
     *  - Note that Xen has its own ram setup code in xen_ram_init(),
     *    called via xen_hvm_init_pc().
     *
     * Examples:
     *    qemu -M pc-1.7 -m 4G    (old default)    -> 3584M low,  512M high
     *    qemu -M pc -m 4G        (new default)    -> 3072M low, 1024M high
     *    qemu -M pc,max-ram-below-4g=2G -m 4G     -> 2048M low, 2048M high
     *    qemu -M pc,max-ram-below-4g=4G -m 3968M  -> 3968M low (=4G-128M)
     */
    if (xen_enabled()) {
        xen_hvm_init_pc(pcms, &ram_memory);
    } else {
        ram_memory = machine->ram;
        if (!pcms->max_ram_below_4g) {
            pcms->max_ram_below_4g = 0xe0000000; /* default: 3.5G */
        }
        lowmem = pcms->max_ram_below_4g;
        if (machine->ram_size >= pcms->max_ram_below_4g) {
            if (pcmc->gigabyte_align) {
                if (lowmem > 0xc0000000) {
                    lowmem = 0xc0000000;
                }
                if (lowmem & (1 * GiB - 1)) {
                    warn_report("Large machine and max_ram_below_4g "
                                "(%" PRIu64 ") not a multiple of 1G; "
                                "possible bad performance.",
                                pcms->max_ram_below_4g);
                }
            }
        }

        if (machine->ram_size >= lowmem) {
            x86ms->above_4g_mem_size = machine->ram_size - lowmem;
            x86ms->below_4g_mem_size = lowmem;
        } else {
            x86ms->above_4g_mem_size = 0;
            x86ms->below_4g_mem_size = machine->ram_size;
        }
    }

    pc_machine_init_sgx_epc(pcms);
    x86_cpus_init(x86ms, pcmc->default_cpu_version);

    if (kvm_enabled()) {
        kvmclock_create(pcmc->kvmclock_create_always);
    }

    pci_memory = g_new(MemoryRegion, 1);
    memory_region_init(pci_memory, NULL, "pci", UINT64_MAX);

    phb = OBJECT(qdev_new(TYPE_I440FX_PCI_HOST_BRIDGE));
    object_property_add_child(OBJECT(machine), "i440fx", phb);
    object_property_set_link(phb, PCI_HOST_PROP_RAM_MEM,
                             OBJECT(ram_memory), &error_fatal);
    object_property_set_link(phb, PCI_HOST_PROP_PCI_MEM,
                             OBJECT(pci_memory), &error_fatal);
    object_property_set_link(phb, PCI_HOST_PROP_SYSTEM_MEM,
                             OBJECT(system_memory), &error_fatal);
    object_property_set_link(phb, PCI_HOST_PROP_IO_MEM,
                             OBJECT(system_io), &error_fatal);
    object_property_set_uint(phb, PCI_HOST_BELOW_4G_MEM_SIZE,
                             x86ms->below_4g_mem_size, &error_fatal);
    object_property_set_uint(phb, PCI_HOST_ABOVE_4G_MEM_SIZE,
                             x86ms->above_4g_mem_size, &error_fatal);
    object_property_set_str(phb, I440FX_HOST_PROP_PCI_TYPE, pci_type,
                            &error_fatal);
    sysbus_realize_and_unref(SYS_BUS_DEVICE(phb), &error_fatal);

    pcms->pcibus = PCI_BUS(qdev_get_child_bus(DEVICE(phb), "pci.0"));
    pci_bus_map_irqs(pcms->pcibus,
                     xen_enabled() ? xen_pci_slot_get_pirq
                                   : pc_pci_slot_get_pirq);

    hole64_size = object_property_get_uint(phb,
                                           PCI_HOST_PROP_PCI_HOLE64_SIZE,
                                           &error_abort);

    /* allocate ram and load rom/bios */
    if (!xen_enabled()) {
        pc_memory_init(pcms, system_memory, pci_memory, hole64_size);
    } else {
        assert(machine->ram_size == x86ms->below_4g_mem_size +
                                    x86ms->above_4g_mem_size);

        pc_system_flash_cleanup_unused(pcms);
        if (machine->kernel_filename != NULL) {
            /* For xen HVM direct kernel boot, load linux here */
            xen_load_linux(pcms);
        }
    }

    gsi_state = pc_gsi_create(&x86ms->gsi, true);

    pci_dev = pci_new_multifunction(-1, pcms->south_bridge);
    object_property_set_bool(OBJECT(pci_dev), "has-usb",
                             machine_usb(machine), &error_abort);
    object_property_set_bool(OBJECT(pci_dev), "has-acpi",
                             x86_machine_is_acpi_enabled(x86ms),
                             &error_abort);
    object_property_set_bool(OBJECT(pci_dev), "has-pic", false,
                             &error_abort);
    object_property_set_bool(OBJECT(pci_dev), "has-pit", false,
                             &error_abort);
    qdev_prop_set_uint32(DEVICE(pci_dev), "smb_io_base", 0xb100);
    object_property_set_bool(OBJECT(pci_dev), "smm-enabled",
                             x86_machine_is_smm_enabled(x86ms),
                             &error_abort);
    dev = DEVICE(pci_dev);
    for (i = 0; i < ISA_NUM_IRQS; i++) {
        qdev_connect_gpio_out_named(dev, "isa-irqs", i, x86ms->gsi[i]);
    }
    pci_realize_and_unref(pci_dev, pcms->pcibus, &error_fatal);

    if (xen_enabled()) {
        pci_device_set_intx_routing_notifier(
                    pci_dev, piix_intx_routing_notifier_xen);

        /*
         * Xen supports additional interrupt routes from the PCI devices to
         * the IOAPIC: the four pins of each PCI device on the bus are also
         * connected to the IOAPIC directly.
         * These additional routes can be discovered through ACPI.
         */
        pci_bus_irqs(pcms->pcibus, xen_intx_set_irq, pci_dev,
                     XEN_IOAPIC_NUM_PIRQS);
    }

    isa_bus = ISA_BUS(qdev_get_child_bus(DEVICE(pci_dev), "isa.0"));
    x86ms->rtc = ISA_DEVICE(object_resolve_path_component(OBJECT(pci_dev),
                                                          "rtc"));
    piix4_pm = object_resolve_path_component(OBJECT(pci_dev), "pm");
    dev = DEVICE(object_resolve_path_component(OBJECT(pci_dev), "ide"));
    pci_ide_create_devs(PCI_DEVICE(dev));
    pcms->idebus[0] = qdev_get_child_bus(dev, "ide.0");
    pcms->idebus[1] = qdev_get_child_bus(dev, "ide.1");


    if (x86ms->pic == ON_OFF_AUTO_ON || x86ms->pic == ON_OFF_AUTO_AUTO) {
        pc_i8259_create(isa_bus, gsi_state->i8259_irq);
    }

    ioapic_init_gsi(gsi_state, phb);

    if (tcg_enabled()) {
        x86_register_ferr_irq(x86ms->gsi[13]);
    }

    pc_vga_init(isa_bus, pcms->pcibus);

    /* init basic PC hardware */
    pc_basic_device_init(pcms, isa_bus, x86ms->gsi, x86ms->rtc,
                         !MACHINE_CLASS(pcmc)->no_floppy, 0x4);

    qemu_sem_init(&async_bh_completion_sem, 0); // 初期値 0
    qatomic_set(&async_pending_count, 0);
    // アドレス取得用のトリガーポート (0x1230 - 0x1237)
    MemoryRegion *data_mr = g_new(MemoryRegion, 1);
    memory_region_init_io(data_mr, NULL, &data_ops, NULL, "hypercall-data", 8);
    memory_region_add_subregion(get_system_io(), 0x1230, data_mr);

    // GVA -> GPAの変換を行い、スキップリストに追加するトリガーポート (0x1238)
    MemoryRegion *trigger_mr = g_new(MemoryRegion, 1);
    memory_region_init_io(trigger_mr, NULL, &trigger_ops, NULL, "hypercall-trigger", 1);
    memory_region_add_subregion(get_system_io(), 0x1238, trigger_mr);

    // ページ覗き見用のトリガーポート (0x1239)
    MemoryRegion *peek_mr = g_new(MemoryRegion, 1);
    memory_region_init_io(peek_mr, NULL, &peek_trigger_ops, NULL, "hypercall-peek", 1);
    memory_region_add_subregion(get_system_io(), 0x1239, peek_mr);

    // mongoDBのスキップリスト作成用のトリガーポート (0x1240)
    MemoryRegion *mongo_evict_mr = g_new(MemoryRegion, 1);
    memory_region_init_io(mongo_evict_mr, NULL, &mongo_evict_ops, NULL, "hypercall-mongo-evict", 1);
    memory_region_add_subregion(get_system_io(), 0x1240, mongo_evict_mr);

    // mongoDBへの指令フラグ用のトリガーポート (0x1241)
    MemoryRegion *mongo_cmd_mr = g_new(MemoryRegion, 1);
    memory_region_init_io(mongo_cmd_mr, NULL, &mongo_cmd_ops, NULL, "hypercall-mongo-cmd", 1);
    memory_region_add_subregion(get_system_io(), 0x1241, mongo_cmd_mr);

    // mongoDB同期待機用のポート (0x1242)
    MemoryRegion *mongo_sync_mr = g_new(MemoryRegion, 1);
    memory_region_init_io(mongo_sync_mr, NULL, &mongo_sync_ops, NULL, "hypercall-mongo-sync", 1);
    memory_region_add_subregion(get_system_io(), 0x1242, mongo_sync_mr);

    // mongoDB同期待機用のポート (0x1243)
    MemoryRegion *mongo_sem_mr = g_new(MemoryRegion, 1);
    memory_region_init_io(mongo_sem_mr, NULL, &mongo_sem_ops, NULL, "hypercall-mongo-sem", 1);
    memory_region_add_subregion(get_system_io(), 0x1243, mongo_sem_mr);

    pc_nic_init(pcmc, isa_bus, pcms->pcibus);

    // 非同期処理メカニズムの初期化
    init_evict_async_mechanism();
    init_mongo_migration_sync();
    if (piix4_pm) {
        smi_irq = qemu_allocate_irq(pc_acpi_smi_interrupt, first_cpu, 0);

        qdev_connect_gpio_out_named(DEVICE(piix4_pm), "smi-irq", 0, smi_irq);
        pcms->smbus = I2C_BUS(qdev_get_child_bus(DEVICE(piix4_pm), "i2c"));
        /* TODO: Populate SPD eeprom data.  */
        smbus_eeprom_init(pcms->smbus, 8, NULL, 0);

        object_property_add_link(OBJECT(machine), PC_MACHINE_ACPI_DEVICE_PROP,
                                 TYPE_HOTPLUG_HANDLER,
                                 (Object **)&x86ms->acpi_dev,
                                 object_property_allow_set_link,
                                 OBJ_PROP_LINK_STRONG);
        object_property_set_link(OBJECT(machine), PC_MACHINE_ACPI_DEVICE_PROP,
                                 piix4_pm, &error_abort);
    }

    if (machine->nvdimms_state->is_enabled) {
        nvdimm_init_acpi_state(machine->nvdimms_state, system_io,
                               x86_nvdimm_acpi_dsmio,
                               x86ms->fw_cfg, OBJECT(pcms));
    }

#if defined(CONFIG_IGVM)
    /* Apply guest state from IGVM if supplied */
    if (x86ms->igvm) {
        if (IGVM_CFG_GET_CLASS(x86ms->igvm)
                ->process(x86ms->igvm, machine->cgs, false, &error_fatal) < 0) {
            g_assert_not_reached();
        }
    }
#endif
}

typedef enum PCSouthBridgeOption {
    PC_SOUTH_BRIDGE_OPTION_PIIX3,
    PC_SOUTH_BRIDGE_OPTION_PIIX4,
    PC_SOUTH_BRIDGE_OPTION_MAX,
} PCSouthBridgeOption;

static const QEnumLookup PCSouthBridgeOption_lookup = {
    .array = (const char *const[]) {
        [PC_SOUTH_BRIDGE_OPTION_PIIX3] = TYPE_PIIX3_DEVICE,
        [PC_SOUTH_BRIDGE_OPTION_PIIX4] = TYPE_PIIX4_PCI_DEVICE,
    },
    .size = PC_SOUTH_BRIDGE_OPTION_MAX
};

static int pc_get_south_bridge(Object *obj, Error **errp)
{
    PCMachineState *pcms = PC_MACHINE(obj);
    int i;

    for (i = 0; i < PCSouthBridgeOption_lookup.size; i++) {
        if (g_strcmp0(PCSouthBridgeOption_lookup.array[i],
                      pcms->south_bridge) == 0) {
            return i;
        }
    }

    error_setg(errp, "Invalid south bridge value set");
    return 0;
}

static void pc_set_south_bridge(Object *obj, int value, Error **errp)
{
    PCMachineState *pcms = PC_MACHINE(obj);

    if (value < 0) {
        error_setg(errp, "Value can't be negative");
        return;
    }

    if (value >= PCSouthBridgeOption_lookup.size) {
        error_setg(errp, "Value too big");
        return;
    }

    pcms->south_bridge = PCSouthBridgeOption_lookup.array[value];
}

#ifdef CONFIG_XEN
static void pc_xen_hvm_init(MachineState *machine)
{
    PCMachineState *pcms = PC_MACHINE(machine);

    if (!xen_enabled()) {
        error_report("xenfv machine requires the xen accelerator");
        exit(1);
    }

    pc_init1(machine, xen_igd_gfx_pt_enabled()
                      ? TYPE_IGD_PASSTHROUGH_I440FX_PCI_DEVICE
                      : TYPE_I440FX_PCI_DEVICE);

    xen_igd_reserve_slot(pcms->pcibus);
    pci_create_simple(pcms->pcibus, -1, "xen-platform");
}
#endif

static void pc_i440fx_init(MachineState *machine)
{
    pc_init1(machine, TYPE_I440FX_PCI_DEVICE);
}

#define DEFINE_I440FX_MACHINE(major, minor) \
    DEFINE_PC_VER_MACHINE(pc_i440fx, "pc-i440fx", pc_i440fx_init, false, NULL, major, minor);

#define DEFINE_I440FX_MACHINE_AS_LATEST(major, minor) \
    DEFINE_PC_VER_MACHINE(pc_i440fx, "pc-i440fx", pc_i440fx_init, true, "pc", major, minor);

static void pc_i440fx_machine_options(MachineClass *m)
{
    PCMachineClass *pcmc = PC_MACHINE_CLASS(m);
    ObjectClass *oc = OBJECT_CLASS(m);
    pcmc->default_south_bridge = TYPE_PIIX3_DEVICE;
    pcmc->pci_root_uid = 0;
    pcmc->default_cpu_version = 1;

    m->family = "pc_piix";
    m->desc = "Standard PC (i440FX + PIIX, 1996)";
    m->default_machine_opts = "firmware=bios-256k.bin";
    m->default_display = "std";
    m->default_nic = "e1000";
    m->no_floppy = !module_object_class_by_name(TYPE_ISA_FDC);
    m->no_parallel = !module_object_class_by_name(TYPE_ISA_PARALLEL);
    machine_class_allow_dynamic_sysbus_dev(m, TYPE_RAMFB_DEVICE);
    machine_class_allow_dynamic_sysbus_dev(m, TYPE_VMBUS_BRIDGE);
    machine_class_allow_dynamic_sysbus_dev(m, TYPE_UEFI_VARS_X64);

    object_class_property_add_enum(oc, "x-south-bridge", "PCSouthBridgeOption",
                                   &PCSouthBridgeOption_lookup,
                                   pc_get_south_bridge,
                                   pc_set_south_bridge);
    object_class_property_set_description(oc, "x-south-bridge",
                                     "Use a different south bridge than PIIX3");
    compat_props_add(m->compat_props,
                     pc_piix_compat_defaults, pc_piix_compat_defaults_len);
}

static void pc_i440fx_machine_10_2_options(MachineClass *m)
{
    pc_i440fx_machine_options(m);
}

DEFINE_I440FX_MACHINE_AS_LATEST(10, 2);

static void pc_i440fx_machine_10_1_options(MachineClass *m)
{
    pc_i440fx_machine_10_2_options(m);
    m->smbios_memory_device_size = 2047 * TiB;
    compat_props_add(m->compat_props, hw_compat_10_1, hw_compat_10_1_len);
    compat_props_add(m->compat_props, pc_compat_10_1, pc_compat_10_1_len);
}

DEFINE_I440FX_MACHINE(10, 1);

static void pc_i440fx_machine_10_0_options(MachineClass *m)
{
    pc_i440fx_machine_10_1_options(m);
    compat_props_add(m->compat_props, hw_compat_10_0, hw_compat_10_0_len);
    compat_props_add(m->compat_props, pc_compat_10_0, pc_compat_10_0_len);
}

DEFINE_I440FX_MACHINE(10, 0);

static void pc_i440fx_machine_9_2_options(MachineClass *m)
{
    pc_i440fx_machine_10_0_options(m);
    compat_props_add(m->compat_props, hw_compat_9_2, hw_compat_9_2_len);
    compat_props_add(m->compat_props, pc_compat_9_2, pc_compat_9_2_len);
}

DEFINE_I440FX_MACHINE(9, 2);

static void pc_i440fx_machine_9_1_options(MachineClass *m)
{
    pc_i440fx_machine_9_2_options(m);
    compat_props_add(m->compat_props, hw_compat_9_1, hw_compat_9_1_len);
    compat_props_add(m->compat_props, pc_compat_9_1, pc_compat_9_1_len);
}

DEFINE_I440FX_MACHINE(9, 1);

static void pc_i440fx_machine_9_0_options(MachineClass *m)
{
    PCMachineClass *pcmc = PC_MACHINE_CLASS(m);

    pc_i440fx_machine_9_1_options(m);
    m->smbios_memory_device_size = 16 * GiB;

    compat_props_add(m->compat_props, hw_compat_9_0, hw_compat_9_0_len);
    compat_props_add(m->compat_props, pc_compat_9_0, pc_compat_9_0_len);
    pcmc->isa_bios_alias = false;
}

DEFINE_I440FX_MACHINE(9, 0);

static void pc_i440fx_machine_8_2_options(MachineClass *m)
{
    PCMachineClass *pcmc = PC_MACHINE_CLASS(m);

    pc_i440fx_machine_9_0_options(m);

    compat_props_add(m->compat_props, hw_compat_8_2, hw_compat_8_2_len);
    compat_props_add(m->compat_props, pc_compat_8_2, pc_compat_8_2_len);
    /* For pc-i44fx-8.2 and 8.1, use SMBIOS 3.X by default */
    pcmc->default_smbios_ep_type = SMBIOS_ENTRY_POINT_TYPE_64;
}

DEFINE_I440FX_MACHINE(8, 2);

static void pc_i440fx_machine_8_1_options(MachineClass *m)
{
    PCMachineClass *pcmc = PC_MACHINE_CLASS(m);

    pc_i440fx_machine_8_2_options(m);
    pcmc->broken_32bit_mem_addr_check = true;

    compat_props_add(m->compat_props, hw_compat_8_1, hw_compat_8_1_len);
    compat_props_add(m->compat_props, pc_compat_8_1, pc_compat_8_1_len);
}

DEFINE_I440FX_MACHINE(8, 1);

static void pc_i440fx_machine_8_0_options(MachineClass *m)
{
    PCMachineClass *pcmc = PC_MACHINE_CLASS(m);

    pc_i440fx_machine_8_1_options(m);
    compat_props_add(m->compat_props, hw_compat_8_0, hw_compat_8_0_len);
    compat_props_add(m->compat_props, pc_compat_8_0, pc_compat_8_0_len);

    /* For pc-i44fx-8.0 and older, use SMBIOS 2.8 by default */
    pcmc->default_smbios_ep_type = SMBIOS_ENTRY_POINT_TYPE_32;
}

DEFINE_I440FX_MACHINE(8, 0);

static void pc_i440fx_machine_7_2_options(MachineClass *m)
{
    pc_i440fx_machine_8_0_options(m);
    compat_props_add(m->compat_props, hw_compat_7_2, hw_compat_7_2_len);
    compat_props_add(m->compat_props, pc_compat_7_2, pc_compat_7_2_len);
}

DEFINE_I440FX_MACHINE(7, 2)

static void pc_i440fx_machine_7_1_options(MachineClass *m)
{
    pc_i440fx_machine_7_2_options(m);
    compat_props_add(m->compat_props, hw_compat_7_1, hw_compat_7_1_len);
    compat_props_add(m->compat_props, pc_compat_7_1, pc_compat_7_1_len);
}

DEFINE_I440FX_MACHINE(7, 1);

static void pc_i440fx_machine_7_0_options(MachineClass *m)
{
    PCMachineClass *pcmc = PC_MACHINE_CLASS(m);
    pc_i440fx_machine_7_1_options(m);
    pcmc->enforce_amd_1tb_hole = false;
    compat_props_add(m->compat_props, hw_compat_7_0, hw_compat_7_0_len);
    compat_props_add(m->compat_props, pc_compat_7_0, pc_compat_7_0_len);
}

DEFINE_I440FX_MACHINE(7, 0);

static void pc_i440fx_machine_6_2_options(MachineClass *m)
{
    pc_i440fx_machine_7_0_options(m);
    compat_props_add(m->compat_props, hw_compat_6_2, hw_compat_6_2_len);
    compat_props_add(m->compat_props, pc_compat_6_2, pc_compat_6_2_len);
}

DEFINE_I440FX_MACHINE(6, 2);

static void pc_i440fx_machine_6_1_options(MachineClass *m)
{
    pc_i440fx_machine_6_2_options(m);
    compat_props_add(m->compat_props, hw_compat_6_1, hw_compat_6_1_len);
    compat_props_add(m->compat_props, pc_compat_6_1, pc_compat_6_1_len);
    m->smp_props.prefer_sockets = true;
}

DEFINE_I440FX_MACHINE(6, 1);

static void pc_i440fx_machine_6_0_options(MachineClass *m)
{
    pc_i440fx_machine_6_1_options(m);
    compat_props_add(m->compat_props, hw_compat_6_0, hw_compat_6_0_len);
    compat_props_add(m->compat_props, pc_compat_6_0, pc_compat_6_0_len);
}

DEFINE_I440FX_MACHINE(6, 0);

static void pc_i440fx_machine_5_2_options(MachineClass *m)
{
    pc_i440fx_machine_6_0_options(m);
    compat_props_add(m->compat_props, hw_compat_5_2, hw_compat_5_2_len);
    compat_props_add(m->compat_props, pc_compat_5_2, pc_compat_5_2_len);
}

DEFINE_I440FX_MACHINE(5, 2);

static void pc_i440fx_machine_5_1_options(MachineClass *m)
{
    PCMachineClass *pcmc = PC_MACHINE_CLASS(m);

    pc_i440fx_machine_5_2_options(m);
    compat_props_add(m->compat_props, hw_compat_5_1, hw_compat_5_1_len);
    compat_props_add(m->compat_props, pc_compat_5_1, pc_compat_5_1_len);
    pcmc->kvmclock_create_always = false;
    pcmc->pci_root_uid = 1;
}

DEFINE_I440FX_MACHINE(5, 1);

static void pc_i440fx_machine_5_0_options(MachineClass *m)
{
    pc_i440fx_machine_5_1_options(m);
    m->numa_mem_supported = true;
    compat_props_add(m->compat_props, hw_compat_5_0, hw_compat_5_0_len);
    compat_props_add(m->compat_props, pc_compat_5_0, pc_compat_5_0_len);
    m->auto_enable_numa_with_memdev = false;
}

DEFINE_I440FX_MACHINE(5, 0);

static void pc_i440fx_machine_4_2_options(MachineClass *m)
{
    pc_i440fx_machine_5_0_options(m);
    compat_props_add(m->compat_props, hw_compat_4_2, hw_compat_4_2_len);
    compat_props_add(m->compat_props, pc_compat_4_2, pc_compat_4_2_len);
}

DEFINE_I440FX_MACHINE(4, 2);

static void pc_i440fx_machine_4_1_options(MachineClass *m)
{
    pc_i440fx_machine_4_2_options(m);
    compat_props_add(m->compat_props, hw_compat_4_1, hw_compat_4_1_len);
    compat_props_add(m->compat_props, pc_compat_4_1, pc_compat_4_1_len);
}

DEFINE_I440FX_MACHINE(4, 1);

static void pc_i440fx_machine_4_0_options(MachineClass *m)
{
    PCMachineClass *pcmc = PC_MACHINE_CLASS(m);
    pc_i440fx_machine_4_1_options(m);
    pcmc->default_cpu_version = CPU_VERSION_LEGACY;
    compat_props_add(m->compat_props, hw_compat_4_0, hw_compat_4_0_len);
    compat_props_add(m->compat_props, pc_compat_4_0, pc_compat_4_0_len);
}

DEFINE_I440FX_MACHINE(4, 0);

static void pc_i440fx_machine_3_1_options(MachineClass *m)
{
    PCMachineClass *pcmc = PC_MACHINE_CLASS(m);

    pc_i440fx_machine_4_0_options(m);
    m->smbus_no_migration_support = true;
    pcmc->pvh_enabled = false;
    compat_props_add(m->compat_props, hw_compat_3_1, hw_compat_3_1_len);
    compat_props_add(m->compat_props, pc_compat_3_1, pc_compat_3_1_len);
}

DEFINE_I440FX_MACHINE(3, 1);

static void pc_i440fx_machine_3_0_options(MachineClass *m)
{
    pc_i440fx_machine_3_1_options(m);
    compat_props_add(m->compat_props, hw_compat_3_0, hw_compat_3_0_len);
    compat_props_add(m->compat_props, pc_compat_3_0, pc_compat_3_0_len);
}

DEFINE_I440FX_MACHINE(3, 0);

static void pc_i440fx_machine_2_12_options(MachineClass *m)
{
    pc_i440fx_machine_3_0_options(m);
    compat_props_add(m->compat_props, hw_compat_2_12, hw_compat_2_12_len);
    compat_props_add(m->compat_props, pc_compat_2_12, pc_compat_2_12_len);
}

DEFINE_I440FX_MACHINE(2, 12);

static void pc_i440fx_machine_2_11_options(MachineClass *m)
{
    pc_i440fx_machine_2_12_options(m);
    compat_props_add(m->compat_props, hw_compat_2_11, hw_compat_2_11_len);
    compat_props_add(m->compat_props, pc_compat_2_11, pc_compat_2_11_len);
}

DEFINE_I440FX_MACHINE(2, 11);

static void pc_i440fx_machine_2_10_options(MachineClass *m)
{
    pc_i440fx_machine_2_11_options(m);
    compat_props_add(m->compat_props, hw_compat_2_10, hw_compat_2_10_len);
    compat_props_add(m->compat_props, pc_compat_2_10, pc_compat_2_10_len);
    m->auto_enable_numa_with_memhp = false;
}

DEFINE_I440FX_MACHINE(2, 10);

static void pc_i440fx_machine_2_9_options(MachineClass *m)
{
    pc_i440fx_machine_2_10_options(m);
    compat_props_add(m->compat_props, hw_compat_2_9, hw_compat_2_9_len);
    compat_props_add(m->compat_props, pc_compat_2_9, pc_compat_2_9_len);
}

DEFINE_I440FX_MACHINE(2, 9);

static void pc_i440fx_machine_2_8_options(MachineClass *m)
{
    pc_i440fx_machine_2_9_options(m);
    compat_props_add(m->compat_props, hw_compat_2_8, hw_compat_2_8_len);
    compat_props_add(m->compat_props, pc_compat_2_8, pc_compat_2_8_len);
}

DEFINE_I440FX_MACHINE(2, 8);

static void pc_i440fx_machine_2_7_options(MachineClass *m)
{
    pc_i440fx_machine_2_8_options(m);
    compat_props_add(m->compat_props, hw_compat_2_7, hw_compat_2_7_len);
    compat_props_add(m->compat_props, pc_compat_2_7, pc_compat_2_7_len);
}

DEFINE_I440FX_MACHINE(2, 7);

static void pc_i440fx_machine_2_6_options(MachineClass *m)
{
    X86MachineClass *x86mc = X86_MACHINE_CLASS(m);
    PCMachineClass *pcmc = PC_MACHINE_CLASS(m);

    pc_i440fx_machine_2_7_options(m);
    pcmc->legacy_cpu_hotplug = true;
    x86mc->fwcfg_dma_enabled = false;
    compat_props_add(m->compat_props, hw_compat_2_6, hw_compat_2_6_len);
    compat_props_add(m->compat_props, pc_compat_2_6, pc_compat_2_6_len);
}

DEFINE_I440FX_MACHINE(2, 6);

#ifdef CONFIG_XEN
static void xenfv_machine_4_2_options(MachineClass *m)
{
    pc_i440fx_machine_4_2_options(m);
    m->desc = "Xen Fully-virtualized PC";
    m->max_cpus = HVM_MAX_VCPUS;
    m->default_machine_opts = "accel=xen,suppress-vmdesc=on";
}

DEFINE_PC_MACHINE(xenfv_4_2, "xenfv-4.2", pc_xen_hvm_init,
                  xenfv_machine_4_2_options);

static void xenfv_machine_3_1_options(MachineClass *m)
{
    pc_i440fx_machine_3_1_options(m);
    m->desc = "Xen Fully-virtualized PC";
    m->alias = "xenfv";
    m->max_cpus = HVM_MAX_VCPUS;
    m->default_machine_opts = "accel=xen,suppress-vmdesc=on";
}

DEFINE_PC_MACHINE(xenfv, "xenfv-3.1", pc_xen_hvm_init,
                  xenfv_machine_3_1_options);
#endif
