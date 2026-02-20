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
#include "system/ram_addr.h"

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

uint64_t mongo_evict_list = 0; // ゲストからリストの先頭GPAを受け取るための変数
extern volatile int mongo_command_flag; // MongoDBへの指令フラグ (0:なし, 1:クリア実行せよ)

// ツリー構造の末端となるデータバッチ
typedef struct {
    uint64_t entry_count; // このバッチに登録されているスキップ対象ページの総数
    uint64_t target_gpas[510];      // スキップ対象ページのGPAリスト (1ページに510エントリまで格納可能)
} SkipListLeaf;
// 転送スキップ対象を管理するツリー構造の最上位ノード
typedef struct {
    uint64_t magic;
    uint64_t mid_entry_count;     // 登録されている中間目次の総数
    uint64_t mid_level_gpas[510]; // 次の階層(中間目次)へのGPA配列
} SkipListRoot;

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

static int async_pending_count; // 非同期でキューに入ったアイテムの総数
static QemuSemaphore async_bh_completion_sem; // BH処理完了を通知するためのセマフォ

// GPAの内容を覗き見る(現在は使用していないが，今後のデバッグ用に残しておく)
static void __attribute__((unused)) hypercall_peek_work_fn(CPUState *cpu, run_on_cpu_data data)
{
    hwaddr read_len = TARGET_PAGE_SIZE; // ページサイズ分読んでみる
    hwaddr actual_mapped_len;
    bool is_write_access = false;
    char *hva = cpu_physical_memory_map(mongo_evict_list, &read_len, false);
    
    if (hva) {
        actual_mapped_len = read_len;
        printf("           Guest Memory Dump (GPA: %#llx):\n", (unsigned long long)mongo_evict_list);
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

/*
 * [第3層] 末端データ(Leaf)からのビットマップ一括更新
 * 第2層から渡された末端バッチのGPAを読み込み，
 * 個々のページに対してGPA->HVA-> RAMOffset の変換を行う．
 * "pc.ram" (メインメモリ) のみを抽出してスタック配列へ保存した後，
 * 一括でビットマップを更新する．
 */
static void process_register_leaf_batch(hwaddr batch_gpa)
{
    SkipListLeaf list_data;
    cpu_physical_memory_read(batch_gpa, &list_data, sizeof(list_data));

    if (list_data.entry_count == 0 || list_data.entry_count > 512) return; // 安全のため件数チェック (1ページに入る最大件数は512)

    RamSkipItem batch_items[512];
    size_t valid_count = 0;
    hwaddr len = TARGET_PAGE_SIZE;

    for (uint64_t i = 0; i < list_data.entry_count; i++) {
        hwaddr target_gpa = list_data.target_gpas[i];
        if (!target_gpa) continue; // 0ならスキップ (早期リターン)

        // GPA -> HVA -> RAMOffset 変換
        void *hva = cpu_physical_memory_map(target_gpa, &len, false); // GPA -> HVA 変換
        if (!hva) continue;
        ram_addr_t offset;
        RAMBlock *block = qemu_ram_block_from_host(hva, false, &offset); // HVA -> RAMOffset 変換

        // メインメモリのみを対象とし、構造体リテラルで一時配列へ格納
        if (block && strcmp(block->idstr, "pc.ram") == 0) {
            batch_items[valid_count++] = (RamSkipItem){target_gpa, offset};
        }
        cpu_physical_memory_unmap(hva, len, false, len);
    }

    if (valid_count > 0) {
        set_skip_bitmap_bulk(batch_items, valid_count); // まとめて一括登録 (バルク更新)
    }
}

/*
 * [第2層] スキップリストのツリー構造探索とアドレス解決
 * 第1層から渡されたルート目次のGPAを起点に，ツリー構造を辿る．
 * ルート目次から中間目次のGPAを取得し，さらにそこから * 末端のデータバッチ(Leaf)の
 * GPAリストを読み出して，物理アドレス変換と登録を行う第3層へ順次引き渡す．
 */
static void process_skip_tree_mid_level(hwaddr root_gpa)
{
    SkipListRoot root;
    cpu_physical_memory_read(root_gpa, &root, sizeof(root)); // ルート目次(L3)を読み込む

    if (root.magic != 0xCAFEBABE) { // マジックナンバー確認 (整合性チェック)
        fprintf(stderr, "QEMU: Invalid Evict Root Magic\n");
        return;
    }

    size_t processed = 0;
    // 中間目次ページを走査
    for (int i = 0; i < 510 && processed < root.mid_entry_count; i++) {
        if (root.mid_level_gpas[i] == 0) continue;

        // 末端データ(Leaf)のGPAリストを読み込む
        uint64_t leaf_batch_gpas[512];
        cpu_physical_memory_read(root.mid_level_gpas[i], leaf_batch_gpas, sizeof(leaf_batch_gpas));

        // 末端データ(Leaf)の走査
        for (int j = 0; j < 512 && processed < root.mid_entry_count; j++) {
            if (leaf_batch_gpas[j]) process_register_leaf_batch(leaf_batch_gpas[j]);
            processed++;
        }
    }
}

/*
 * [第1層] 転送スキップ処理の非同期エントリーポイント (Bottom Half 関数)
 * MongoDBからのトリガーによってスケジュールされ，QEMUのメインスレッド上で非同期に実行される．
 * vCPUを長時間ブロックしないよう，キューに積まれたスキップリストのルートアドレスを取り出し，
 * 実際のツリー探索処理(第2層)へ引き渡す．
 */
static void process_page_skip_bh(void *opaque)
{
    while (true) {
        qemu_mutex_lock(&evict_queue_lock);
        EvictWorkItem *item = QSIMPLEQ_FIRST(&evict_work_queue);
        if (item) QSIMPLEQ_REMOVE_HEAD(&evict_work_queue, next);
        qemu_mutex_unlock(&evict_queue_lock);

        if (!item) break; // キューが空になったら終了

        process_skip_tree_mid_level(item->root_gpa); // ツリー探索処理を開始 (第2層へ丸投げ)
        g_free(item);
        qemu_sem_post(&async_bh_completion_sem); // アイテムの処理が完了したことを通知 (セマフォ post)
    }
}

/* [Fast Path] I/Oポートハンドラ (0x1240)
 * ルートGPAをキューに積むだけ (超高速)
 */
static void hypercall_mongo_evict_work_fn_async(void)
{
    // グローバル変数 mongo_evict_list には、outl で送られた Root GPA が入っている前提
    hwaddr root_gpa = (hwaddr)mongo_evict_list; 
    EvictWorkItem *item = g_new0(EvictWorkItem, 1); // 作業アイテムを確保
    item->root_gpa = root_gpa; // ここではデータの中身をコピーせずGPAだけを持つ

    // キューに追加
    qemu_mutex_lock(&evict_queue_lock);
    QSIMPLEQ_INSERT_TAIL(&evict_work_queue, item, next);
    qemu_mutex_unlock(&evict_queue_lock);

    qemu_bh_schedule(evict_bh); // BHをスケジュール (後で実行するように指示)
}

/*
 * [Sync Wait] 非同期処理(BH)が完了するのを待つ関数
 * vCPUスレッドで実行されます。
 */
static void wait_for_evict_bh_completion(void)
{
    qemu_bh_schedule(evict_bh); // QEMUのメインループに実行権を渡し、BHを確実に実行させる
    long count_to_wait = qatomic_xchg(&async_pending_count, 0); // BHに積まれている全てのアイテム数を取得
    
    if (count_to_wait > 0) {
        // アイテムの数だけセマフォを待つ（BQLは自動で解除されます）
        for (long i = 0; i < count_to_wait; i++) {
            qemu_sem_wait(&async_bh_completion_sem); // qemu_sem_wait は内部で BQL を解除し、待機中にメインループを回す．
        }
    }
}

// GPA登録データ用ポート (0x1230, 0x1234) のハンドラ
static MemTxResult hypercall_data_handler(void *opaque, hwaddr addr, uint64_t val, unsigned size, MemTxAttrs attrs)
{
    if (size == 4) { // 32ビット書き込み(outl)のみ受け付ける
        if (addr == 0) { // low port (0x1230)
            mongo_evict_list = (mongo_evict_list & 0xFFFFFFFF00000000ULL) | (uint32_t)val;
        } else if (addr == 4) { // high port (0x1234)
            mongo_evict_list = (mongo_evict_list & 0x00000000FFFFFFFFULL) | (val << 32);
        }
    }
    return MEMTX_OK;
}

// mongoDBのスキップリストのGPA登録コマンド用ポート (0x1240) ハンドラ
static MemTxResult hypercall_mongo_evict_handler(void *opaque, hwaddr addr, uint64_t val, unsigned size, MemTxAttrs attrs)
{
    // 非同期処理待ちのアイテム数をカウントアップ
    // これにより、同期関数（wait_for_evict_bh_completion）が呼ばれた際に「あと何回セマフォを待てば全ての処理が終わるか」を知ることができます。
    qatomic_inc(&async_pending_count);
    hypercall_mongo_evict_work_fn_async(); // 非同期版を呼ぶ（内部でキュー追加とBHスケジュールが行われる）
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

// 書き込みハンドラ (MongoDB -> QEMU: 受け取りました/完了しました)(ポート 0x1241)
static MemTxResult mongo_cmd_write(void *opaque, hwaddr addr, uint64_t value, 
                                   unsigned size, MemTxAttrs attrs)
{
    // MongoDBが outl(0, 0x1241) した時に呼ばれる
    if (value == 0) {
        //printf("QEMU: MongoDB acknowledged command. Flag reset.\n");
        mongo_command_flag = 0;
    }
    return MEMTX_OK; // 成功ステータスを返す
}

/* * 同期ポートハンドラ (ポート 0x1242)
 * ゲストがここに書き込むと、QEMU側の処理完了までブロックします。
 */
static MemTxResult hypercall_mongo_evict_sync_handler(void *opaque, hwaddr addr, uint64_t val, unsigned size, MemTxAttrs attrs)
{
    if (val == 1) { // 値が 1 のときだけ同期を実行
        wait_for_evict_bh_completion();
    }
    return MEMTX_OK;
}

// キャッシュクリア完了通知用ハンドラ (ポート 0x1243)
static MemTxResult hypercall_mongo_evict_sem_handler(void *opaque, hwaddr addr, uint64_t val, unsigned size, MemTxAttrs attrs)
{
    // ゲストから '1' が書き込まれたら完了とみなす
    if (val == 1) {
        mongo_clear_status = 1;
        qemu_sem_post(&mongo_clear_sem); // 待機中のマイグレーションスレッド (ram_save_setup) を起こす
    }
    return MEMTX_OK;
}

// MemoryRegionOpsの定義
static const MemoryRegionOps data_ops = { .write_with_attrs = hypercall_data_handler, .endianness = DEVICE_LITTLE_ENDIAN };
static const MemoryRegionOps mongo_evict_ops = { .write_with_attrs = hypercall_mongo_evict_handler, .endianness = DEVICE_LITTLE_ENDIAN };
static const MemoryRegionOps mongo_cmd_ops = { .read_with_attrs = mongo_cmd_read, .write_with_attrs = mongo_cmd_write, .endianness = DEVICE_LITTLE_ENDIAN };
static const MemoryRegionOps mongo_sync_ops = { .write_with_attrs = hypercall_mongo_evict_sync_handler, .endianness = DEVICE_LITTLE_ENDIAN };
static const MemoryRegionOps mongo_sem_ops = { .write_with_attrs = hypercall_mongo_evict_sem_handler, .endianness = DEVICE_LITTLE_ENDIAN };

/* ゲストからの非同期ハイパーコール処理機構 (キューとBH) の初期化 */
static void init_evict_async_mechanism(void) {
    qemu_mutex_init(&evict_queue_lock);
    evict_bh = qemu_bh_new(process_page_skip_bh, NULL); // メインスレッドで実行されるBHを作成
}

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

    // キャッシュクリア完了通知用のポート (0x1243)
    MemoryRegion *mongo_sem_mr = g_new(MemoryRegion, 1);
    memory_region_init_io(mongo_sem_mr, NULL, &mongo_sem_ops, NULL, "hypercall-mongo-sem", 1);
    memory_region_add_subregion(get_system_io(), 0x1243, mongo_sem_mr);

    pc_nic_init(pcmc, isa_bus, pcms->pcibus);

    // MongoDB連携機能の初期化
    init_evict_async_mechanism(); // QEMU側の非同期キュー処理の初期化
    ram_mongo_migration_init();   // RAMマイグレーション側のデータ構造初期化

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
