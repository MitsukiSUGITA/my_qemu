#!/bin/bash

MEM_SIZE=${1:-4G}

echo "[INFO] Starting Source VM (qcow2 pure) with Memory: ${MEM_SIZE}"

# 変更点: file.locking=off, metadata_port_src.sock, port 4446
QEMU_ALLOW_IVSHMEM_MIGRATION=1 \
/home/mitsuki/my_qemu/build/qemu-system-x86_64 \
     -name migration_src \
     -enable-kvm \
     -m ${MEM_SIZE} \
     -cpu host \
     -smp 2 \
     -L /usr/share/qemu \
     -drive file=/var/lib/libvirt/images/migration.qcow2,format=qcow2,if=virtio,cache=none,file.locking=off,id=drive-virtio-disk0 \
     -drive file=/var/lib/libvirt/images/mongo_data.qcow2,format=qcow2,if=virtio,cache=none,file.locking=off,id=mongo-disk \
     -netdev bridge,id=net0,br=br0 \
     -device virtio-net-pci,netdev=net0,mac=52:54:00:12:34:56 \
     -device virtio-serial-pci \
     -chardev socket,id=meta_char,path=/tmp/metadata_port.sock,server=on,wait=off \
     -device virtserialport,chardev=meta_char,name=metadata_port \
     -object memory-backend-file,size=8M,share=on,mem-path=/dev/shm/mongo_bitmap,id=shm0 \
     -device ivshmem-plain,memdev=shm0 \
     -vnc 0.0.0.0:0 \
     -monitor stdio \
     -monitor telnet:127.0.0.1:4446,server,nowait \
     -serial file:/tmp/host_mongo_debug_src.log \
     2>&1 | tee /tmp/qemu_monitor_src.log