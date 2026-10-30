#!/bin/sh
OUT_DIR=../resources
set -e

create_test_img() {
	local name=$1
	local blkcount=$2
	local fatSize=$3
	dd if=/dev/zero of="$name" bs=1024 count=$blkcount
	mkfs.vfat -s 1 -F $fatSize -n "Test!" -i 12345678 "$name"
	mkdir -p mnt
	sudo mount -o loop "$name" mnt -o rw,uid=$USER,gid=$USER
	for i in $(seq 1 1000); do
	  echo "Rust is cool!" >>"mnt/long.txt"
	done
	echo "Rust is cool!" >>"mnt/short.txt"
	mkdir -p "mnt/very/long/path"
	echo "Rust is cool!" >>"mnt/very/long/path/test.txt"
	mkdir -p "mnt/very-long-dir-name"
	echo "Rust is cool!" >>"mnt/very-long-dir-name/very-long-file-name.txt"

	sudo umount mnt
}

create_test_img "$OUT_DIR/fat12.img" 1000 12
create_test_img "$OUT_DIR/fat16.img" 2500 16
create_test_img "$OUT_DIR/fat32.img" 34000 32
