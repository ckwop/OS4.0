# OS 4.0 build. Runs inside the Docker image (see Readme.md); the host has no toolchain.

CROSS   ?= aarch64-linux-gnu-
AS      := $(CROSS)as
LD      := $(CROSS)ld
ASFLAGS := -g -I arch/aarch64

ARCH          := arch/aarch64
BUILD         := build
LIMINE_DIR    ?= /opt/limine
UEFI_FIRMWARE ?= /usr/share/qemu-efi-aarch64/QEMU_EFI.fd

# The kernel embeds the boot files listed in kernel.s and includes the other
# kernel sources. It is assembled once per platform, choosing the drivers.
KERNEL_DEPS := $(wildcard $(ARCH)/*.s) $(wildcard forth/*.fs) $(wildcard hal/*.fs)

# Data disks: DATA_IMG for running, TEST_IMG made fresh for every test.
DATA_IMG    ?= $(BUILD)/data.img
TEST_IMG    := $(BUILD)/test-data.img
BLOCKS_TOOL := python3 tools/blocks.py
TEST_SETUP  := $(BLOCKS_TOOL) format --force $(TEST_IMG) --blocks 1024 --volume-id 42

# Hosted: an AArch64 Linux binary run under qemu-aarch64 (milestone 2).
HOSTED      := $(BUILD)/forth-hosted
HOSTED_CMD   = qemu-aarch64 $(HOSTED) $(1)

# Bare metal: Limine boots the kernel on QEMU's virt machine (milestone 3).
# The boot disk is virtio-pci; the data disk is virtio-mmio, as our driver expects.
KERNEL_ELF := $(BUILD)/kernel.elf
BOOT_IMG   := $(BUILD)/boot.img
VIRT_CMD    = qemu-system-aarch64 -machine virt -cpu cortex-a72 -m 256M -nographic \
              -bios $(UEFI_FIRMWARE) -nic none \
              -drive file=$(BOOT_IMG),format=raw,if=virtio \
              -drive file=$(1),format=raw,if=none,id=data,cache=writeback \
              -device virtio-blk-device,drive=data -global virtio-mmio.force-legacy=false

CONSOLE := python3 tools/console-run.py

.PHONY: all build image data run run-hosted test test-hosted test-virt clean

all: build

build: $(HOSTED) $(KERNEL_ELF)

$(BUILD)/hosted/kernel.o: $(ARCH)/kernel.s $(KERNEL_DEPS)
	@mkdir -p $(@D)
	$(AS) $(ASFLAGS) --defsym HOSTED=1 -o $@ $<

$(BUILD)/virt/kernel.o: $(ARCH)/kernel.s $(KERNEL_DEPS)
	@mkdir -p $(@D)
	$(AS) $(ASFLAGS) -o $@ $<

$(BUILD)/%.o: $(ARCH)/%.s $(ARCH)/macros.s
	@mkdir -p $(@D)
	$(AS) $(ASFLAGS) -o $@ $<

$(HOSTED): $(BUILD)/hosted/kernel.o $(BUILD)/linux.o
	$(LD) -static -o $@ $^

$(KERNEL_ELF): $(BUILD)/virt/kernel.o $(BUILD)/virt.o $(BUILD)/vectors.o $(ARCH)/virt.ld
	$(LD) -T $(ARCH)/virt.ld -static -z max-page-size=0x1000 --no-warn-rwx-segments -o $@ $(filter %.o,$^)

# FAT boot disk: Limine as the UEFI removable-media loader, its config, the kernel.
image: $(BOOT_IMG)

$(BOOT_IMG): $(KERNEL_ELF) $(ARCH)/limine.conf
	rm -f $@
	truncate -s 64M $@
	mkfs.fat -F 32 -n OS40BOOT $@ >/dev/null
	mmd -i $@ ::/EFI ::/EFI/BOOT ::/boot
	mcopy -i $@ $(LIMINE_DIR)/BOOTAA64.EFI ::/EFI/BOOT/
	mcopy -i $@ $(ARCH)/limine.conf ::/boot/
	mcopy -i $@ $(KERNEL_ELF) ::/boot/kernel.elf

# A data disk to run with, made once and then kept: it holds your blocks.
data: $(DATA_IMG)

$(DATA_IMG):
	@mkdir -p $(@D)
	$(BLOCKS_TOOL) format $@

# Boot the bare-metal kernel with the serial console on this terminal.
# Leave with bye, Ctrl-D, or Ctrl-A then x.
run: $(BOOT_IMG) $(DATA_IMG)
	@$(call VIRT_CMD,$(DATA_IMG))

run-hosted: $(HOSTED) $(DATA_IMG)
	@$(call HOSTED_CMD,$(DATA_IMG))

test: test-hosted test-virt

test-hosted: $(HOSTED)
	TEST_SETUP="$(TEST_SETUP)" sh tools/run-tests.sh "$(CONSOLE) $(call HOSTED_CMD,$(TEST_IMG))" tests

# The same tests over the serial console, plus bare-metal-only ones.
test-virt: $(BOOT_IMG)
	TEST_SETUP="$(TEST_SETUP)" TEST_TIMEOUT=90 sh tools/run-tests.sh \
	  "$(CONSOLE) $(call VIRT_CMD,$(TEST_IMG))" tests tests/baremetal

clean:
	rm -rf $(BUILD) tests/*.actual tests/*/*.actual
