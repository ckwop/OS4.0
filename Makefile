# OS 4.0 build. Runs inside the Docker image (see Readme.md); the host has no toolchain.

CROSS   ?= aarch64-linux-gnu-
AS      := $(CROSS)as
LD      := $(CROSS)ld
ASFLAGS := -g -I arch/aarch64

ARCH          := arch/aarch64
BUILD         := build
LIMINE_DIR    ?= /opt/limine
UEFI_FIRMWARE ?= /usr/share/qemu-efi-aarch64/QEMU_EFI.fd

# The kernel embeds forth/core.fs and includes the other kernel sources.
KERNEL_DEPS := $(wildcard $(ARCH)/*.s) forth/core.fs

# Hosted: an AArch64 Linux binary run under qemu-aarch64 (milestone 2).
HOSTED     := $(BUILD)/forth-hosted
HOSTED_RUN := qemu-aarch64 $(HOSTED)

# Bare metal: Limine boots the kernel on QEMU's virt machine (milestone 3).
KERNEL_ELF := $(BUILD)/kernel.elf
BOOT_IMG   := $(BUILD)/boot.img
VIRT_RUN   := qemu-system-aarch64 -machine virt -cpu cortex-a72 -m 256M -nographic \
              -bios $(UEFI_FIRMWARE) -drive file=$(BOOT_IMG),format=raw,if=virtio -nic none

.PHONY: all build image run run-hosted test test-hosted test-virt clean

all: build

build: $(HOSTED) $(KERNEL_ELF)

$(BUILD)/kernel.o: $(ARCH)/kernel.s $(KERNEL_DEPS)
	@mkdir -p $(@D)
	$(AS) $(ASFLAGS) -o $@ $<

$(BUILD)/%.o: $(ARCH)/%.s $(ARCH)/macros.s
	@mkdir -p $(@D)
	$(AS) $(ASFLAGS) -o $@ $<

$(HOSTED): $(BUILD)/kernel.o $(BUILD)/linux.o
	$(LD) -static -o $@ $^

$(KERNEL_ELF): $(BUILD)/kernel.o $(BUILD)/virt.o $(BUILD)/vectors.o $(ARCH)/virt.ld
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

# Boot the bare-metal kernel with the serial console on this terminal.
# Leave with bye, Ctrl-D, or Ctrl-A then x.
run: $(BOOT_IMG)
	@$(VIRT_RUN)

run-hosted: $(HOSTED)
	@$(HOSTED_RUN)

test: test-hosted test-virt

test-hosted: $(HOSTED)
	sh tools/run-tests.sh "$(HOSTED_RUN)" tests

# The same tests over the serial console, plus bare-metal-only ones.
test-virt: $(BOOT_IMG)
	TEST_TIMEOUT=60 sh tools/run-tests.sh "python3 tools/serial-run.py $(VIRT_RUN)" tests tests/baremetal

clean:
	rm -rf $(BUILD) tests/*.actual tests/*/*.actual
