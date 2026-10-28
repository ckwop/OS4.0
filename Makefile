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
KERNEL_DEPS := $(wildcard $(ARCH)/*.s) $(wildcard forth/*.fs forth/*/*.fs) $(wildcard hal/*.fs)

# Data disks: DATA_IMG for running; every test gets a fresh one of its own.
DATA_IMG    ?= $(BUILD)/data.img
BLOCKS_TOOL := python3 tools/blocks.py
TEST_SETUP  := $(BLOCKS_TOOL) format --force {disk} --blocks 1024 --volume-id 42

# App disks (DECISIONS.md #99): FAT, read only, made afresh from the directory
# APP for each run (empty without one); a test's from tests/<name>.app/.
APP         ?=
APP_IMG     := $(BUILD)/app.img
APP_SETUP   := sh tools/app-disk.sh {appdisk} {appdir}

# Hosted: an AArch64 Linux binary run under qemu-aarch64 (milestone 2).
# Arguments: the disks, separated by commas, then optionally our UDP port and
# the peer's, which carry network frames (hal/linux-net.fs).
HOSTED      := $(BUILD)/forth-hosted
HOSTED_CMD   = qemu-aarch64 $(HOSTED) $(1) $(2)

# Network backends for the bare-metal NIC: QEMU's user networking (NAT, with
# the PORTS forwarded) to run; for tests, frames as UDP to the test's own peer.
PORTS    ?= 4000 4001
NET_USER  = -netdev user$(comma)id=net$(foreach p,$(PORTS),$(comma)hostfwd=tcp::$(p)-:$(p))
NET_TEST := -netdev dgram,id=net,local.type=inet,local.host=127.0.0.1,local.port={port},remote.type=inet,remote.host=127.0.0.1,remote.port={peerport}

# Bare metal: Limine boots the kernel on QEMU's virt machine (milestone 3).
# The boot disk is virtio-pci and read-only (the OS never writes it, and tests
# share it); the data disk and the app disk ($(3), read-only) are virtio-mmio,
# as our driver expects.
KERNEL_ELF := $(BUILD)/kernel.elf
BOOT_IMG   := $(BUILD)/boot.img
VIRT_CMD    = qemu-system-aarch64 -machine virt,gic-version=2 -cpu cortex-a72 -m 1G -nographic \
              -bios $(UEFI_FIRMWARE) \
              -drive file=$(BOOT_IMG),format=raw,if=virtio,readonly=on \
              -drive file=$(1),format=raw,if=none,id=data,cache=writeback \
              -device virtio-blk-device,drive=data -global virtio-mmio.force-legacy=false \
              -drive file=$(3),format=raw,if=none,id=app,readonly=on \
              -device virtio-blk-device,drive=app \
              $(2) -device virtio-net-device,netdev=net -device virtio-rng-device

comma   := ,
CONSOLE := python3 tools/console-run.py
TESTS   := python3 tools/run-tests.py --disks /tmp/os4-test-disks --setup "$(TEST_SETUP)" --setup "$(APP_SETUP)" --timeout 150
TEST_HOSTED = --cmd "$(CONSOLE) $(call HOSTED_CMD,{disk}$(comma){appdisk},{port} {peerport})"
TEST_VIRT   = --cmd "$(CONSOLE) $(call VIRT_CMD,{disk},$(NET_TEST),{appdisk})"

.PHONY: all build image data app run run-hosted run-tap test test-hosted test-virt test-app check-course ping-check tcp-check clean FORCE

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

# The app disk, made afresh every time from APP: make run APP=examples/hello
app: $(APP_IMG)

$(APP_IMG): FORCE
	@mkdir -p $(@D)
	@sh tools/app-disk.sh $@ $(APP)

# Boot the bare-metal kernel with the serial console on this terminal.
# Leave with bye, Ctrl-D, or Ctrl-A then x.
run: $(BOOT_IMG) $(DATA_IMG) $(APP_IMG)
	@$(call VIRT_CMD,$(DATA_IMG),$(NET_USER),$(APP_IMG))

run-hosted: $(HOSTED) $(DATA_IMG) $(APP_IMG)
	@$(call HOSTED_CMD,$(DATA_IMG)$(comma)$(APP_IMG))

test: check-course test-hosted test-virt

# The course (docs/course) and code tours (.tours) still match the code.
check-course:
	python3 tools/check-course.py

# Platform-independent tests in tests/, platform-specific ones beside them.
test-hosted: $(HOSTED)
	$(TESTS) $(TEST_HOSTED) tests tests/hosted

test-virt: $(BOOT_IMG)
	$(TESTS) $(TEST_VIRT) tests tests/baremetal

# An app's tests, APP/tests/*.in, on both builds, each with APP as its app
# disk (unless the test has a <name>.app of its own). APP must be absolute.
test-app: $(HOSTED) $(BOOT_IMG)
	@test -d "$(APP)/tests" || { echo "make test-app APP=/path/to/app (with a tests directory)" >&2; exit 2; }
	$(TESTS) --app $(APP) $(TEST_HOSTED) $(APP)/tests
	$(TESTS) --app $(APP) $(TEST_VIRT) $(APP)/tests

# The OS on a TAP device, reachable from this container at 10.0.2.15 (the
# container is 10.0.2.2). Needs: docker run --cap-add NET_ADMIN --device /dev/net/tun
NET_TAP := -netdev tap$(comma)id=net$(comma)ifname=tap0$(comma)script=no$(comma)downscript=no

# Boot it with the console on this terminal; ping it from another shell in the
# same container (docker exec).
run-tap: $(BOOT_IMG) $(DATA_IMG) $(APP_IMG)
	@sh tools/tap-up.sh
	@$(call VIRT_CMD,$(DATA_IMG),$(NET_TAP),$(APP_IMG))

# The milestone 6 acceptance test, literally: boot, ping the OS, shut down.
ping-check: $(BOOT_IMG) $(DATA_IMG) $(APP_IMG)
	sh tools/ping-check.sh "$(call VIRT_CMD,$(DATA_IMG),$(NET_TAP),$(APP_IMG))"

# The OS's TCP against a real stack: the host's, through user networking.
tcp-check: $(BOOT_IMG) $(DATA_IMG) $(APP_IMG)
	OS4_PEER="python3 tools/tcp-check.py" $(CONSOLE) $(call VIRT_CMD,$(DATA_IMG),$(NET_USER),$(APP_IMG)) < tools/tcp-check.in

clean:
	rm -rf $(BUILD) tests/*.actual tests/*/*.actual
