# OS 4.0 build. Runs inside the Docker image (see Readme.md); the host has no toolchain.

CROSS   ?= aarch64-linux-gnu-
AS      := $(CROSS)as
LD      := $(CROSS)ld
ASFLAGS := -g -I arch/aarch64

BUILD  := build
HOSTED := $(BUILD)/forth-hosted

# Hosted kernel: an AArch64 Linux binary run under qemu-aarch64 (milestone 2).
# The kernel embeds forth/core.fs and includes the other arch/aarch64 sources.
KERNEL_DEPS := $(wildcard arch/aarch64/*.s) forth/core.fs
HOSTED_RUN  := qemu-aarch64 $(HOSTED)

.PHONY: all build image run test clean

all: build

build: $(HOSTED)

$(BUILD)/kernel.o: arch/aarch64/kernel.s $(KERNEL_DEPS)
	@mkdir -p $(@D)
	$(AS) $(ASFLAGS) -o $@ $<

$(BUILD)/linux.o: arch/aarch64/linux.s arch/aarch64/macros.s
	@mkdir -p $(@D)
	$(AS) $(ASFLAGS) -o $@ $<

$(HOSTED): $(BUILD)/kernel.o $(BUILD)/linux.o
	$(LD) -static -o $@ $^

# Bare-metal boot and data disk images arrive with milestone 3.
image:
	@echo "image: no bootable image until milestone 3"

run: $(HOSTED)
	@$(HOSTED_RUN)

test: $(HOSTED)
	sh tools/run-tests.sh "$(HOSTED_RUN)"

clean:
	rm -rf $(BUILD) tests/*.actual
