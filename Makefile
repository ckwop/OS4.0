# OS 4.0 build. Runs inside the Docker image (see Readme.md); the host has no toolchain.

CROSS  ?= aarch64-linux-gnu-
AS     := $(CROSS)as
LD     := $(CROSS)ld
ASFLAGS := -g

BUILD  := build
HOSTED := $(BUILD)/forth-hosted

# Hosted kernel: an AArch64 Linux binary run under qemu-aarch64 (milestone 2).
HOSTED_SRC := arch/aarch64/hosted.s
HOSTED_RUN := qemu-aarch64 $(HOSTED)

.PHONY: all build image run test clean

all: build

build: $(HOSTED)

$(BUILD):
	mkdir -p $@

$(BUILD)/hosted.o: $(HOSTED_SRC) | $(BUILD)
	$(AS) $(ASFLAGS) -o $@ $<

$(HOSTED): $(BUILD)/hosted.o
	$(LD) -static -o $@ $^

# Bare-metal boot and data disk images arrive with milestone 3.
image:
	@echo "image: no bootable image until milestone 3"

run: $(HOSTED)
	$(HOSTED_RUN)

test: $(HOSTED)
	sh tools/run-tests.sh "$(HOSTED_RUN)"

clean:
	rm -rf $(BUILD) tests/*.actual
