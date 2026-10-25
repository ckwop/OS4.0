# OS 4.0 toolchain image: builds the kernel, runs QEMU and runs the tests.
#   docker build -t os4 .
#   docker run --rm -it os4                          # boot to the Forth prompt on the serial console
#   docker run --rm -v "${PWD}:/src" os4 make test   # against live source
FROM debian:trixie-slim

# Limine is not packaged by Debian; pin a commit on its prebuilt-binary branch.
ARG LIMINE_REPO=https://codeberg.org/Limine/Limine.git
ARG LIMINE_COMMIT=ee5d29cd0a8034612dcd1df3f00052480db785c5

# Trixie dropped gforth; bookworm's 0.7.3 installs cleanly alongside. Every other
# package has a newer trixie version, so apt still takes those from trixie.
RUN echo 'deb http://deb.debian.org/debian bookworm main' > /etc/apt/sources.list.d/bookworm.list

RUN apt-get update && apt-get install -y --no-install-recommends \
        binutils-aarch64-linux-gnu \
        qemu-system-arm \
        qemu-user \
        qemu-efi-aarch64 \
        gforth \
        python3 \
        make \
        gcc \
        libc6-dev \
        git \
        ca-certificates \
        mtools \
        dosfstools \
    && rm -rf /var/lib/apt/lists/*

# Builds the host-side `limine` tool next to the prebuilt EFI binaries.
RUN git init -q /opt/limine \
    && cd /opt/limine \
    && git fetch -q --depth 1 "$LIMINE_REPO" "$LIMINE_COMMIT" \
    && git checkout -q FETCH_HEAD \
    && make \
    && rm -rf .git

ENV LIMINE_DIR=/opt/limine \
    UEFI_FIRMWARE=/usr/share/qemu-efi-aarch64/QEMU_EFI.fd \
    PATH=/opt/limine:$PATH

WORKDIR /src
COPY . .
RUN make build image

CMD ["make", "run"]
