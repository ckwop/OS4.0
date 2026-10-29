# OS 4.0 toolchain image: builds the kernel, runs QEMU and runs the tests; apps
# depend on a tagged version of it.
#   docker build -t os4:0.9b -t os4 .
#   docker run --rm -it os4                          # boot to the Forth prompt on the serial console
#   docker run --rm -v "${PWD}:/src" os4 make test   # against live source
#   docker run --rm -v "${PWD}:/app" -w /app os4:0.9b os4-app test   # an app's tests
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
        iproute2 \
        iputils-ping \
        dosfstools \
        curl \
    && rm -rf /var/lib/apt/lists/*

# Lean 4 for the proofs (docs/verification.md); the version matches
# proofs/lean-toolchain.
ARG LEAN_TOOLCHAIN=leanprover/lean4:v4.19.0
ENV ELAN_HOME=/opt/elan \
    PATH=/opt/elan/bin:$PATH
RUN curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
        | sh -s -- -y --no-modify-path --default-toolchain none \
    && elan toolchain install "$LEAN_TOOLCHAIN" \
    && elan default "$LEAN_TOOLCHAIN"

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

# The base, built, in /opt/os4: apps build and test against it with os4-app
# (DECISIONS.md #99). Working on the base itself mounts its source at /src.
WORKDIR /opt/os4
COPY . .
RUN make build image \
    && chmod +x tools/os4-app \
    && ln -s /opt/os4/tools/os4-app /usr/local/bin/os4-app
WORKDIR /src

CMD ["make", "-C", "/opt/os4", "run"]
