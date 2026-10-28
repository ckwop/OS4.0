# Lean toolchain for the proofs (spike), kept apart from the os4 image.
#   docker build -t os4-lean proofs
#   docker run --rm -v "${PWD}:/src" -w /src/proofs os4-lean lake build
FROM debian:trixie-slim

RUN apt-get update && apt-get install -y --no-install-recommends \
        curl ca-certificates git \
    && rm -rf /var/lib/apt/lists/*

# Matches proofs/lean-toolchain.
ARG LEAN_TOOLCHAIN=leanprover/lean4:v4.19.0
RUN curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
        | sh -s -- -y --no-modify-path --default-toolchain none
ENV PATH=/root/.elan/bin:$PATH
RUN elan toolchain install "$LEAN_TOOLCHAIN" && elan default "$LEAN_TOOLCHAIN"
WORKDIR /src/proofs
