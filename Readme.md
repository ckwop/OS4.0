## OS 4.0

A tiny bare-metal Forth operating system for 64-bit ARM, built to run a MUD: a text game that loads its world from Forth blocks on disk and serves players over TCP. It runs under QEMU in Docker first, then on AWS ECS Fargate, and finally as a native Graviton EC2 AMI.

- Full specification: [docs/brief.md](docs/brief.md)
- Choices made along the way: [DECISIONS.md](DECISIONS.md)
- Notes for AI coding agents: [CLAUDE.md](CLAUDE.md)

### Prerequisites

Windows 11 with:

- WSL2
- Rancher Desktop, with the container engine set to **dockerd (moby)** and Kubernetes off. Rancher does not put `docker` on your PATH; add `C:\Program Files\Rancher Desktop\resources\resources\win32\bin` to your user PATH.

The image provides every other tool: cross binutils, QEMU, gforth and Limine.

### Build and run

From the repo root in PowerShell:

```powershell
docker build -t os4 .                              # build the toolchain image, the kernel and the boot disk
docker run --rm -it os4                            # boot the OS to its Forth prompt on the serial console
docker run --rm -v "${PWD}:/src" os4 make test     # run the test suites against your working copy
docker run --rm -it -v "${PWD}:/src" os4 make run  # boot your working copy without rebuilding the image
docker run --rm -it -v "${PWD}:/src" os4 make run-hosted  # the same Forth as a Linux program; starts instantly
```

Booting takes about ten seconds: UEFI firmware, then Limine, then the OS. Leave with `bye`, Ctrl-D on an empty line, or Ctrl-A then x.

Make targets (run inside the container): `build` (the default), `image`, `run`, `run-hosted`, `test`, `test-hosted`, `test-virt` and `clean`.

### Milestones

Each milestone is done when its acceptance test passes in the Docker image.

| # | Milestone | Status |
| --- | --- | --- |
| 1 | Toolchain image | Done |
| 2 | Hosted Forth (under `qemu-aarch64`) | Done |
| 3 | Bare-metal boot | Done |
| 4 | Blocks | Not started |
| 5 | Multitasking and timer | Not started |
| 6 | Network to ping | Not started |
| 7 | UDP | Not started |
| 8 | TCP, many connections | Not started |
| 9 | Network REPL | Not started |
| 10 | MUD engine | Not started |
| 11 | Fargate deployment | Not started |
| 12 | EC2 AMI | Not started |
| 13 | x86-64 port | Not started |
