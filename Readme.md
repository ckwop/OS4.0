## OS 4.0

A tiny bare-metal Forth operating system for 64-bit ARM, built to run a MUD: a text game that loads its world from Forth blocks on disk and serves players over TCP. It runs under QEMU in Docker first, then on AWS ECS Fargate, and finally as a native Graviton EC2 AMI.

- Full specification: [docs/brief.md](docs/brief.md)
- Choices made along the way: [DECISIONS.md](DECISIONS.md)
- Notes for AI coding agents: [CLAUDE.md](CLAUDE.md)

### Prerequisites

Windows 11 with:

- WSL2
- Rancher Desktop, with the container engine set to **dockerd (moby)**

The image provides every other tool: cross binutils, QEMU, gforth and Limine.

### Milestones

Each milestone is done when its acceptance test passes in the Docker image.

| # | Milestone | Status |
| --- | --- | --- |
| 1 | Toolchain image | Not started |
| 2 | Hosted Forth (under `qemu-aarch64`) | Not started |
| 3 | Bare-metal boot | Not started |
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
