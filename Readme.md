## OS 4.0

A tiny bare-metal Forth operating system for 64-bit ARM, built to run a MUD: a text game that loads its world from Forth blocks on disk and serves players over TCP. It runs under QEMU in Docker first, then on AWS ECS Fargate, and finally as a native Graviton EC2 AMI.

- Full specification: [docs/brief.md](docs/brief.md)
- Choices made along the way: [DECISIONS.md](DECISIONS.md)
- Known shortcuts and gaps: [docs/tech-debt.md](docs/tech-debt.md)
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

Make targets (run inside the container): `build` (the default), `image`, `data`, `run`, `run-hosted`, `test`, `test-hosted`, `test-virt` and `clean`.

### Blocks

The OS keeps its data on a second disk of 1 KiB blocks, `build/data.img`, created on first run. With the `-v "${PWD}:/src"` mount it is kept between runs; without it, it disappears with the container. Changes are durable only after `sync`.

```forth
.disk                                  \ volume ID and size
5 wipe                                 \ blank block 5 and edit it
0 >line \ my first screen
1 >line : hello ." Hello from block 5" ;
5 list                                 \ show it
sync                                   \ write it to disk
5 load hello                           \ compile it, run the word it defined
```

`tools/blocks.py` reads and writes data disks from the host: `format`, `info`, `list` and `put` (import a text file as screens).

### Tasks

Tasks are cooperative: each runs until it waits or calls `pause`. A watchdog stops any task, the console included, that runs for 5 seconds without pausing.

```forth
task clock                             \ a task, asleep until started
: tick-tock ( -- ) 5 0 do ." tick " 1000 ms loop ;
' tick-tock clock start                \ runs while you keep typing
.tasks                                 \ who is running, ready, sleeping or stopped
```

### Network

The OS is 10.0.2.15 on QEMU's user network, with the gateway at 10.0.2.2. It answers ARP and ping, and can ping out:

```forth
.net                                   \ address, MAC and gateway
ip 10.0.2.2 ping                       \ three echo requests
echo-service                           \ answer UDP echo on port 7
: heard ( data len -- ) ." heard: " type cr ;
' heard 5000 udp-bind                  \ datagrams to port 5000 go to HEARD
s" hello" 5000 ip 10.0.2.2 7 udp-send drop
```

To ping the OS from inside the container with the real `ping` (this needs extra privileges for a TAP device):

```powershell
docker run --rm --cap-add NET_ADMIN --device /dev/net/tun -v "${PWD}:/src" os4 make ping-check
```

### Milestones

Each milestone is done when its acceptance test passes in the Docker image.

| # | Milestone | Status |
| --- | --- | --- |
| 1 | Toolchain image | Done |
| 2 | Hosted Forth (under `qemu-aarch64`) | Done |
| 3 | Bare-metal boot | Done |
| 4 | Blocks | Done |
| 5 | Multitasking and timer | Done |
| 6 | Network to ping | Done |
| 7 | UDP | Done |
| 8 | TCP, many connections | Not started |
| 9 | Network REPL | Not started |
| 10 | MUD engine | Not started |
| 11 | Fargate deployment | Not started |
| 12 | EC2 AMI | Not started |
| 13 | x86-64 port | Not started |
