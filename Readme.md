## OS 4.0

A tiny bare-metal Forth operating system for 64-bit ARM, built to run a MUD: a text game that loads its world from Forth blocks on disk and serves players over TCP. It runs under QEMU in Docker first, then on AWS ECS Fargate, and finally as a native Graviton EC2 AMI.

- Full specification: [docs/brief.md](docs/brief.md)
- Choices made along the way: [DECISIONS.md](DECISIONS.md)
- Known shortcuts and gaps: [docs/tech-debt.md](docs/tech-debt.md)
- How it is put together, as twelve short narrated lectures with code tours for VS Code's CodeTour extension: [docs/course](docs/course/index.html) (open `index.html` in a browser; Edge's "Natural" voices sound best)
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

Make targets (run inside the container): `build` (the default), `image`, `data`, `app`, `run`, `run-hosted`, `test`, `test-hosted`, `test-virt`, `test-app`, `proofs` and `clean`.

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

### Network REPL

The OS serves Forth over telnet. Port 4000 is a sandbox: arithmetic, the stack and printing, but no compiling and no access to memory or the rest of the dictionary. Port 4001 is the full Forth, as on the console, after the admin password. Each session runs in its own task with its own stack, number base and buffers; `bye` ends it, and so do ten minutes without input. Each port takes a limited number of sessions at once (16 and 4).

Port 4001 turns everyone away until you set the admin password on the console. It is kept, hashed, on the data disk, so this is needed once per disk:

```forth
set-admin-password      \ asks twice; nothing you type is shown
```

To try it from Windows, boot with both ports published to your machine only:

```powershell
docker run --rm -it -p 127.0.0.1:4000:4000 -p 127.0.0.1:4001:4001 -v "${PWD}:/src" os4 make run
```

Then, from another terminal, `telnet localhost 4000` (or 4001). Windows ships its telnet client switched off; turn it on once from an administrator PowerShell with `dism /online /Enable-Feature /FeatureName:TelnetClient`, or use PuTTY with the connection type set to Telnet.

Even with its password, keep port 4001 to your own machine (the `127.0.0.1:` above). `make tcp-check` runs eight sandbox sessions and a full-Forth one from the container's own TCP stack.

### TCP

`listen` opens a port; `accept-connection` waits for the next client; `get-line`, `send`, `send-line` and `close-connection` talk to it. Each client gets its own task. A line echo server on port 5000:

```forth
: serve ( conn -- ) begin pad 256 2 pick get-line dup 0< 0= while pad swap 2 pick send-line repeat drop close-connection ;
: line-server ( -- ) 5000 listen begin 5000 accept-connection ['] serve spawn drop again ;
task server  ' line-server server start
.tcp                                   \ connections live and pooled
```

### Applications

This repository is the base. An application lives in a repository of its own and depends on a tagged image of the base, `os4:0.10`, built from here:

```powershell
docker build -t os4:0.10 -t os4 .
```

An app is a directory of Forth files with `app.fs` as its entry point, which can `include` the others (paths with `/`, any case). At boot the OS finds the app disk, includes `app.fs` and runs the app's `main`, which starts the app's tasks and returns; the console follows. If loading fails, the OS reports where (`app.fs:12: ...`) and the console still comes up. Without an app, the OS starts the network REPL as above. With one, the app chooses: it can serve its own port through a door with a session cap (`port-door`, `serve-door`, as `tests/doors.app` does) and call `start-admin` to keep the full Forth on port 4001 without the sandbox on 4000.

The app disk is FAT, made with ordinary tools, and the OS only reads it. Everything the OS writes goes in blocks on the data disk. [examples/hello](examples/hello) greets whoever connects to port 5000. From an app's directory:

```powershell
docker run --rm -v "${PWD}:/app" -w /app os4:0.10 os4-app test         # its tests/*.in on both builds
docker run --rm -it -p 127.0.0.1:5000:5000 -v "${PWD}:/app" -w /app os4:0.10 os4-app run . 5000
```

`os4-app run` keeps the app's data disk in `build/data.img` in the app's directory. On the console, `dir` lists the app disk and `include` loads a file from it.

### Proofs

The base is certified as it goes, with Lean 4 proofs about the words as the system actually compiles them ([docs/verification.md](docs/verification.md)). `make proofs` boots the hosted build, dumps its dictionary, turns every word it can into a Lean definition, and checks every theorem. Run it at each milestone and before merging a change to the base: a change that breaks a property fails it like a failing test. Only what changed is re-proven: with nothing changed it takes seconds, after a change to a late boot file about a minute, and after a change to `core.fs` about eight, so it is not yet part of `make test` (TD-30). Keep Lake's build on the Docker volume, as below, rather than in your working copy.

```powershell
docker run --rm -v "${PWD}:/src" -v os4-lake:/src/proofs/.lake os4 make proofs   # extract, generate and check
```

Every word with a fixed stack effect has it proven, layered through its callees' proofs, and every plain stack comment is checked against what the code does. A comment that disagrees, or a word whose effect depends on its data, is listed in `build/proof-findings.txt`. Hand-written theorems (`proofs/OS4/*.lean`) prove deeper properties: arithmetic words for all inputs, the Forth reference definitions against the assembly primitives' models, and memory. What is trusted rather than proven is listed in `proofs/OS4/Machine.lean`.

The system tasks' loops (the network task and the REPL listeners) are proven to pause within a bounded number of Forth instructions, so the watchdog never stops them (`proofs/OS4/Yield.lean`). Inner loops that never pause are listed in `proofs/yields.txt`, each with what bounds it; a new one that is not listed fails `make proofs`, and the bounds are reported in `build/yields.txt`.

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
| 8 | TCP, many connections | Done |
| 9 | Network REPL | Done |
| 9a | Hardened base | Done |
| 9b | Applications: an app is files on a read-only FAT app disk, `app.fs` its entry point; apps live in their own repositories and build against a versioned `os4` image | Done |
| 9c | The course: narrated lectures on how the base is put together (`docs/course`), code tours (`.tours`), checked against the code by `make test` | Done |
| 10 | MUD engine (in its own repository, `os4-mud`, as the first application). Phase 1: rooms, items, mobs and doors from area files on the app disk; players, passwords, inventories, credits, wearing on the data disk; say mode; colour. Phase 2 (combat, experience, mob scripts, shops, building) is parked | Phase 1 done |
| 11 | Fargate deployment | Not started |
| 12 | EC2 AMI | Not started |
| 13 | x86-64 port | Not started |

The verification track ([docs/verification.md](docs/verification.md)) runs beside these and strengthens the base. Its roadmap runs in phases. Foundations come first (proof speed, footprints). Then what players reach comes before the MUD launches (V2, V6's stopped tasks, V10, V3), and the network before milestone 11 (V4). The rest removes trust.

| Phase | # | Verification milestone | Status |
| --- | --- | --- | --- |
| | V0 | Spike: Lean definitions generated from the compiled dictionary | Done |
| 1 | V1 | Proofs in the suite: every fixed stack effect proven compositionally (done); proofs fast enough for `make test`; interpreter primitives modelled; reference definitions | In progress |
| 1 | V9 | Footprints: what each word may read and write, proven compositionally | Not started |
| 2 | V2 | Sandbox isolation: a sandboxed task can run only the exposed words | Not started |
| 2 | V6 | Tasks: the system tasks pause within bounded steps (done); a stopped task leaves nothing broken; mutual exclusion, lock discipline | In progress |
| 2 | V10 | Proofs for an app: the MUD's tasks yield and its commands stay isolated | Not started |
| 2 | V3 | Crash-safe records: after a crash, `record@` gives the old record or the new one | Not started |
| 3 | V4 | The network survives any input: the receive ring stays supplied, parsers read only the frame and write only their buffers, pools stay whole | Not started |
| 4 | V7 | TCP state machine invariants, off-path attacks | Not started |
| 4 | V5 | Primitives proven against the assembly | Not started |
| 4 | V8 | Cryptography against its standards | Not started |
