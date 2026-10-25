# Forth MUD OS — Project Brief

Oct 25, 2026 · @Simon

## Purpose

Build a tiny bare-metal Forth operating system whose finish line is a MUD: a text game that loads a world from disk and serves players over TCP. The primary target is 64-bit ARM (AWS Graviton), run under QEMU in Docker first, then on ECS Fargate, and finally as a native EC2 AMI.

This brief is the starting context for an agent initialising the build. Read it fully, then work through the milestones in order. Each milestone must pass its acceptance test before the next begins. Where this brief is silent, choose the simplest option and record the choice in `DECISIONS.md`.

## Goals and non-goals

Goals:

- Smallest practical assembly kernel; nearly everything else written in Forth, so a port means rewriting only primitives and boot glue.
- Reproducible build and run from one Docker image, developed on Windows (Docker Desktop with WSL2).
- Durable block storage that survives crashes without losing player data.
- Cooperative multitasking serving dozens of simultaneous TCP connections.
- A MUD engine with a Forth-based world-building vocabulary and sandboxed area scripts.
- A path to production: Fargate first, a Graviton EC2 AMI last.

Non-goals (for now):

- Memory protection, user/kernel privilege separation or system calls. Everything runs at EL1 in one flat address space; isolation comes from restricted wordlists.
- Preemptive scheduling or SMP world processing.
- A general filesystem. Forth blocks are the storage model.
- TLS inside the OS. Terminate it upstream if ever needed.

## Key decisions

| Area | Decision | Notes |
| --- | --- | --- |
| Primary CPU | AArch64 (ARMv8-A), QEMU `virt` machine | Matches Graviton; 31 registers suit Forth |
| Porting test | x86-64 | Second target once stable; proves portability |
| Cell size | 64-bit | Block numbers and addresses fit in one cell |
| Threading | Direct-threaded code | `NEXT` = `ldr x8, [x19], #8` then `br x8` |
| Kernel size | Minimal primitive set (eForth-style, \~30 words) | Interpreter and compiler in Forth where practical |
| Bootstrap | Assembly outer interpreter first; metacompiler (on gforth) later | Metacompilation is a later milestone, not day one |
| Boot loader | Limine (UEFI) | Hands over with MMU on and RAM mapped; can load the core Forth image as a module |
| Memory | Single flat address space, identity or Limine direct map | No virtual memory beyond what boot requires |
| Storage model | Classic Forth blocks (1 KB) | `block`, `update`, `save-buffers`, plus a custom `sync` |
| Multitasking | Cooperative round-robin via `pause` | Fixed task pool, no runtime allocation |
| Network stack | Own minimal Ethernet/ARP/IPv4/ICMP/UDP/TCP | uIP is the design reference |
| Dev environment | Docker on Windows, QEMU software emulation | Container arch is independent of guest arch |
| First hosted step | Optional: run the kernel as an AArch64 Linux binary under `qemu-aarch64` | `key`/`emit` via `read`/`write` syscalls, JonesForth-style |

Register plan (AArch64): Forth machine state lives in callee-saved registers so any future C code preserves it.

- `x19` instruction pointer (IP)
- `x20` data stack pointer (grows down)
- `x21` return stack pointer (grows down)
- `x22` top of stack (cached)
- `x23` user area pointer (current task)
- `x8`–`x15` scratch inside primitives; hardware `sp` reserved for exceptions and C calls (it must stay 16-byte aligned)

## Architecture

The system is a stack of small layers, and the HAL words are the only contract between portable Forth and platform code.

&#91;embedded content: system layers · 7 levels, porting boundary highlighted\]

A port to a new CPU replaces the assembly kernel and boot glue; a new platform on the same CPU replaces only drivers. Nothing above the HAL words changes in either case.

## Repository and tooling

One Docker image builds the kernel, assembles the disk images, runs QEMU and runs the tests. `docker run -it` drops the user into the Forth prompt over the serial console.

```
Dockerfile          toolchain: aarch64 binutils, QEMU (system + user), gforth, Limine, python3
Makefile            build, image, run, test targets
DECISIONS.md        running log of choices the brief left open
arch/aarch64/       boot glue, primitives, exception vectors, barriers
arch/x86_64/        later port
hal/                per-platform drivers: uart, virtio, nvme, ena (later)
forth/              core.fs, blocks.fs, tasks.fs, net/*.fs, mud/*.fs
tools/              host-side image tool (read/write blocks, import areas, backups)
world/              area source files, versioned in git
tests/              *.in / *.out pairs, run headless against QEMU
```

Run command (development):

```
qemu-system-aarch64 -machine virt -cpu cortex-a72 -m 256M -nographic \
  -bios <UEFI firmware> -drive file=boot.img,format=raw,if=virtio \
  -drive file=data.img,format=raw,if=virtio,cache=writeback \
  -netdev user,id=n0,hostfwd=tcp::4000-:4000 -device virtio-net-device,netdev=n0
```

Rules:

- Never use `cache=unsafe` on the data drive; it silently discards flushes.
- Tests pipe Forth source into the serial console and diff the output against `.out` files. Every milestone adds tests; the whole suite runs on every change.
- The host-side image tool must understand the block layout so world files and backups can be handled without booting the OS.

## Milestones

Work strictly in this order. Each milestone ends with its acceptance test passing in the Docker image.

1. **Toolchain image.** Dockerfile with cross binutils, QEMU, gforth and Limine; `make` builds an empty kernel.
   - Accept: `docker build` succeeds and `make test` runs (with zero tests).
2. **Hosted Forth (optional but recommended).** The kernel as an AArch64 Linux binary under `qemu-aarch64`: primitives, inner and outer interpreter, colon compiler, `if/then`, `begin/until`, `do/loop`, numbers in any `base`.
   - Accept: `: sq dup * ; 7 sq .` prints `49`; a core word test suite passes.
3. **Bare-metal boot.** Limine boots the kernel on QEMU `virt`; `key`/`emit` over the PL011 UART; exception vectors print registers on a fault.
   - Accept: the same tests pass over the serial console; a deliberate bad access prints a register dump.
4. **Blocks.** virtio-blk driver (polled), `block`, `buffer`, `update`, `save-buffers`, `sync` (with device flush), `load`, `thru`, `list`, `index`.
   - Accept: write a screen, reboot QEMU, `load` it, and the defined word works.
5. **Multitasking and timer.** User areas, `pause`, task pool, ARM generic timer, `ms`, idle `wfi` when all tasks wait, watchdog hook.
   - Accept: two tasks interleave output; a task that never pauses is reported by the watchdog.
6. **Network to ping.** virtio-net driver, Ethernet, ARP, IPv4, ICMP echo, behind `net-send`/`net-poll`.
   - Accept: the OS answers ping from inside the container.
7. **UDP.** Static IP (10.0.2.15 under QEMU user networking).
   - Accept: a UDP echo test passes.
8. **TCP, many connections.** Connection table, state machine, retransmission timer, windowing; `accept-connection`, `get-line`, `send`.
   - Accept: 32 simultaneous scripted clients exchange lines without loss.
9. **Network REPL.** Telnet into a sandboxed Forth prompt via the forwarded port.
   - Accept: `telnet localhost 4000` from the host gives a working prompt.
10. **MUD engine.** Player records, login, name index, rooms, movement, chat, world loader, builder vocabulary, scripts with hooks.
    - Accept: two players log in, walk between rooms, talk, and state survives a restart.
11. **Fargate deployment.** ARM64 or x86 container on ECS Fargate, data image on EFS, NLB on the MUD port.
    - Accept: players connect over the internet; a task restart loses nothing.
12. **EC2 AMI.** NVMe and ENA drivers, ACPI table parsing, raw image import as an AMI.
    - Accept: the AMI boots on a t4g instance and serves the MUD from a separate EBS data volume.
13. **x86-64 port.** New primitives and boot glue only.
    - Accept: the full test suite passes on `qemu-system-x86_64`.

The MUD engine can be prototyped earlier in gforth on Linux against the same small set of network words, then moved onto the OS at milestone 10.

## Storage

Code and data live on separate disks. The boot disk (Limine, kernel, core image) is never written by the OS. The data disk holds all blocks and is the only disk the block layer will write.

Data disk layout (1 KB blocks; generous fixed regions, nothing ever moves):

| Blocks | Region | Contents |
| --- | --- | --- |
| 0 | Header | Magic number, format version, volume ID; the OS refuses to write a disk without a valid header |
| 1–999 | System | Load screen, engine and support code as Forth screens |
| 1000–9999 | World | Area source screens |
| 10000–19999 | Scripts | Mob and item script source |
| 20000–49999 | Text | Long prose records (room descriptions, help) |
| 50000–50999 | Player index | Fixed 32-byte entries: lowercased name, slot, flags |
| 51000–299999 | Players | Fixed slots, two alternating copies each |
| 300000+ | Spare | Logs, snapshots, future use |

Conventions:

- Code is stored as standard screens: 16 lines of 64 characters, no newlines; line 0 is an index comment.
- Player records are fixed binary fields plus bounded text fields, with a sequence number and checksum. Never store player data as Forth source to be interpreted.
- Passwords are stored as salted, deliberately slow hashes.
- The player index is read into an in-memory hash table at boot.

Durability rules:

- `sync` = `save-buffers`, then a device flush, then wait for completion. A write without a flush is not durable.
- Saves alternate between a player's two copies; loading picks the newest copy with a valid checksum, so torn writes are rejected.
- New player: write the record, `sync`, then write the index entry, `sync`. Never the other order.
- Do not rely on a clean shutdown. Flush on every save and periodically from the saver task.

## Multitasking and networking

Scheduling is cooperative round-robin. Each task has a data stack, return stack and user area (including its search order); `pause` saves the stack pointers, switches to the next awake task and restores its pointers. This is the only multitasking code in assembly.

Standing tasks:

- **Network:** polls the NIC, runs ARP/IP/TCP, fills per-connection input buffers.
- **Listener:** accepts connections and assigns a player task from a fixed pool (start with 64).
- **Player:** one per connection; reads lines with `get-line`, which pauses until a line is ready.
- **Heartbeat:** mob `on-tick` hooks, combat rounds, the delayed-action timer queue.
- **Saver:** periodic `sync` of dirty blocks.

Rules:

- Every blocking word loops on `pause`. Engine code must never run long without pausing.
- When every task is waiting, execute `wfi` until the timer or a device wakes the CPU. Busy-spinning wastes burstable-instance CPU credits.
- A timer-interrupt watchdog reports any task that runs too long without pausing. The second vCPU may later take over as a read-only watchdog.
- Route every world change through a small set of words (`move-to`, `damage`, `give` and so on) so locking or message passing can be added later.

Networking:

- Drivers sit behind `net-send` and `net-poll`; blocks behind `blk-read`, `blk-write` and `blk-flush`. virtio for development and Fargate; NVMe and ENA for EC2. Nothing above these words knows which is in use.
- ARM is weakly ordered: every device ring update needs the correct barrier (`dmb`/`dsb`), wrapped in named Forth words.
- Telnet: strip or minimally refuse IAC negotiation, buffer input into lines, handle disconnects cleanly.
- No TLS in the OS. Use upstream TLS termination for public traffic, or Noise for node-to-node links later.

## MUD engine and scripting

The world is Forth source written with a building vocabulary; player commands are words in their own wordlist, and the command parser is the outer interpreter pointed at that wordlist.

```forth
room tavern  " The Rusty Flagon"
  " Smoke hangs under low beams. A fire crackles to the east."
  north exit square
  east exit kitchen
item mug  " a chipped tin mug"  in tavern

mob innkeeper  " the innkeeper"
  on-enter: chance 50 if " Welcome, traveller!" say then ;
  on-tick:  chance 5 if " polishes a glass." emote then ;
```

Wordlists (each a separate, exclusive search order):

| Wordlist | Used by | Allowed |
| --- | --- | --- |
| Player | Connected players | Game commands only; no compiling, no memory access |
| Builder | Trusted builders in-game | Player words plus `dig`, `describe`, `link` and similar |
| Script | Mob and item hooks | Accessor words (`say`, `emote`, `move`, `give`, `chance`, `actor`), bounded loops |
| Admin | Operator via network REPL | Full Forth |

Scripting rules:

- Hooks: `on-enter`, `on-say`, `on-tick`, `on-get`, `on-drop`, `on-combat`, `on-death`.
- Store script source in blocks and compile at load; never persist execution tokens.
- In the script wordlist, `again`, `repeat`, `until` and `loop` decrement an instruction budget and abort the script at zero, so every loop is bounded.
- Scripts never wait inside a hook; delays use `n seconds after: ... ;` via the timer queue.
- Stored records are the master copy of the world; area files are an import format, and `dump-area` exports an area back to source for git.

## Deployment path

Three stages, each reusing the previous one's disk layout unchanged.

1. **Docker locally.** QEMU in the container provides virtio devices. Port 4000 is forwarded to the host.
2. **ECS Fargate.** The same container, QEMU in software emulation (no KVM). The data image lives on a mounted EFS volume so restarts keep player data. A Network Load Balancer (or a public task IP) carries raw TCP; an Application Load Balancer will not.
3. **EC2 AMI on Graviton.** UEFI boot from the root EBS volume via Limine. Requires an NVMe driver (EBS) and an ENA driver (network), plus ACPI table parsing (SPCR for the UART, MCFG for PCIe). Build a raw disk image, upload to S3, `aws ec2 import-snapshot`, then `aws ec2 register-image` with `--ena-support` and UEFI boot mode.

EC2 specifics:

- Keep the OS on the root volume and the world on a separate EBS data volume; upgrades swap the AMI and reattach the data volume.
- Identify the data volume by its block 0 header; also check that the NVMe serial number matches the expected EBS volume ID.
- Check the NVMe sector size; if it is 4 KB, block writes become read-modify-write.
- Use EBS snapshots of the data volume for backups.
- The existing `data.img` from Fargate can be imported as the first EBS data volume.
- Without ACPI power-button handling, stops are forced; the durability rules make this safe. Handling the event comes later.
- ENA cannot be emulated in QEMU; debug it on real instances using the EC2 serial console.

## Conventions for the agent

- Work one milestone at a time; do not start the next until the current acceptance test passes and is committed.
- Prefer Forth over assembly. Move a word to assembly only when it is a primitive, touches hardware, or is a measured hot spot; keep the Forth version as a reference.
- Every hardware access goes through the HAL words. No driver details above `hal/`.
- Comment every assembly primitive with its stack effect, `( n1 n2 -- n3 )` style; give every Forth word a stack-effect comment.
- Barriers and other ordering-sensitive operations are named words, never inline magic.
- Add tests with every feature: a `.in` file of Forth input and a `.out` file of expected output.
- Record any choice this brief leaves open in `DECISIONS.md` with a one-line reason.
- The workspace may not run a Docker daemon. Install the same tools directly, build and test there, and keep the Dockerfile in step; the user's first `docker build` is the real check.
- Never write to the boot disk at runtime, never use `cache=unsafe`, and never let a player-facing wordlist reach the full dictionary.
- Report progress at each milestone with what passed and anything that changed the plan.

## Open questions and future options

- [ ] Container architecture on Fargate: one x86 image everywhere, or an ARM64 build for cheaper Graviton tasks?
- [ ] Player cap for the first release (sets the task pool and TCP connection table size; 64 assumed).
- [ ] MUD port number (4000 assumed) and whether to offer a plain telnet port only.
- [ ] Password hash algorithm, implemented in Forth.
- [ ] When to move from the assembly outer interpreter to a metacompiled image.

Future options, deliberately out of scope now: ACPI power-button handling; a second-core watchdog or network core; virtio-9p shared folders; Noise for node-to-node links; a Raspberry Pi 4 target (needs SD card and GENET Ethernet drivers).
