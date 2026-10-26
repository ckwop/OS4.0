# OS 4.0: Forth MUD OS

A tiny bare-metal Forth operating system for AArch64 (QEMU `virt`, then AWS Graviton) whose end goal is a MUD served over TCP.

**The spec is [docs/brief.md](docs/brief.md). Read it before starting any milestone.** Where it is silent, pick the simplest option and log it in [DECISIONS.md](DECISIONS.md).

## Current status

See the milestone table in [Readme.md](Readme.md). Work strictly in milestone order; a milestone is done only when its acceptance test passes in the Docker image and is committed.

## Environment

- Host is Windows 11. There is no native toolchain on the host (no make, QEMU, gforth or binutils), and none should be added.
- Everything builds and runs inside the Docker image, via Rancher Desktop (dockerd/moby runtime) on WSL2.
- Build the image with `docker build -t os4 .`, then run `make` targets in the container against live source: `docker run --rm -v "${PWD}:/src" os4 make test`. See the Readme for the full command list.
- The repo currently lives under OneDrive. If git or bind mounts misbehave (lock files, slow I/O), suspect OneDrive sync first.

## Hard rules (from the brief)

- Never write to the boot disk at runtime. Only the data disk is written.
- Never use `cache=unsafe` on the data drive.
- Never let a player-facing wordlist reach the full dictionary.
- Never store player data as Forth source, and never persist execution tokens.
- `sync` means `save-buffers`, then a device flush, then wait for completion. New player: record, `sync`, then index entry, `sync`.
- Every hardware access goes through HAL words (`net-send`, `net-poll`, `blk-read`, `blk-write`, `blk-flush`, `key`, `emit`). No driver details above `hal/`.
- Barriers (`dmb`/`dsb`) and other ordering-sensitive operations are named Forth words, never inline.

## Code conventions

- Most of the software is built in Forth: drivers, protocol stacks, the block layer, the MUD engine and tools. Assembly is only for primitives, the thinnest hardware access (register reads and writes, barriers), the bootstrap that loads the boot files, and measured hot spots; keep the Forth definition as the reference.
- Boot files: `forth/core.fs` (the language), `forth/output.fs` (output, strings, throw messages), the platform's drivers from `hal/`, `forth/blocks.fs` (block storage), `forth/errors.fs` (`.error`), `forth/tasks.fs` (multitasking, `ms`, the pausing `key`), `forth/interpreter.fs` (the outer interpreter; must stay last, as it ends by starting `quit`). `kernel.s` is assembled per platform (`HOSTED` defined for Linux) and its `bootfile` list picks the drivers.
- Drivers are Forth in `hal/`, behind HAL words. Blocks: `blk-count blk-read blk-write blk-flush` (`virtio-blk.fs` bare metal, `linux-blk.fs` hosted). Network: `net-up? net-mac net-send net-poll` (`virtio-net.fs`; hosted `linux-net.fs` carries frames as UDP). Register text for new throw codes with `n message: text`.
- The network stack is `forth/net/*.fs` (#65–67): `eth`, `arp`, `ip` (register protocols with `ip-handler!`), `icmp`, `udp` (`udp-bind`, `udp-send`, `udp-reply`; #73), and `net.fs` with the network task. Build outgoing packets in `tx-frame` and send without pausing in between (TD-15). They are embedded in the kernel and loaded in the order of the `bootfile` lines in `kernel.s`; add a new file there. Errors while loading report `<file>:<line>:`.
- The REPL is Forth (`interpreter.fs`); the assembly interpreter in `outer.s` only loads the boot files (DECISIONS.md #33).
- Tasks are cooperative (#48–56): any word that waits must `pause` in its loop or sleep with `ms`/`stop`, and long computations must `pause` now and then, or the watchdog (default 5 s) stops them with -262. Per-task state belongs in the user area: define it with `user`; reach another task's with `>user`.
- Anything shared that a task might use across a pause needs a `semaphore`; prefer `['] (word) some-lock locked`, which releases on errors too (#76). Block words hold `blocks-lock` and network senders hold `tx-lock` (#77–78): a new sending word must too.
- Errors are `throw`n with standard codes and caught by `catch`; the REPL catches per line (#35–37). New error conditions should `throw` a code, not print and abort. Kernel errors throw through `try_throw` in `outer.s`. Mark words that only make sense inside a definition with `compile-only`.
- Every assembly primitive and every Forth word gets a stack-effect comment: `( n1 n2 -- n3 )`.
- Forth source on disk uses standard screens: 16 lines of 64 characters, and line 0 is an index comment.
- AArch64 registers: `x19` IP, `x20` data stack pointer, `x21` return stack pointer, `x22` cached TOS, `x23` user area. `x8`–`x15` are scratch, and `x24`–`x28` are scratch for primitives across subroutine calls. Hardware `sp` is reserved for exceptions and C calls and stays 16-byte aligned.
- Direct-threaded code: `NEXT` is `ldr x8, [x19], #8` then `br x8`. Non-primitive words start with an 8-byte code field `<insn>; bl <handler>` (DECISIONS.md #12).
- Kernel layout: `arch/aarch64/kernel.s` includes `outer.s`, `text.s`, `prims.s` and `compiler.s` as one assembly unit (the dictionary link chain needs this). Platform glue is a separate object: `linux.s` for the hosted build, `virt.s` (plus `vectors.s` and `virt.ld`) for bare metal on QEMU virt under Limine.
- Bare metal: Limine base revision 3, kernel in the higher half, devices reached through our own TTBR0 identity map of 0–1 GiB as Device memory (DECISIONS.md #23–25). Faults print a register dump and throw -256 (hosted: a signal report, then the same throw).
- The dictionary is RAM handed to `forth_cold` by the platform (largest usable region from Limine's memory map; hosted, an `mmap`), up to 128 MiB (#72). Code fields `bl` to handler trampolines at its start: use the `docol`/`dovar`/`docon` words, never the kernel's handler labels, when compiling code fields.
- Each task's stacks have limits, checked in colon calls, branches, loops and `pause` (#57). Kernel errors go through `try_throw` in `outer.s`, which unwinds to the `catch` frame first. Internal kernel words that only work inside definitions get `F_CONLY` in their `defcode` line.
- Assembly subroutines follow AAPCS64 (args in `x0`–`x7`, may clobber `x0`–`x15` and `x30`) and are named `*_sub`; HAL routines are `hal_key`, `hal_emit` and `hal_bye`.
- All text files use LF line endings (enforced by `.gitattributes`).

## Tests

- Tests are `tests/*.in` (Forth fed to the serial console) paired with `tests/*.out` (expected output), run headless under QEMU.
- `.out` files are transcripts: the banner, then each input line as the Forth echoes it, its output, and ` ok`. Generate a new one by running the `.in` file, then check every value by hand (and against gforth for standard words) before committing it.
- `make test` runs `tests/` and `tests/hosted/` on the hosted build (seconds), then `tests/` and `tests/baremetal/` over the serial console (under a minute; one VM per test, in parallel). `make test-hosted` or `make test-virt` runs one. `tools/run-tests.py` is the runner.
- A `<name>.filter` file next to a test is a sed script that masks build-dependent output, such as addresses in a register dump.
- Each test gets a fresh data disk of its own (in `build/test-disks/`, 1024 blocks, volume ID 42). A line `\ --- reboot ---` in a `.in` file shuts down and boots again on the same disk (`tools/console-run.py`).
- Network tests: each test's NIC is wired to its own UDP ports; a `<name>.peer` file names a peer to run on that LAN (`tools/netpeer.py`, 10.0.2.2), whose findings follow `--- peer ---` in the transcript. Add peer scripts there for UDP and TCP. `make ping-check` (privileged container) pings the OS with the real `ping`.
- `make run-tap` (privileged container) boots the OS on `tap0`, reachable from the container at 10.0.2.15: ping it from another shell with `docker exec`.
- `tools/blocks.py` formats data disks and lists or imports screens from the host: `python3 tools/blocks.py list build/data.img 5`.
- Drive a REPL interactively through a pseudo-terminal with `script -qec 'make -s run' /dev/null` (bare metal) or `script -qec 'make -s run-hosted' /dev/null` inside the container.
- Every feature adds tests, and the whole suite runs on every change.

## Workflow

- Record any choice the brief leaves open in `DECISIONS.md` with a one-line reason.
- Record shortcuts, gaps and risks in `docs/tech-debt.md`; close entries there when they are fixed. Check its open entries when starting a milestone: some are due before particular milestones.
- At the end of each milestone, update the Readme milestone table and report what passed and anything that changed the plan.
