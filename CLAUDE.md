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

- Prefer Forth over assembly. Assembly is only for primitives, hardware access or measured hot spots; keep a Forth reference version alongside.
- Every assembly primitive and every Forth word gets a stack-effect comment: `( n1 n2 -- n3 )`.
- Forth source on disk uses standard screens: 16 lines of 64 characters, and line 0 is an index comment.
- AArch64 registers: `x19` IP, `x20` data stack pointer, `x21` return stack pointer, `x22` cached TOS, `x23` user area. `x8`–`x15` are scratch, and `x24`–`x28` are scratch for primitives across subroutine calls. Hardware `sp` is reserved for exceptions and C calls and stays 16-byte aligned.
- Direct-threaded code: `NEXT` is `ldr x8, [x19], #8` then `br x8`. Non-primitive words start with an 8-byte code field `<insn>; bl <handler>` (DECISIONS.md #12).
- Kernel layout: `arch/aarch64/kernel.s` includes `outer.s`, `text.s`, `prims.s` and `compiler.s` as one assembly unit (the dictionary link chain needs this). Platform glue is a separate object: `linux.s` for the hosted build, `virt.s` (plus `vectors.s` and `virt.ld`) for bare metal on QEMU virt under Limine. `forth/core.fs` is embedded and interpreted at start-up.
- Bare metal: Limine base revision 3, kernel in the higher half, devices reached through our own TTBR0 identity map of 0–1 GiB as Device memory (DECISIONS.md #23–25). Faults print a register dump and resume at ABORT.
- Assembly subroutines follow AAPCS64 (args in `x0`–`x7`, may clobber `x0`–`x15` and `x30`) and are named `*_sub`; HAL routines are `hal_key`, `hal_emit` and `hal_bye`.
- All text files use LF line endings (enforced by `.gitattributes`).

## Tests

- Tests are `tests/*.in` (Forth fed to the serial console) paired with `tests/*.out` (expected output), run headless under QEMU.
- `.out` files are transcripts: the banner, then each input line as the Forth echoes it, its output, and ` ok`. Generate a new one by running the `.in` file, then check every value by hand (and against gforth for standard words) before committing it.
- `make test` runs `tests/` on the hosted build, then `tests/` and `tests/baremetal/` over the serial console (`make test-hosted`, `make test-virt` for one). The serial run boots QEMU per test, about 10 s each.
- A `<name>.filter` file next to a test is a sed script that masks build-dependent output, such as addresses in a register dump.
- Drive a REPL interactively through a pseudo-terminal with `script -qec 'make -s run' /dev/null` (bare metal) or `script -qec 'make -s run-hosted' /dev/null` inside the container.
- Every feature adds tests, and the whole suite runs on every change.

## Workflow

- Record any choice the brief leaves open in `DECISIONS.md` with a one-line reason.
- At the end of each milestone, update the Readme milestone table and report what passed and anything that changed the plan.
