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
- AArch64 registers: `x19` IP, `x20` data stack pointer, `x21` return stack pointer, `x22` cached TOS, `x23` user area. `x8`–`x15` are scratch. Hardware `sp` is reserved for exceptions and C calls and stays 16-byte aligned.
- Direct-threaded code: `NEXT` is `ldr x8, [x19], #8` then `br x8`.
- All text files use LF line endings (enforced by `.gitattributes`).

## Tests

- Tests are `tests/*.in` (Forth fed to the serial console) paired with `tests/*.out` (expected output), run headless under QEMU.
- Every feature adds tests, and the whole suite runs on every change.

## Workflow

- Record any choice the brief leaves open in `DECISIONS.md` with a one-line reason.
- At the end of each milestone, update the Readme milestone table and report what passed and anything that changed the plan.
