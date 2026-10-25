# Decisions

A running log of choices that [docs/brief.md](docs/brief.md) leaves open. Add new entries at the bottom: one line of decision, one line of reason.

| # | Date | Decision | Reason |
| --- | --- | --- | --- |
| 1 | 2026-10-25 | Use Rancher Desktop (dockerd/moby runtime) on WSL2 instead of Docker Desktop. | Same `docker` CLI and image format the brief assumes, with no Docker Desktop licence terms. |
| 2 | 2026-10-25 | Force LF line endings for all text files via `.gitattributes`. | The host is Windows with `core.autocrlf=true`, but shell scripts, Makefiles, Forth screens and `.out` test files are consumed inside Linux and diffed byte-for-byte. |
| 3 | 2026-10-25 | Keep the brief at `docs/brief.md`. | A stable, ASCII-only path that docs and agent instructions can link to. |
| 4 | 2026-10-25 | Milestone 2 is done only when `docker run -it os4` gives an interactive Forth prompt, in addition to its test suite. | Matches the brief's "docker run -it drops the user into the Forth prompt" and is the user-facing check. |
| 5 | 2026-10-25 | Base image `debian:trixie-slim`. | Current Debian stable; packages cross binutils, QEMU (system and user), AArch64 UEFI firmware and gforth. |
| 6 | 2026-10-25 | Limine pinned by commit (`ee5d29c`, branch `v9.x-binary`) from Codeberg, with the host `limine` tool built in the image. | Not packaged by Debian; pinning keeps builds reproducible. |
| 7 | 2026-10-25 | Assembly sources are `.s` files assembled with plain `as`; constants via `.equ`, reuse via `.macro`. | No cross C compiler or preprocessor in the toolchain, and none is needed. |
| 8 | 2026-10-25 | The image copies and builds the source at `docker build` time, with `make run` as its default command; bind-mount `/src` to work on live source. | `docker run -it os4` then works with no extra arguments. |
| 9 | 2026-10-25 | Test runner applies a per-test timeout (`TEST_TIMEOUT`, default 10 s). | A hung kernel must fail its test rather than stall the suite. |
| 10 | 2026-10-25 | Install gforth 0.7.3 from the bookworm repository on the trixie base. | Trixie no longer packages gforth; bookworm's installs cleanly, and staying on trixie keeps QEMU 10.0 rather than 7.2. |
| 11 | 2026-10-25 | gforth provides expected output only for tests of standard words; OS-specific tests have hand-written `.out` files. | Prompts, error text and non-standard words differ between gforth and our system by design. |
| 12 | 2026-10-25 | Every non-primitive word starts with an 8-byte code field `<insn>; bl <handler>`; the handler finds the body in `x30`. `DOES>` compiles `mov x9, x30; bl dodoes` into the defining word. | The simplest direct-threaded scheme on AArch64: one uniform code field for colon, variable, constant and `DOES>` words. |
| 13 | 2026-10-25 | Dictionary header: link cell, flags/length byte (immediate, hidden, 5-bit length), name, padding to 8 bytes, then the xt. | Minimal and 8-byte aligned; 31-character names are plenty. |
| 14 | 2026-10-25 | The bootstrap kernel is about 75 words, more than the brief's ~30: it includes the assembly outer interpreter and compiler basics, plus hot-path primitives (`do`/`loop` runtime, `pick`, `um/mod`). | The brief starts from an assembly outer interpreter; the count falls when the metacompiler moves the interpreter and compiler into Forth. |
| 15 | 2026-10-25 | The kernel source is split into files that `kernel.s` includes, forming one assembly unit. | The dictionary link chain (`.set link`) must run across every word; separate objects would break it. |
| 16 | 2026-10-25 | `forth/core.fs` is embedded with `.incbin` and interpreted line by line at start-up; an error there prints `core.fs:<line>:` and exits with status 1. | One self-contained binary; a broken core.fs fails loudly rather than leaving a half-built system. |
| 17 | 2026-10-25 | The Forth echoes its own input. The hosted build puts a terminal stdin into raw mode (restored on exit), so tests are transcripts: echoed input, output, then ` ok`. | A serial console does not echo, so bare metal must echo itself; doing the same hosted keeps tests identical across platforms. |
| 18 | 2026-10-25 | Prompts: ` ok` after a line while interpreting, ` compiled` while compiling, nothing during core.fs. Errors print `name ?` or a message, reset both stacks and discard the line. | Classic Forth behaviour, close to gforth. |
| 19 | 2026-10-25 | Division is floored, word lookup is case-insensitive, and numbers accept `-`, the prefixes `$` `#` `%`, and `'c'`. | Matches gforth, so gforth can check our test outputs. |
| 20 | 2026-10-25 | Branch cells hold absolute target addresses. | Simplest to compile and to read in a dump; no relocation needed in one flat address space. |
| 21 | 2026-10-25 | The hosted build makes its dictionary executable with `mprotect`; bare metal gets this from its flat RWX memory. | New code fields are written at run time and must be executable. |
| 22 | 2026-10-25 | `x24`–`x28` are free scratch registers for primitives across subroutine calls. | Subroutines preserve them under AAPCS64, and the Forth machine state uses only `x19`–`x23`. |

## Open questions (from the brief)

Still unresolved; move each to the table above once decided.

- Fargate container architecture: one x86 image everywhere, or an ARM64 build for cheaper Graviton tasks?
- Player cap for the first release (sizes the task pool and TCP connection table; 64 assumed).
- MUD port number (4000 assumed), and whether to offer only a plain telnet port.
- Password hash algorithm, implemented in Forth.
- When to move from the assembly outer interpreter to a metacompiled image.
