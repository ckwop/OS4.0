# Decisions

A running log of choices that [docs/brief.md](docs/brief.md) leaves open. Add new entries at the bottom: one line of decision, one line of reason.

| # | Date | Decision | Reason |
| --- | --- | --- | --- |
| 1 | 2026-10-25 | Use Rancher Desktop (dockerd/moby runtime) on WSL2 instead of Docker Desktop. | Same `docker` CLI and image format the brief assumes, with no Docker Desktop licence terms. |
| 2 | 2026-10-25 | Force LF line endings for all text files via `.gitattributes`. | The host is Windows with `core.autocrlf=true`, but shell scripts, Makefiles, Forth screens and `.out` test files are consumed inside Linux and diffed byte-for-byte. |
| 3 | 2026-10-25 | Keep the brief at `docs/brief.md`. | A stable, ASCII-only path that docs and agent instructions can link to. |

## Open questions (from the brief)

Still unresolved; move each to the table above once decided.

- Fargate container architecture: one x86 image everywhere, or an ARM64 build for cheaper Graviton tasks?
- Player cap for the first release (sizes the task pool and TCP connection table; 64 assumed).
- MUD port number (4000 assumed), and whether to offer only a plain telnet port.
- Password hash algorithm, implemented in Forth.
- When to move from the assembly outer interpreter to a metacompiled image.
