# Technical debt register

Known shortcuts, gaps and risks in OS 4.0, and what we plan to do about them. Add an entry when you take a shortcut or find a gap; close it, with the commit or decision that fixed it, when it is gone. Closed entries stay here as a record.

**Impact:** *high* can lose data or crash the system; *medium* wrong behaviour in some cases, or a real cost; *low* tidiness or convenience.

## Open

| ID | Debt | Impact | Plan |
| --- | --- | --- | --- |
| TD-7 | The block layer is not safe for two tasks at once: a task that paused mid-request could have its buffer reused. Disk waits therefore spin without `pause` (DECISIONS.md #54). | high, once a second task uses blocks | Add a lock around block requests, then let disk waits pause. Before the MUD's saver task (milestone 10). |
| TD-8 | Device waits (`vq-wait`) have no timeout: a device that never answers hangs its task. | medium | Use timed waits with the network driver (milestone 6), then apply them to the disk. |
| TD-9 | Idle costs about 5% of a core under QEMU emulation: the 100 Hz tick and the console's 10 ms key polling keep waking the CPU (DECISIONS.md #51, #53). | medium on Fargate | Tickless idle (program the timer for the next wake time) and a UART receive interrupt. Before Fargate (milestone 11). |
| TD-10 | Magic numbers in more than one place: header flag bits (32, 64, 128) are written out in several Forth files, and kernel throw codes appear both as `.equ` lines and as `message:` lines. | low | Named constants for the flag bits; keep each throw code's number and message together. Tidy when next touching those files. |
| TD-11 | The kernel has about 110 assembly words, against the brief's ~30. Most are constants, user variables, the bootstrap interpreter and device access; the bootstrap duplicates parsing and lookup that the Forth side also has (boot-only since TD-5). | low | Accepted by DECISIONS.md #14, #32 and #33. Revisit only if metacompilation comes back. |
| TD-12 | Assembly hot spots have no Forth reference definition beside them, although CLAUDE.md asks for one: the loop runtime (`(do)` `(loop)` `(+loop)` `i` `j`), `pick`, `um/mod`. | low | Add the Forth versions as comments in `core.fs`. |
| TD-13 | Stack overflow is checked at calls, branches and loops. A straight run of more than 16 pushes with none of those in between could pass the limit undetected. | low | Accepted: such code is unusual. A guard page would close it if tasks ever get their own mappings. |
| TD-14 | The repository lives under OneDrive, which syncs `build/` (a 64 MB boot image, data disks) on every build. | low (environment) | The user's call: exclude `build/` from sync, or move the repository out of OneDrive. |

## Closed

| ID | Debt | Fixed by |
| --- | --- | --- |
| TD-1 | Nothing guarded the stacks: a task's data stack overflowed into its own user area, and its return stack into its data stack. | Stack limits checked in calls, branches, loops and `pause`; kernel errors unwind to the `catch` frame before throwing (DECISIONS.md #57). |
| TD-2 | Nothing guarded the dictionary: `allot` and `,` could write past its end. | Bounds checks throwing -8, and `unused` (#58). |
| TD-3 | The block buffer eviction path (write back a changed buffer to reuse it), `flush` and `empty-buffers` were never tested. | `tests/buffers`. |
| TD-4 | On the hosted build a bad address killed the program; bare metal recovered. | `SIGSEGV`, `SIGBUS` and `SIGILL` handlers report and throw -256 (#61). |
| TD-5 | Two lookup paths after boot: `'`, `[']` and `postpone` used the kernel's lookup, which future wordlists would not govern. | Rebuilt on the Forth `find-word` (#59). |
| TD-6 | The serial test suite ran one VM at a time, about 10 s per test. | `tools/run-tests.py` runs tests in parallel with a disk each; 18 serial tests in under a minute (#62). |
