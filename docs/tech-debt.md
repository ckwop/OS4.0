# Technical debt register

Known shortcuts, gaps and risks in OS 4.0, and what we plan to do about them. Add an entry when you take a shortcut or find a gap; close it, with the commit or decision that fixed it, when it is gone. Closed entries stay here as a record.

**Impact:** *high* can lose data or crash the system; *medium* wrong behaviour in some cases, or a real cost; *low* tidiness or convenience.

## Open

| ID | Debt | Impact | Plan |
| --- | --- | --- | --- |
| TD-7 | The block layer is not safe for two tasks at once: a task that paused mid-request could have its buffer reused. Disk waits therefore spin without `pause` (DECISIONS.md #54). | high, once a second task uses blocks | Add a lock around block requests, then let disk waits pause. Before the MUD's saver task (milestone 10). |
| TD-9 | Idle costs about 5% of a core under QEMU emulation: the 100 Hz tick, the console's 10 ms key polling and the network task's 10 ms interface polling keep waking the CPU (DECISIONS.md #51, #53, #67). Polling also adds up to 10 ms to every ping. | medium on Fargate | Tickless idle (program the timer for the next wake time), and UART and virtio interrupts to wake the waiting task. Before Fargate (milestone 11). |
| TD-10 | Magic numbers in more than one place: header flag bits (32, 64, 128) are written out in several Forth files, and kernel throw codes appear both as `.equ` lines and as `message:` lines. | low | Named constants for the flag bits; keep each throw code's number and message together. Tidy when next touching those files. |
| TD-11 | The kernel has about 110 assembly words, against the brief's ~30. Most are constants, user variables, the bootstrap interpreter and device access; the bootstrap duplicates parsing and lookup that the Forth side also has (boot-only since TD-5). | low | Accepted by DECISIONS.md #14, #32 and #33. Revisit only if metacompilation comes back. |
| TD-12 | Assembly hot spots have no Forth reference definition beside them, although CLAUDE.md asks for one: the loop runtime (`(do)` `(loop)` `(+loop)` `i` `j`), `pick`, `um/mod`. | low | Add the Forth versions as comments in `core.fs`. |
| TD-13 | Stack overflow is checked at calls, branches and loops. A straight run of more than 16 pushes with none of those in between could pass the limit undetected. | low | Accepted: such code is unusual. A guard page would close it if tasks ever get their own mappings. |
| TD-14 | The repository lives under OneDrive, which syncs `build/` (a 64 MB boot image, data disks) on every build. | low (environment) | The user's call: exclude `build/` from sync, or move the repository out of OneDrive. |
| TD-15 | Outgoing packets share one `tx-frame`. That is safe only because building and sending a packet never pauses; a task that paused in between would have its packet overwritten. | medium, from milestone 8 | Before TCP, which will wait mid-conversation: one frame per sender, or a lock. |
| TD-16 | `ip` reads dotted addresses without checking them: `ip 300.1` gives a wrong address, not an error. | low | Check four octets of 0-255; throw otherwise. |
| TD-17 | The network stack sends no ICMP errors (port or protocol unreachable) and ignores IP options and fragments. | low | Add destination-unreachable replies with UDP (milestone 7); fragments only if a real need appears. |
| TD-19 | Every virtqueue has 8 entries, and its page layout in `hal/virtio.fs` is written for that size. The NIC therefore has only 8 receive buffers: more than 8 frames between two polls (10 ms apart) are dropped. | medium, from milestone 8 | Compute the layout from the queue size; give the receive queue 64 or more buffers. Before milestone 8's 32-client test. |
| TD-18 | The address, netmask and gateway are set at boot to QEMU's user-networking values (variables `my-ip`, `netmask`, `gateway`). On EC2 the VPC assigns addresses by DHCP. | high for milestone 12 | A DHCP client over UDP, falling back to the static values. Before the EC2 AMI (milestone 12). |

## Closed

| ID | Debt | Fixed by |
| --- | --- | --- |
| TD-1 | Nothing guarded the stacks: a task's data stack overflowed into its own user area, and its return stack into its data stack. | Stack limits checked in calls, branches, loops and `pause`; kernel errors unwind to the `catch` frame before throwing (DECISIONS.md #57). |
| TD-2 | Nothing guarded the dictionary: `allot` and `,` could write past its end. | Bounds checks throwing -8, and `unused` (#58). |
| TD-3 | The block buffer eviction path (write back a changed buffer to reuse it), `flush` and `empty-buffers` were never tested. | `tests/buffers`. |
| TD-4 | On the hosted build a bad address killed the program; bare metal recovered. | `SIGSEGV`, `SIGBUS` and `SIGILL` handlers report and throw -256 (#61). |
| TD-5 | Two lookup paths after boot: `'`, `[']` and `postpone` used the kernel's lookup, which future wordlists would not govern. | Rebuilt on the Forth `find-word` (#59). |
| TD-6 | The serial test suite ran one VM at a time, about 10 s per test. | `tools/run-tests.py` runs tests in parallel with a disk each; 18 serial tests in under a minute (#62). |
| TD-8 | Device waits (`vq-wait`) had no timeout: a device that never answered hung its task. | 5-second timeout throwing -263 (#70). |
