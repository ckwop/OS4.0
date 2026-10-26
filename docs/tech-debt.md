# Technical debt register

Known shortcuts, gaps and risks in OS 4.0, and what we plan to do about them. Add an entry when you take a shortcut or find a gap; close it, with the commit or decision that fixed it, when it is gone. Closed entries stay here as a record.

**Impact:** *high* can lose data or crash the system; *medium* wrong behaviour in some cases, or a real cost; *low* tidiness or convenience.

## Open

| ID | Debt | Impact | Plan |
| --- | --- | --- | --- |
| TD-9 | Idle costs about 5% of a core under QEMU emulation: the 100 Hz tick, the console's 10 ms key polling and the network task's 10 ms interface polling keep waking the CPU (DECISIONS.md #51, #53, #67). Polling also adds up to 10 ms to every ping. | medium on Fargate | Tickless idle (program the timer for the next wake time), and UART and virtio interrupts to wake the waiting task. Before Fargate (milestone 11). |
| TD-11 | The kernel has about 110 assembly words, against the brief's ~30. Most are constants, user variables, the bootstrap interpreter and device access; the bootstrap duplicates parsing and lookup that the Forth side also has (boot-only since TD-5). | low | Accepted by DECISIONS.md #14, #32 and #33. Revisit only if metacompilation comes back. |
| TD-13 | Stack overflow is checked at calls, branches and loops. A straight run of more than 16 pushes with none of those in between could pass the limit undetected. | low | Accepted: such code is unusual. A guard page would close it if tasks ever get their own mappings. |
| TD-14 | The repository lives under OneDrive, which syncs `build/` (a 64 MB boot image, data disks) on every build. | low (environment) | The user's call: exclude `build/` from sync, or move the repository out of OneDrive. |
| TD-17 | The network stack ignores IP options, and drops fragmented packets. | low | Reassembly only if a real need appears; nothing we send or expect is fragmented. |
| TD-18 | The address, netmask and gateway are set at boot to QEMU's user-networking values (variables `my-ip`, `netmask`, `gateway`). On EC2 the VPC assigns addresses by DHCP. | high for milestone 12 | A DHCP client over UDP, falling back to the static values. Before the EC2 AMI (milestone 12). |
| TD-21 | The dictionary is capped at 128 MiB (the reach of `bl`, DECISIONS.md #72); RAM beyond it is unused, and nothing is ever freed. That holds thousands of players, but not an unbounded number. | low | If ever needed: a page allocator over the rest of RAM for bulk data such as connection buffers, or more trampolines further into memory. |

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
| TD-19 | Every virtqueue had 8 entries in a fixed layout, so the NIC had 8 receive buffers. (Under QEMU this lost nothing: its network backends hold frames back while the guest has no buffers. Real NICs drop them.) | Virtqueues sized per use; 64 receive buffers (DECISIONS.md #75). `tests/udp` round-trips a burst of 48 datagrams. |
| TD-17a | No ICMP errors were sent. | Port and protocol unreachable (#74); IP options and fragments remain under TD-17. |
| TD-20 | All memory was the 1 MB dictionary inside the kernel image; the rest of RAM was unused, so pools could not grow. | The dictionary moved to RAM from the platform, up to 128 MiB (#72). Pools now `allot` from it. |
| TD-7 | The block layer is not safe for two tasks at once: a task that paused mid-request could have its buffer reused. Disk waits therefore spin without `pause` (DECISIONS.md #54). | Block words hold `blocks-lock`; device waits pause; `last-buf` and `scr` per task (DECISIONS.md #77). `tests/locks` writes 60 blocks from two tasks. |
| TD-10 | Magic numbers in more than one place: header flag bits (32, 64, 128) are written out in several Forth files, and kernel throw codes appear both as `.equ` lines and as `message:` lines. | Flag bits from the kernel as `f-` constants; the throw-code lists cross-reference each other (#79). |
| TD-12 | Assembly hot spots have no Forth reference definition beside them, although CLAUDE.md asks for one: the loop runtime (`(do)` `(loop)` `(+loop)` `i` `j`), `pick`, `um/mod`. | `pick-ref` and `um/mod-ref`, checked by `tests/reference`; the loop runtime as commented Forth (#79). |
| TD-15 | Outgoing packets share one `tx-frame`. That is safe only because building and sending a packet never pauses; a task that paused in between would have its packet overwritten. | `tx-lock` around every build-and-send (#78). |
| TD-16 | `ip` reads dotted addresses without checking them: `ip 300.1` gives a wrong address, not an error. | `ip` checks four parts of 0-255 and throws -268 (#79); `tests/ip`. |
