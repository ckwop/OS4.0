# Defect log

Every defect found in code that was already committed, with how it was
found. The point is to compare the methods (tests, proofs, audits the proofs
pointed to, review) by what they find, not only how often they find it.

Add a row whenever a committed defect is fixed or logged as tech debt. Leave
out mistakes caught before their first commit; nothing records those
consistently.

**How found:**
- **Proof**: a proof could not be finished until the code changed.
- **Proof audit**: a hand audit of what a proof flagged (a footprint that
  writes "anywhere", a loop listed in `proofs/yields.txt`).
- **Proof planning**: reading the code against a property while setting up
  its proof, before the proof itself exists.
- **Test**: a test, or its peer, failed or showed the problem.
- **App**: using the base for an app (the MUD) showed it.
- **Hardening**: deliberate review against a threat list (RFCs, an attacker
  model), with tests written alongside.

**Tests catch it?** asks whether the test suite as it stood would have
failed. "Repro" means a test can show the bug once you know it is there, and
one now does.

## Log

| # | Date | Defect | Effect | How found | Tests catch it? | Fix |
|---|------|--------|--------|-----------|-----------------|-----|
| 1 | 2026-10-27 | A SYN to the broadcast address got an answer | An off-path host could make the OS answer for the whole subnet | Hardening (`hostile` test written for it) | No, before `hostile` | #98 |
| 2 | 2026-10-27 | ARP and IP learned a forged group (multicast) MAC | Traffic for a peer could be sent to a multicast address | Hardening (`hostile`) | No, before `hostile` | #98 |
| 3 | 2026-10-27 | A half-open TCP connection that timed out or was reset was never recycled | SYNs used up the connection pool for good | Hardening (TCP, TD-22) | No, before `tcp-attack` | #92 |
| 4 | 2026-10-27 | A peer MSS of 0 stopped sending | One hostile client could wedge its own connection | Hardening (TCP, TD-22) | No | #92 |
| 5 | 2026-10-28 | `telnet-key?` was true for the LF of CR LF, and the `key` that followed blocked | A task polling `key?` (the MUD) stalled until the next key | App (the MUD's login test) | No | #104 |
| 6 | 2026-10-29 | `serve-door` never paused while connections kept waiting | The watchdog could stop a listener under a burst of connections | Proof (`Yield.lean`) | No | #108 |
| 7 | 2026-10-29 | The TCP timer sweep walked up to 256 connections without pausing, on every frame | The watchdog could stop the network task with many connections open | Proof (`Yield.lean`) | No (`soak` uses a handful) | #109 |
| 8 | 2026-10-30 | A system call writing into a page that also held code (hosted) returned short: `pread64` gave 472 of 1024 bytes | Every block read failed once the dictionary layout moved | Test (all failed after a layout change made while building the proofs) | Yes | TD-33, #110 |
| 9 | 2026-10-31 | HOLD wrote below `numbuf` without bound in base 1 | Memory overwritten through the task's buffers and beyond (hosted: a loop of segfaults) | Proof (sandbox isolation, `Printing.lean`) | No | #114 |
| 10 | 2026-10-31 | virtio-net trusted the device's used length: over 2048 bytes overran `rx-frame` | A faulty or hostile device could overwrite memory | Proof audit (footprints, "anywhere") | No: QEMU's device is honest | #115 |
| 11 | 2026-10-31 | virtio-net: a used length shorter than the virtio header went negative, and `cmove` took it as a huge count | As above | Proof audit (footprints) | No | #115 |
| 12 | 2026-10-31 | virtio-net trusted the device's buffer id, and `rx-post` wrote a descriptor outside its table | As above | Proof audit (footprints) | No | #115 |
| 13 | 2026-10-31 | Five loops and buffers with unchecked bounds (a looping FAT chain, an rng that never answers, a second acceptor on a port, `ip-handler!`'s protocol, `hmac` outside `hash-lock`) | Each a hang or overwrite under unlikely conditions | Proof audit (footprints, `yields.txt`) | No | Open: TD-35 |
| 14 | 2026-10-31 | A task the watchdog stopped inside `get`, or in `locked` before its `catch`, held the semaphore for good | Every later user of that lock (blocks, network sends, connections) waited for ever | Proof (V6, `Semaphores.lean`) | No; repro in `tests/locks` (hung the system) | #116 |
| 15 | 2026-10-31 | A throw caught near the end of the watchdog allowance left the cleanup a few ticks; a second -262 escaped every `catch`, and the worker ran a REPL on whatever terminal it had | A client got a REPL outside the session's control and cleanup, and the pool lost the worker | Proof (V6, `Semaphores.lean`) | No; repro in `tests/watchdog` | #116 |
| 16 | 2026-10-31 | `session` set up the telnet terminal before its `catch`: a client that reset before its task ran made it throw past the cleanup | The door kept the place and the connection leaked; sixteen such clients (a port scan) shut port 4000 for good | Proof (V6, `Sessions.lean`) | No; repro in `tests/sessions` | #117 |
| 17 | 2026-10-31 | The idle timeout was set only after that terminal setup, so its send waited with no timeout | A client that never opened its window held a place at the door for ever | Proof (V6, `Sessions.lean`, same change) | No | #117 |
| 18 | 2026-10-31 | `record!` overwrote the older copy even when the newer one might not be durable: after a failed sync it could be only in a buffer | A failed disk write, a second `record!`, then a crash during its sync, lost the last durable record | Proof planning (reading `records.fs` against V3's durability property); proven in a model (`Records.lean`, `old_loses`) | No; repro in `tests/record-errors` (A's copy overwritten in the cache) | #118 |
| 19 | 2026-11-02 | `(segment-out)` copied `o-len` bytes into `tx-frame` with no bound: the frame held the data only if every caller kept the length within `our-mss` | A wrong length (a caller's slip, or a connection record gone bad) would write past `tx-frame` into whatever follows it | Proof planning (V2: the footprint of `telnet-type`'s send path said "anywhere") | No; repro in `tests/tcp` (a fake connection, -24) | #119, #122 |
| 20 | 2026-11-03 | After a failed wait, `(send)` reset the connection itself, which unlinks it from the shared connection lists | A sandboxed session whose send timed out wrote memory outside its task (other connections' links, the free list), so bounded writes failed on that path | Proof (V2, runs that fail: `Telnet.lean`) | No | #125 |
| 21 | 2026-11-04 | A virtio request that timed out stayed with the device; when it completed late, its used-ring entry was taken by the next request on that queue, and its buffer was still written | After one disk timeout, a later read could return before its data arrived, with the wrong request's status; the late write could land in a reused block buffer | Proof planning (writing the HAL contract, V4) | No: QEMU completes requests at once | Open: TD-36 (needs a device reset, the user's call) |
| 22 | 2026-11-04 | `net-send` (bare metal) copied `len` bytes into its 2 KiB transmit buffer with no bound, relying on every caller to keep frames short | A length over 2036, or a negative one, would write past `tx-buf` into the driver's other data and beyond | Proof planning (writing the HAL contract, V4) | No: the network stack never sends a frame that long | Length held to the buffer; proven (`Drivers.lean`) |
| 23 | 2026-11-04 | `net-send` (bare metal) offered the card an empty frame, header only, when asked to send 0 bytes | QEMU's virtio-net never completes such a request and marks the device broken: the send throws -263 and the network is gone until reboot | Test (`net-faults`, written for defect 22's fix: its negative length became 0) | Only once that test was written | Empty frames are not sent; the test sends again after one |
| 24 | 2026-11-05 | `options-mss` read an MSS option's length byte and value even when they lay past the end of the TCP header | A SYN whose options end in a truncated MSS option (kind 2 in the last byte, or kind 2 and length 4 in the last two) set the connection's MSS from bytes after the header: the segment's data, or stale bytes of an earlier frame when there was none (clamped to 64 to our MSS, so no memory harm) | Proof planning (V4 reads: a parser reads only the frame) | No | Options are read only while their bytes lie inside the header; `tcp-attack` sends both truncated forms |

## Also shown

- **Mutation:** a `u>` changed to compare signed passed all 36 hosted tests,
  and failed its proof (`docs/verification.md`).
- **Stack comments:** of 431 stack comments checked against their code
  (272 at first, #107), none disagreed. The proofs found no defects there.

## What the log says so far

Up to 2026-11-05: 24 defects. Tests found 2, the app 1, hardening 4, and
the proofs 17 (7 directly, 5 by the audits they pointed to, 5 while
planning a proof). (A double free in the fix for 20 was caught by
`tcp-attack` before it was committed, so it is not logged: the tests and
the proofs find different things.) No proof-found
defect would have failed the test suite as it stood. The tests had already
passed over every one of them.

They are also a different kind of bug. Hardening and the app found bugs in
behaviour: what the OS does with a packet or a keystroke. The proofs found
bugs in what must hold on every path:
- what happens when a task is stopped at an arbitrary instruction;
- what happens when a device or a peer sends the worst value it can;
- whether a loop yields however much work there is.

Tests exercise the paths someone thought to write down. Most of these bugs
live on paths nobody had thought of: a throw before a `catch` exists, a
second watchdog fire during cleanup, a length the device should never send.
Several matter for security: a REPL outside the session's control, a door
shut for good, memory overwritten.

Read the counts with care:
- The record is biased. Before the proofs (to 2026-10-28), bugs fixed in
  the same commit that introduced them were never logged. This log starts
  from the bugs written down in DECISIONS.md, the tech-debt list and commit
  messages.
- The proofs came after the tests, so they searched code the tests had
  already cleaned.
- Proof found is not the same as proof only. Once a proof says where to
  look, a test can often show the bug; for 14 to 16 one now does.
