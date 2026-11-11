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
| 24 | 2026-11-10 | ICMP "destination unreachable" quoted the packet's header and 8 bytes even when the packet ended sooner | The reply carried 8 bytes of an earlier frame still in `rx-frame`: a sender on the link, choosing the header length, could read another connection's ports and sequence number (which RFC 5961's checks rely on being secret) or 8 bytes of its data | Proof planning (V4: a parser reads only its frame) | No; repro in `tests/udp` (the peer's protocol 200 cases) | #138; proven (`Icmp.lean`) |
| 25 | 2026-11-05 | `options-mss` read an MSS option's length byte and value even when they lay past the end of the TCP header | A SYN whose options end in a truncated MSS option (kind 2 in the last byte, or kind 2 and length 4 in the last two) set the connection's MSS from bytes after the header: the segment's data, or stale bytes of an earlier frame when there was none (clamped to 64 to our MSS, so no memory harm) | Proof planning (V4 reads: a parser reads only the frame) | No | Options are read only while their bytes lie inside the header; `tcp-attack` sends both truncated forms (found before 24, merged after it) |

| 26 | 2026-11-10 | `udp-find` matched port 0 to the first free slot (a free slot holds port 0), so a datagram to UDP port 0 ran that slot's handler: one left by `udp-unbind`, or xt 0, a jump to address 0 | Any host could run a handler the application had unbound (the `udp` test's own `heard` answered a datagram to port 0), or make the network task jump to address 0 on every such datagram (a fault, caught per frame; bare metal prints a register dump each time) | Proof planning (V4 H-parse: what `udp-in` may execute, read against its table) | No; repro in `tests/udp` (the peer's port 0 case) | #140: port 0 is never found or bound |
| 27 | 2026-11-10 | `listener-of` likewise matched port 0 to a free listening slot: a SYN to TCP port 0 was answered, and once the handshake completed, the connection was queued on that free slot, where nothing accepts it and nothing times it out | Any client could open 256 such connections and fill `max-conns` for good: no further TCP connection to any port until reboot. A later `listen` taking that slot would hand its application the stale connections | Proof planning (V4 H-pool: the listeners' queues hold only connections someone will accept, read against `listener-of`) | No; repro in `tests/tcp-attack` (a SYN to port 0 must get a reset) | #140 |
| 28 | 2026-11-10 | `ms` returned as soon as the task was woken. A connection's events (data, ACKs) wake its owner, and after `close-connection` the owner stayed set, so a pooled task went on being woken by a connection it had finished with | The two-second pause between admin password tries ended as soon as the client sent anything, or its ACK arrived: the pause did not slow guessing. Any `ms` in a task that owned a connection was cut short | Proof planning (V4 H-pool: reading what keeps a connection's task pointer after the connection is given up) | No; repro in `tests/tasks` (a task woken in a loop while another sleeps 200 ms) | `ms` sleeps until its time, however often woken; `close-connection` clears the owner |
| 29 | 2026-11-10 | `fin-in` compared the FIN's sequence number, `i-seq + i-len`, with `rcv-nxt` without taking it to 32 bits | A FIN in a segment whose data crossed 2^32 was ignored, its data acknowledged and the FIN not: the connection closed only when the peer sent the FIN again on its own | Proof planning (V4: wraparound in the receive path's sequence arithmetic) | No; repro in `tests/tcp-attack` (a client whose data crosses 2^32) | Masked to 32 bits |
| 30 | 2026-11-10 | `release-conn` freed a connection already closed once the application had closed it. `close-connection` frees a closed connection itself, waiting for `conns-lock` while the timer sweep holds it; had that sweep's `catch` released the same connection (after a throw in `conn-timers`, only the watchdog's in practice), it would have been freed twice | A connection on the free list twice, so two later connections sharing one record. Not reachable short of the watchdog stopping the sweep at that connection | Proof planning (V4 H-pool: every path frees a live connection exactly once) | No | `release-conn` leaves a closed connection alone |
| 31 | 2026-11-10 | A connection's hash bucket was a hash of its addresses and ports and of `my-ip`, recomputed when it was freed: if `my-ip` had changed since, `hash-out` looked in the wrong bucket and the freed record stayed in its old one | A record recycled by `new-conn` (its hash link cleared) cut that bucket's chain, so live connections behind it could no longer be found, and `find-conn` could return the recycled record for the old addresses. Only full Forth can change `my-ip` (the console, the admin REPL, an app), not a player or a peer | Proof planning (V4 H-pool: `find-conn` returns a live connection or 0, which needs a connection's bucket fixed while it is hashed) | No; repro in `tests/tcp` | The bucket hash leaves out our address (#141) |
| 32 | 2026-11-10 | `segment-in` never checked a segment's sequence number (RFC 793's first check) before acting on its acknowledgement, and took the send window from any segment with an acceptable ACK, old or new (no SND.WL1/WL2) | An outsider needed only an acknowledgement in range, whatever sequence number they sent: one in about 2^16 guesses shut the send window (output stalled until a probe reopened it), and one in (2^32 / bytes in flight) acknowledged data the peer never had, which was then never resent and the connection stalled. A reordered old segment of the real peer could also shut the window. A segment outside the window got no ACK | Proof planning (V4: the ACK path read against RFC 793's and 5961's order of checks; the window half was TD-39) | No; repro in `tests/tcp-attack` (an ACK outside the window must draw a challenge ACK; a window of 0 outside the window, or older than the last, must not stop the next send). Seen failing on the old code | #142: `acceptable?` first, then `window-in` |
| 33 | 2026-11-10 | Challenge ACKs had no rate limit (RFC 5961 section 7; a choice, #92, logged as TD-39) | Each forged segment in range drew an ACK to the real peer: a spoofer could make the OS send as fast as it was sent to | Proof planning (TD-39) | No; repro in `tests/tcp-attack` (60 resets in the window drew 60 ACKs on the old code) | #142: per connection, bursts of 10, then 10 a second |
| 34 | 2026-11-10 | `password?` took the iteration count from the stored hash unchecked, and `pbkdf2` ran `n 1 ?do`: a count of 0 or less ran 2^64 iterations | A stored hash with a bad count (a damaged record that still passes its checksum, or an app's own record of player hashes gone wrong) hung the login for good while holding `hash-lock`: every later hash or login in the system waited behind it. It pauses, so the watchdog never stopped it | Proof planning (a password check must end and read only its 56 bytes, whatever they hold) | No; repro in `tests/crypto` (a task checking a count of 0 is still at it a second later). Seen failing on the old code | #143: counts outside 1 to `max-iterations` refused unhashed; `pbkdf2` throws -24 for a count below 1 |
| 35 | 2026-11-10 | `password?` compared the hashes with `compare`, which stops at the first byte that differs | How long a wrong guess took said how many leading bytes of its hash matched. Not usable as it stands (the salt is secret, and the 250 ms hash and the network hide nanoseconds), but it is the kind of leak a password check must not have | Hardening (review against a checklist) | No (no test can time it) | #143: `bytes-differ` reads all 32 bytes |
| 36 | 2026-11-10 | `udp-send` checked its length against `udp-max` with a signed comparison, so a negative length passed, and `cmove` took it as a count near 2^64 | An application (or a sandbox word built on it, were one ever exposed) that passed a negative length overwrote everything after `tx-frame` until it faulted | Proof planning (V4: every copy bounded by both its source and its destination, read across the network words) | No; repro in `tests/udp` (a length of -1 must throw -265). Seen failing on the old code: the hosted build's emulator itself died of a SIGSEGV | Unsigned comparison |
| 37 | 2026-11-11 | `mount` took the header's size with a signed `min`, so a negative size left `#blocks` negative, and `?block`'s unsigned check then let every block number through. The drivers turned the block number into an offset (hosted `u * 1024`) or sector (`2u`) that wraps | A data disk with a hostile header made block 2^54 an alias of block 0: reading it returned the header, and a write through it overwrote the header that `?writable` protects; writes past the end grew the hosted image | Hardening (contract: block numbers against `blk-count`) | No; repro in `tests/hosted/disk-header` | #144: `umin`; the drivers also refuse a block at or beyond `blk-count` |
| 38 | 2026-11-11 | `empty-buffers` (and `flush`) set every buffer's pin count to 0, even a buffer a `load` was reading; that `load`'s `unpin` then left the count at -1 | The buffer was never chosen again (a victim needs a count of 0): each such load lost one of the 8 buffers for good, and 8 of them left every `block` throwing -260. The loading task's source buffer could also be reassigned under it | Hardening (contract: counters that drift) | No; repro in `tests/buffers` (a screen that runs `empty-buffers flush`, loaded 9 times) | #145: buffers a `load` holds keep their block and pin |
| 39 | 2026-11-11 | `fill-copy` filled the buffer for a record's copy before `(update)` checked the block could be written | `record!` on a disk without a valid header (-258), or on block 0 (-259), left the new copy in a clean buffer: `record@` then returned data that never reached the disk, and the buffer for block 0 no longer held block 0 | Hardening (contract: what a failed write leaves) | No; repro in `tests/record-errors` | `fill-copy` checks `?block ?writable` first |
| 40 | 2026-11-11 | `record!` chose the next sequence number with a signed `max` but chose the copy to overwrite, as `record@` chose the copy to read, with an unsigned `u<`; nothing handled the count wrapping to 0 (never written) | A copy numbered 2^63 or more (a crafted disk: the checksum's key is public) made every later `record!` write a number older than it: the write succeeded and `record@` kept returning the old record | Hardening (contract: sequence comparisons that wrap) | No; repro in `tests/record-errors` | #146: sequence numbers compare as serial numbers (`newer?`), and the next skips 0; proven in `RecordSeq.lean`. `record@` also takes its maximum length as unsigned: a negative one, through a signed `min`, was a `move` of nearly 2^64 bytes |
| 41 | 2026-11-11 | `restarting` released the semaphores of a loop that ended in an error, but not the dictionary: `retire` and the REPL's `reset` do both | A system task's loop that stopped while it had claimed the dictionary kept it: every other task's next definition (the REPL, the admin session) waited for good. No base loop claims it; an app's could | Proof planning (the cleanup contract in `Semaphores.lean`) | No; repro in `tests/supervise` | `restarting` unclaims; `cleanup_wired` checks it |
| 42 | 2026-11-11 | `set-admin-password` made the new hash in `admin-pw`, the buffer every admin session reads the stored hash into (`admin-password?`, through `record@`). `hash-password` writes the count and salt, then pauses between PBKDF2 iterations before writing the hash | An admin connection arriving while the password was being set read the old record into `admin-pw` mid-hash: the record stored was the old count and salt with the new hash, so neither password worked and the admin door was shut for good (until the console set it again). Two admins running `set-admin-password` at once also shared `new-pw` | Hardening (contract: shared state across a pause) | No; repro in `tests/admin-pw` (a task reading the password while it is set) | `admin-password?` reads into `pw-read` and copies it whole without a pause; the hash is made in `new-hash`; `admin-pw-lock` serializes `set-admin-password` |
| 43 | 2026-11-11 | `bad-source?` let 0.0.0.0 and 127.0.0.0/8 through as a packet's source (TD-41, found 2026-11-10) | A forged SYN from them drew a reply sent by way of the gateway, and could open a half-open connection | Proof planning (V4, TD-41) | No; repro in `tests/hostile` (three forged SYNs, each answered on the old code) | `bad-source?` refuses both (RFC 1122 section 3.2.1.3) |

## Also shown

- **Mutation:** a `u>` changed to compare signed passed all 36 hosted tests,
  and failed its proof (`docs/verification.md`).
- **Stack comments:** of 431 stack comments checked against their code
  (272 at first, #107), none disagreed. The proofs found no defects there.

## What the log says so far

Up to 2026-11-10: 36 defects. Tests found 2, the app 1, hardening 5, and
the proofs 28 (7 directly, 5 by the audits they pointed to, 16 while
planning a proof). Of the six found planning V4's receive path and pool
(26 to 31), the first three were reachable by any client (two through port
0, which a free table slot also holds), and each but 30 fails a test
written for it. Of the next five (32 to 36), 32 and 33 are within an
off-path attacker's reach (TCP's order of checks, and challenge ACKs
without a limit), 34 needs a damaged password record, 35 is a timing
leak with no known use, and 36 an application's slip away from an
overwrite; 32 to 34 and 36 fail tests written for them, each seen failing
on the old code. (A double free in the fix for 20 was caught by
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
