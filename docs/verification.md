# Verification plan

How we use Lean to certify properties of the OS 4.0 base, milestone by
milestone. This is the second track beside the MUD: it strengthens the base,
and it runs in this repository because the proofs are about this code.

## The approach

Proofs are about the system as it is compiled, never about a copy of it.

1. `make proofs-extract` boots the hosted build, which loads every boot file,
   and dumps each word's compiled thread (`tools/dump-words.fs`).
2. `tools/forth2lean.py` turns the threads into Lean definitions
   (`proofs/OS4/Words.lean`, generated). It also certifies each word's stack effect
   (`Specs.lean`) and the system tasks' step counts (`Costs.lean`), all generated.
3. `proofs/OS4/Machine.lean` models what the primitives do. It is the trusted
   base, and every milestone below either uses it or shrinks it.
4. Hand-written theorems (`proofs/OS4/*.lean`) state the properties that
   matter. `lake build` checks them all.

Change a word's Forth, and its generated definition changes with it. A theorem
that no longer holds fails the build, as a test would.

## Where we are

| | |
| --- | --- |
| Colon words modelled | 624 of 639, `interpret` and `find-name` included |
| Not modelled | Code fields (`cf,`, `does-cf,`), the kernel's `parse-find`, defining words with DOES>, and the words that use them |
| Model covers | Stacks, byte memory, loops, DOES> children, strings, CATCH/THROW/EXECUTE, PAUSE and the outside world as unknown; the compiler and interpreter primitives (`,`, `header`, `parse`, `parse-name`, `search-list`) |
| Proven | 903 stack effects and footprints, and 431 stack comments; the arithmetic and stack words for all inputs; `fill-ref` equal to `fill`; the system tasks' steps between pauses; a sandboxed INTERPRET executes only the sandbox's words (V2), for the sandbox `sandbox.fs` builds, on the console or a network session (`isolated`), given what a session rests on (`Box.Net`); a task's cleanup frees exactly the semaphores it holds and its dictionary claim, and `locked` releases however its xt ends; a session gives its door's place back and closes its connection however its work ends (V6); in a model of the disk, the record protocol keeps the last durable record whatever fails (V3) |
| Found | (every defect, and how it was found: [defects.md](defects.md)) A listener and the TCP timer sweep that could run without pausing (#108, #109); HOLD writing past `numbuf` in base 1 (#114); the virtio-net driver trusting the device's buffer id and length (#115, from an audit of every "anywhere" footprint); a semaphore held for good by a task the watchdog stopped inside `get` or `locked`, and a worker turned into a REPL by a throw nothing caught (#116); a client gone before its session started keeping its place at the door, so sixteen shut the door for good (#117); `record!` overwriting the copy holding the last durable record after a failed sync (#118). All fixed |
| Shown to catch | A signed `u>` that passes all 36 hosted tests fails its proof |

Three kinds of compositional proof now exist, all built the same way. The
generator infers a certificate, Lean checks it by `decide`, and one bridge
theorem, proven once, turns the certificate and the callees' theorems into
the word's own theorem:

- **Stack effects** (`Spec.lean`, #107);
- **step counts between pauses** (`Yield.lean`, #108);
- **footprints:** what a word may write, and where its outputs came from
  (`Footprint.lean`, #111). Reads are next (V9).

Footprints in detail (DECISIONS.md #111):

- **903 footprints proven,** one for every word with a stack effect. 589
  write nothing, 93 write named places (`claim` only `dict-owner`; `ms` only
  its own task's `task-status` and `task-wake`; `+!` only the cell at its
  address), and 221 may write anywhere (61 of them only because they print or read through a
  task's vector, whose words' footprints are not stated; #128). `build/footprints.txt` lists each.
- **System calls:** one whose number shows it fills no buffer (write,
  socket, ...) writes nothing; read, pread64 and getrandom may write
  anywhere (#121).
- **Values are symbolic:** an input plus an offset, the user area plus an
  offset, a word's address, a number, or unknown. They follow the stacks
  through `swap`, `>r`, `+` of a literal and every proven callee.
- **"Anywhere"** means an address read from memory or computed in a loop.
  For those, a hand-written proof gives the exact footprint: `fill-ref`
  writes only its n bytes (`Refs.lean`).
- **The task's own writes:** what other tasks or devices change across a
  pause is not counted (`Quiet`).

Stack effects in detail (DECISIONS.md #107):

- **903 effects proven:** every word with a fixed effect, loops included. Each is proven from a certificate and from its callees' theorems. 624 of 639 colon words are modelled, since the generator decodes `(s")` (now a colon word) and stops at the data a `message:` leaves after a word, and the compiler and interpreter primitives are modelled.
- **The `?dup if` idioms (#120):** `?dup` just before a `0branch`, or before `0=` and a `0branch`, is one step of the certificate (`QDup`, `ZEq`): zero goes one item down, anything else on at the same depth. They gave 66 more effects (from 721).
- **`['] word sem locked` (#121):** one step of the certificate, with word's effect, and word's footprint plus the semaphore's 16 bytes (`Runners.lean`). That the literal xt runs word is trusted (`Runs`), and shows as an instance argument in every theorem that rests on it. It gave 50 more effects.
- **431 stack comments proven in their own terms:** none disagree with their code.
- **What is still missing a proven effect:**
  - words whose effect depends on their data (`digit?`, `get-order`, `reset`'s `begin depth while`);
  - words that run an xt from memory or the stack (`type`, `emit`, `key`, `bye`), or CATCH and go on after an error: the model cannot say what a failing word left on the stack, so CATCH's result has no fixed effect;
  - every word that calls one of those.

Trusted today:

- **The primitive models:** each is written to mirror its assembly.
- **The CATCH and THROW specifications.** A failure with code 0, which THROW never makes, is not caught (#121).
- **The dumper and the generator.** In particular, `Runs`: the literal xt of each word handed to LOCKED runs that word (#121); and `Vectored`: TYPE, KEY, KEY? and BYE have the effect every word their vector may hold has (#128).
- **`>phys`** (bare metal): a fixed but unknown function of its input (#133).
- **Lean's kernel.**
- **One abstraction:** the outside world (other tasks, devices, the clock) is unknown, and theorems hold whatever it does.
- **For step counts (`Yield.lean`):**
  - the counted semantics is generated beside the plain one, not proven equal to it;
  - the tables in `proofs/yields.txt` hold only the words listed there;
  - the loops listed there as not counted end.

## Principles for every milestone

- **Proofs gate the milestone.** `make proofs` checks them all, and a
  milestone is not done while it fails. They join `make test` once they are
  fast enough (TD-30).
- **Coverage only goes up.** Record the number of modelled words and proven
  effects; the build fails if either drops without a decision in DECISIONS.md.
- **Every trust assumption is written down.** Each one goes in `Machine.lean`'s header and in this file's trusted list, and each milestone says what it adds or removes.
- **No `sorry`.** An unproven theorem is a missing theorem, not a placeholder.
- **The course gets a lecture and tour on proofs.** Like every other area.

## Roadmap

Milestones are numbered as they were first planned; this is the order they
run in. Three rules set it:

- **Foundations first:** work that several milestones need comes first.
- **Exposure next:** what players reach comes before launching the MUD, and
  what the internet reaches before milestone 11.
- **Depth last:** proofs that only remove trust come after those that rule out
  attacks.

Effort is relative: S is a session or two, XL is many.

| Phase | Milestone | Size | Why then |
| --- | --- | --- | --- |
| 1. Foundations | V1: proofs fast enough for `make test` (TD-30) | M | Every later phase adds proofs. Incremental now (#110), but at eight minutes after a change to `core.fs`, they cannot yet gate each change. |
| | V9: footprints, what a word may read and write (writes done, #111) | M | V2, V4 and V6 all need it. |
| | V1: models of the interpreter primitives, and `search-list-ref` | S | V2 needs `interpret` modelled. |
| | Course: a lecture and tour on the proofs | S | Explains the approach once, while it has three kinds of proof: the model, certificates and bridges, stack effects, step counts, and what they found. |
| 2. Before players | V2: sandbox isolation (done, #113, #114, #123) | M | The brief's hard rule, and what every player reaches. |
| | V6: a stopped task leaves nothing broken (semaphores, the dictionary and sessions done, #116, #117) | M | A player can make the watchdog fire, or drop the connection, at any point. |
| | V10: proofs for an app (the MUD first) | M | The MUD's own tasks and commands, on the base's results. |
| | V3: crash-safe records (the protocol proven in a model, #118) | M | Player data survives a crash at any point. |
| 3. Before the internet (milestone 11) | V4: the network survives any input | L | Every byte from anyone goes through it. |
| 4. Depth | V7: TCP state machine | XL | Off-path attacks and the RFC's invariants. |
| | V5: primitives against the assembly | L | Removes the largest trusted piece. |
| | V8: cryptography | XL | Removes trust in SHA-256, HMAC, PBKDF2, SipHash. |
| | V1: the rest | S each | The `?dup` idiom, vectored words, other reference words, TD-13. Done when convenient. |

A phase gates the milestone it names. The MUD does not launch until phase 2
is done. Milestone 11 (Fargate) waits for phase 3, alongside the open tech
debt marked **must fix before public**.

## Milestones

### V1: Proofs in the suite — S

- **Proofs in the build:**
  - Lean in the `os4` image, or a tagged `os4-lean` image built with it.
  - `make proofs` added to `make test`.
  - The coverage check described above: done (#128, `proofs/coverage.txt`).
- **Stack comments:** every plain stack comment proven, including words with
  loops. The work left:
  - branches that end in THROW of a known code: done (#128; the `?dup` idioms #120);
  - effects for vectored words (`type`, `key`, `key?`, `bye`): done, as the trusted hypothesis `Vectored` (#128);
  - get the proof build fast enough for every `make test`. It is now
    incremental (#110): seconds unchanged, about a minute for a late boot
    file, eight minutes for `core.fs`; the certificates are the cost left.
- **Reference definitions:** each one proven equal to its primitive's model.
  These are `fill-ref`, `cmove-ref`, `cmove>-ref`, `pick-ref`, `um/mod-ref` and
  `search-list-ref`. Together they give the brief's "keep the Forth definition
  as the reference" a check. Done: `fill-ref`, `cmove-ref`, `cmove>-ref`,
  `um/mod-ref` (wherever UM/MOD divides; #127), `search-list-ref` (#131), so
  every reference word but `pick-ref`.
  `pick-ref` reads the stack through `sp@`, and the model keeps the stacks as
  lists, not in memory, so it stays checked by `tests/reference` (#126).
- **TD-13 (stack overflow between checks):** done (#126). A static pass in
  the proof build shows that no run between two stack checks pushes more than
  the 16 cells of headroom, on either stack (deepest 7; `build/stack-runs.txt`).
- **Done when:** proofs run in `make test`; the coverage numbers are recorded
  and checked; every reference word is proven.
- **Status:** done (#126-131). The one reference word left, `pick-ref`, cannot
  be stated in the model (the stacks are lists, not memory) and stays checked
  by `tests/reference`.

### V2: Sandbox isolation — M

The brief's rule, "never let a player-facing wordlist reach the full
dictionary", becomes a theorem.

- **Model:** wordlists and the search order as linked lists in memory;
  `find-name`, `search-list` and `interpret`.
- **Properties:**
  - **Isolation:** for any input line, a task whose search order is the
    sandbox alone executes only the exposed words and their callees.
  - **Number words:** a number in the line only pushes a value.
  - **No arbitrary `execute`:** no exposed word executes an xt it was given.
  - **Bounded writes:** no exposed word writes memory outside its task's own
    buffers. This is a footprint theorem: everything else is unchanged.
- **Done when:** these hold for the sandbox as `sandbox.fs` builds it. Adding
  a word to `expose` must keep them true or fail the build.
- **Status:** done (#113, #114, #123-125). Isolation, number words, no arbitrary EXECUTE and bounded writes hold for the sandbox as built, for runs that return and runs that fail.
  - **The theorem:** EXECUTE replaced by anything that agrees on the
    sandbox's xts gives the same result, for any line.
  - **Its setting:** the search order is the sandbox alone, which is not the
    compilation wordlist; STATE is 0; its headers form a chain that ends.
  - **Also shown:** a number takes the path that writes only `base`, and
    never reaches LITERAL or EXECUTE.
  - **The sandbox as built:** the dump lists the sandbox wordlist's words
    (`«sandbox-wordlist».words`, generated), and `sandbox_isolated` states
    isolation for them. The 40 that compute (arithmetic, stack words, `hex`,
    `decimal`, `(`, `\`) are proven to keep the setting from their frames
    (`sandbox_keeps`).
  - **The words that print** (`Printing.lean`, #114): all 11 keep the
    setting, given that the task's own `type` and `bye` do.
    `isolated_given_terminal` is the theorem with only those two left.
    - most are threads whose every call keeps it (`thread_keeps`);
    - EMIT and `<#` store to their own user variables, `emitted` and `hld`;
    - `."` never reaches its compiling branch, as STATE is 0;
    - HOLD writes through `hld`. Its range check, added for this (#114),
      keeps the byte inside the task's `numbuf`.
  - **The terminal** (`Terminal.lean`): `type` and `bye` run what the
    task's vectors `'type` and `'bye` hold. Those cells are now part of the
    setting, so no sandbox word can change them, and `Box.Term` says what
    they hold: the console's `console-type` and the kernel's BYE, or a
    session's `telnet-type` and `end-session`. `term-conn`, the session's
    connection, is part of the setting too.
  - **The connection's output** (`Telnet.lean`, #123): `telnet-type`,
    `(send)` and `io-wait` are proven an instruction at a time (`GQ`). Words
    that only read have frames; `tcp-output`, `io-start`, the stores and the
    waits have footprints (`tcp-output`'s is precise since #122). After a
    failed wait, `(send)` resets the connection and throws again: from those
    points it never returns, so what they write does not matter. `isolated`
    is the whole result.
  - **Assumed:**
    - **`hdump`:** each header on the sandbox's chain runs one of the words
      the dump found there (the dumper is trusted);
    - **`Box.Net`,** for a network session: no other task or device writes
      the setting or the task's `cur-conn`; the connection's record (12464
      bytes) misses them; and so do TCP output's regions for the connection
      (`«tcp-output».regs`: the frames and the network's variables). All are
      true by allocation (the record and the frames come from `reserve`,
      the variables from the dictionary, apart from the user area and the
      sandbox's headers), but the model has no allocator to prove it from;
    - **`Runs`** for the five words the network runs by xt: `io-wait` (under
      CATCH), `(tcp-output)`, `(segment-out)`, `(arp-request)` and
      `(free-conn)` (under LOCKED).
  - **Bounded writes** (#124): the setting includes every byte outside the
    task's own memory (`Box.own`: its user area, its buffers, and for a
    session its connection) that nothing else writes. So keeping the setting
    is bounded writes: `bounded_writes` for each exposed word, `line_bounded`
    for a whole line.
  - **Runs that fail** (#125): keeping the setting, frames and footprints
    included, holds for runs that fail as well as those that return
    (`run_err`, `KeepsE`). So a line that throws leaves the setting, and the
    bytes outside the task's own memory, as they were (`interpret_fails`,
    `line_bounded`), and the next line's isolation starts from it. A send
    whose wait fails leaves the reset to the TCP task's sweep, so the
    sandboxed task's failure writes only its connection.
  - **No arbitrary EXECUTE:** the proofs account for every call of every
    word a sandboxed line can reach, and the only xts run are INTERPRET's
    (the sandbox's words, proven), TYPE's and BYE's (the setting's vectors,
    `Box.Term`), and the network's literal xts (`Runs`). No exposed word runs
    an xt from its stack.
  - **The tools it added** (`Steps.lean`):
    - `run_congr`: two threads that agree wherever an invariant holds give
      the same result;
    - invariants checked one instruction at a time;
    - `Frame`: what a word may write whatever its stack does, for words with
      no fixed stack effect (`?dup`, `number?`, `find-name`).

### V3: Crash-safe records — M

The brief's `sync` rule and DECISIONS.md #95.

- **Model:** the disk as blocks; the block cache (`blocks.fs`); and the HAL's
  `blk-write` and `blk-flush` as disk operations. A crash can happen between
  any two of them, and a write in progress may tear.
- **Properties:**
  - **No garbage:** after a crash at any point in `record!`, `record@` returns
    the old record or the new one, never anything else.
  - **Durability:** once `record!` returns, `record@` returns the new record
    after any later crash.
- **Ordering:** the new-player order (record, `sync`, index entry, `sync`)
  never leaves an index entry pointing at a missing record. This is stated
  for the base as a pattern; the MUD reuses it.
- **Assumption, stated:** a torn copy fails its SipHash check. That holds with
  overwhelming probability, not certainty, so it is a named hypothesis, not an
  axiom.
- **Status** (`Records.lean`, #118):
  - **Found:** `record!` overwrote the older copy even when the newer one
    might not be durable. After a failed sync, a write or the flush, it
    could be only in a buffer; a second `record!` then wrote over the copy
    holding the last durable record, and a crash during its sync lost both.
  - **Fixed:** `record!` syncs first whenever anything is unsynced
    (`unsynced` in `blocks.fs`).
  - **Proven, in a model of the protocol:** two copies, each durable,
    pending (written, not flushed; a crash keeps, loses or tears it) and
    buffered. Whatever writes and flushes fail, `put_keeps` and
    `crash_reads` give no garbage and durability; other tasks' evictions keep
    the invariant; `old_loses` shows the old protocol losing a record.
  - **Still to do:** link the model to the compiled `record!`, `record@` and
    block words (which needs the disk in `Machine.lean`), and the
    new-player ordering.

### V4: The network survives any input — L

The goal is one invariant: whatever arrives on the wire, in any order, and
whatever the network card writes, the network task keeps its memory intact,
keeps its pools whole and the card supplied with buffers, and is back to
polling within a bounded number of steps. Every byte from the network goes
through `eth`, `arp`, `ip`, `icmp`, `udp`, `tcp` and `telnet` (#65–73).

- **The receive ring (first, the smallest):**
  - after every frame, `virtio-net.fs` has posted a buffer back, so the card
    never runs out of places to put frames;
  - every ring index stays in range.

  The model already treats the device as unknown, so this holds even for a card
  that writes nonsense lengths. It needs the bare-metal driver in the dump: an
  extraction-only build with its registers as plain memory.
- **Reads:** for any frame of length n, a parser reads only bytes inside the
  frame and its own state. Stated as noninterference: two memories that agree
  on those bytes give the same result. Proven so far, the front
  (`proofs/OS4/Parsers.lean`, `frame_in_dispatch`): `frame-in` drops a frame
  under 14 bytes without reading it; otherwise it reads only bytes 12 and 13
  (the type), and hands ARP or IPv4 the rest of the frame with its length
  less 14, or drops it. And IP (`proofs/OS4/IpCheck.lean`,
  `ip_check_bounds`): `ip-check` accepts a packet only with
  20 ≤ ihl ≤ total ≤ len, so the payload `ip-in` hands on (`total - ihl`
  bytes at `ihl`) lies inside the frame, whatever the header claims; the
  checksum's reads are taken from its generated stack effect. UDP likewise
  (`udp_in_head`): `udp-in` goes on only with 8 ≤ ul ≤ len for the
  datagram's own length field, and works with ul from then on. TCP too
  (`tcp_in_head`): after its checksum, `tcp-in` goes on only with
  20 ≤ hlen ≤ len, and sets `i-len` to `len - hlen` and `i-data` to
  `seg + hlen`, so the segment's data lies inside it. And ICMP's reports
  (`proofs/OS4/Icmp.lean`, `unreachable_quote`, `quote_le`): a "destination
  unreachable" quotes the packet's header and 8 bytes or the whole packet,
  whichever is shorter, so never past the packet's total length (#138;
  it used to quote 8 bytes of an earlier frame, defect 24). The `hostile`
  peer already sends each of those edges (ihl 0 to 4 and 15, totals 0, 10,
  19, 200 and 65535).
- **Writes:** a parser writes only its designated buffers and connection state
  (V9's footprints).
- **Overflow:** no length or offset computation wraps into a valid-looking
  address.
- **Pools:** for connections, half-open slots and tasks, free plus live is the
  total, and every path that closes returns its slot. This is the proof
  counterpart of the `soak` peer. Proven so far (`proofs/OS4/Pools.lean`):
  `unlink`, which every closing path uses to take a connection off the live
  list, ends on any list that ends, and leaves exactly the list without
  that connection (`unlink_eq`, `unlink_chain`), provided the list's link
  cells are apart; it writes one cell, the link before the connection.
  `hash-out` takes a connection out of its hash bucket the same way, through
  each connection's hash link (`hash_out_eq`, `hunlink_chain`). And both
  pool steps keep the pool whole (`Pool`: the live and free lists end, and
  their link cells, with `conns` and `free-conns`, are pairwise apart, so no
  connection is on both lists or twice on one): `(free-conn)` moves a live
  connection to the front of the free list (`free_conn_step`), and
  `new-conn` moves the first free one to the live list (`new_conn_pool`), so
  live plus free stays what it was. Assumed there: `conn-bucket`'s own
  stores (its generated footprint: `tuple` and the SipHash state) miss the
  pool; the bucket's cells are apart from the pool's; and a connection's
  176-byte header is apart from every other link cell (records do not
  overlap). Not yet covered: `new-conn` when the free list is empty (it
  reserves a new connection), and the timers' and the application's paths
  to `free-conn`.
- **Steps:** the loops in `proofs/yields.txt` whose bound a peer sets are proven
  bounded, or made to pause: `(tcp-output)`, and `room?` (`count-list`,
  `half-open`).
- This is the proof counterpart of the `hostile` peer: the tests try many bad
  frames, and the proof covers all of them.
- **Done when:** the invariant holds for the base's protocols, as one theorem
  about any sequence of frames.
- **The HAL contract** the network stack rests on, which any driver must meet
  (`virtio-net.fs` here; an ENA driver for EC2 at milestone 12, to the same contract):
  - `net-poll ( addr -- len )` writes only the `len` bytes at `addr`, with
    `len` at most 2036 (a frame without the virtio header), and its own rings
    and buffers; it returns 0 when nothing (valid) has arrived; it never waits;
  - `net-send ( addr len -- )` sends nothing when `len` is 0 or less, and at
    most 2036 bytes otherwise; it reads only the bytes at `addr` it sends, writes only
    its own transmit buffer and ring, and either returns or throws -263 within
    `device-timeout` (5 s), pausing while it waits;
  - whatever the card writes into its rings and registers (ids, lengths, ring
    indexes), both keep to the above: a fault ends in a 0 or a caught throw,
    never in a write elsewhere or a wait without end.
- **The block contract**, likewise (`virtio-blk.fs`; NVMe on EC2 at milestone 12):
  - `blk-read ( addr u n -- )` fills the 1024 bytes at `addr` with block `u`
    of disk `n` and writes nothing else but the disk's own request header,
    status byte and ring; `blk-write ( addr u n -- )` reads only those 1024
    bytes; `blk-flush ( n -- )` returns only once the disk has made every
    completed write durable (or the disk has no write cache);
  - a disk number not below `#disks`, or a status other than success, throws
    (-33 for a read, -34 for a write or flush); a disk that does not answer
    throws -263 within `device-timeout`, pausing while it waits;
  - `blk-count` reads the size from the device: callers take it as a claim,
    and the block layer checks block numbers against it.
- **Status:** started (#132).
  - **The bare-metal drivers are in the proofs:** the bare-metal dictionary is
    dumped over the serial console (`tools/dump-virt.fs`) and `forth2lean.py
    --virt` generates the `hal/virtio*.fs` modules beside the hosted ones,
    under their own root (`OS4Virt`), which `make proofs` checks. Every value
    the device supplies is plain memory, unknown to the proofs.
  - **Generated so far:** the effects and footprints of every driver word,
    once `>phys` was modelled (#133).
    Reading the used ring (`vq-take`, `vq-wait`) writes only the queue's
    "seen" cell; the register stores (`vm!`) and the descriptor and ring
    stores say "anywhere", as their addresses are loaded from the queue's
    record or are a sum of two inputs.
  - **Proven** (`proofs/OS4/Drivers.lean`, #134): whatever id and length the
    card reports, `net-poll` either returns 0 and changes nothing (an id it
    never posted) or copies at most 2036 bytes, into the caller's buffer and
    nowhere else. Whatever length its caller asks for, `net-send` copies at
    most 2036 bytes, into its own transmit buffer and nowhere else. Writing
    this contract found two defects (21, 22 in `docs/defects.md`), and the
    test for one of them a third (23).
  - **Tested** (`tests/baremetal/net-faults`): a used-ring entry naming a
    buffer never posted, and wild ids with absurd lengths, are ignored and
    copy nothing; a device that never completes a request ends in a caught
    -263; a send longer than the buffer, or of negative length, leaves the
    memory after the buffer alone; an empty frame is not sent, as QEMU's card
    stops for good when given one (defect 23); the system and the network
    carry on.
  - **Proven, the rings:** `desc!` writes only its 16-byte descriptor;
    `vq-submit` writes only the available ring (the entry is masked into
    range, whatever index the ring holds) and the notify register; so
    `rx-post`, which hands each buffer back, writes only the receive queue's
    descriptor table and available ring and the card's register; and
    `net-send`, after its copy, writes only the transmit queue's first
    descriptor, its available ring and the register before it waits; and
    `blk-request`, for a read, a write or a flush alike, writes only the
    disk's request header and status byte, its queue's descriptor table and
    available ring, and the disk's register before it waits. These rest on
    an invariant on each queue's record (`RxQueue`, `TxQueue`, `BlkQueue`:
    the size, ring addresses and layout `new-vq` set), assumed, not yet
    proven: `new_vq_gap` shows `new-vq`'s alignment gives the gap they
    assume, and the fault tests check every queue's layout on the running
    system.
  - **Left:** proving those invariants: that `new-vq` takes that path
    (through `claim`, `,` and `allot`, which needs the kernel cells `dp`
    and `dict-owner` apart from the dictionary, today opaque), and that
    nothing else writes the records afterwards; the bound on
    `vq-wait-len`'s loop. A request that times out stays
    with the device (TD-36): only resetting the device fixes that, which is
    a feature still to decide on.
  - **Steps** (#136): `room?` pauses after each connection it counts, under
    `conns-lock`, and `(tcp-output)` sends at most 16 segments a call, so
    neither is in `proofs/yields.txt` any more and both are counted by
    `Yield.lean`. `vq-wait-len` pauses every round; that it ends rests on the
    clock passing its deadline (trusted: `counter` advances).
- **The one theorem, stated** (not yet proven; each hypothesis below names
  what is left). For the bare-metal build, take any state σ with `Inv σ` and
  any behaviour of the card (any ids, lengths and ring indexes in its used
  ring). One round of `net-loop` (`tcp-timers`, `net-poll`, `frame-in`
  under CATCH, then a pause) ends in a state σ' with `Inv σ'`; it writes only
  `W`; and it never runs more than the watchdog's allowance between pauses.
  By induction this holds after any sequence of frames.
  - `Inv`: the queue records (`RxQueue`, `TxQueue`); the pools (the live and
    free connection lists acyclic, disjoint, together every connection ever
    reserved, at most `max-conns` live and `max-half-open` half open; each
    connection in its hash bucket exactly while it is live); the ARP cache's
    index below 8; the listeners' queues hold only live connections.
  - `W`: `rx-frame`, `tx-frame`, `arp-frame`, the ARP cache, the receive and
    transmit rings and buffers, the connection records and their rings, the
    hash buckets, the listeners' queues, the network task's own variables
    and counters, and the wake flags of tasks it wakes.
  - Hypotheses, each a named gap:
    - **H-queue:** `new-vq` builds the records `RxQueue` and `TxQueue`
      describe, and nothing else writes them (Drivers.lean assumes it; the
      fault tests check it on the running system).
    - **H-parse:** `arp-in`, `ip-in`'s handlers (`icmp-in`, `udp-in`,
      `tcp-in`) and the telnet layer write only `W` and read only the frame
      and their own state. Today the generated footprints say "anywhere" for
      `arp-in`, `tcp-in`, `segment-in` and the telnet words.
    - **H-pool:** `Inv`'s pool part is kept by `tcp-in`, the timers, and the
      application side (`accept-connection`, `close-connection`,
      `release-conn`).
    - **H-steps:** the loops still in `proofs/yields.txt` end within the
      bounds their lines give (a frame, a table, a hash bucket).
    - **H-device:** after a request times out the card no longer writes its
      buffers (TD-36: only a device reset makes this true).
    - **H-model:** the primitives and the specifications of CATCH and THROW
      (TD-31), `>phys`, and a clock that advances.
  - Planning H-parse and H-pool for the receive path (2026-11-10) found five
    defects (26 to 30 in `docs/defects.md`), each with a failing test first:
    a datagram to UDP port 0 ran a free slot's handler (an unbound one, or
    xt 0); a SYN to TCP port 0 queued its connection on a free listener
    slot, never accepted, so 256 of them shut TCP for good; `ms` ended at
    any wake, so a connection's traffic cut short the pause between
    password tries; `fin-in` compared an unmasked sequence number; and
    `release-conn` could free a connection the application was already
    freeing. Proven (`proofs/OS4/Ports.lean`): `udp-find` and
    `listener-of` answer 0 for port 0 without searching, and pass any
    other port to the search; `release-conn` leaves a closed connection
    untouched (`release_conn_closed`), so the sweep's `catch` cannot free
    twice. Read and left as they are (TD-39): `close-connection`'s output
    after a wait may touch a freed record (harmless as the code stands),
    window updates without RFC 793's ordering check, challenge ACKs
    without a rate limit.
  - Proven towards it: the driver's part (`Drivers.lean`: whatever the card
    reports, `net-poll` copies at most 2036 bytes into the caller's buffer and
    hands each buffer back with stores only into its own rings); the steps
    for every word not listed in `yields.txt` (`Yield.lean`), now including
    `room?` and `(tcp-output)`; the writes of every word whose footprint is
    generated (`Foots.lean`); the parsers' front, where every length a
    header claims is checked against the frame before it is used
    (`frame_in_dispatch`, `ip_check_bounds`, `udp_in_head`, `tcp_in_head`,
    `unreachable_quote`); and both pool steps (`free_conn_step`, `new_conn_pool`: a connection
    moves between the live and free lists and their total stays the same).
  - Left for each hypothesis, most tractable first:
    - H-parse: ARP's learning writes the cache through an index read from
      memory (`arp-next`), and an address `arp-find` returns: both need
      bounds proven (drafted on branch `v4-arp`, `proofs/OS4/Arp.lean`, not
      yet checked: it did not finish in the time Lean was given).
      `arp-reply`'s generated footprint is already bounded.
      `tcp-in`'s handling (`segment-in`, `data-in`) writes connection
      records found through the hash table, so its footprint rests on the
      pool invariant, now proven for the pool steps: what is left is that
      `find-conn` returns a live connection or 0. Telnet works on a
      connection's receive ring, through masked offsets.
    - H-pool: `new-conn` when it reserves a new connection; the records
      apart from each other and from the hash cells (stated as hypotheses
      of the pool steps); and the paths to `free-conn` (`release-conn`, the
      timers, `close-connection`) shown to pass a live connection. Stated
      and read against the code (2026-11-10), not yet proven: a connection
      is freed only by `close-connection` finding it closed, or by
      `release-conn` closing it after the application has closed it (or it
      never reached one, in the handshake); `release-conn` on a closed one
      is proven to do nothing; the listeners' queues hold only connections
      on a port someone listens on (port 0 never, proven for
      `listener-of`).
    - H-steps: the remaining listed loops each need a bound from the code
      above them (a frame's length, a table's size, an acyclic bucket),
      or to pause. Proven in the plain semantics, not yet in the counted
      one: `unlink` and `hash-out` end on any list that ends (`unlink_eq`,
      `hash_out_eq`).
    - H-queue: needs the kernel's `dp` and `dict-owner` cells stated apart
      from the dictionary (a small trusted hypothesis), then `new-vq`.
    - H-device: a device reset after a timeout (TD-36, the user's call).
    - H-model: V5 (the primitives against the assembly).

### V5: Primitives against the assembly — L

This removes the largest trusted piece, the primitive models.

- **Model:** the roughly 25 AArch64 instructions that `prims.s` uses, in Lean.
  An alternative is AWS's LNSym, built to verify Graviton code.
- **Extraction:** instructions come from the assembled `kernel.o` (objdump), as
  the dumper does for threads.
- **Proof per primitive:** under the register mapping (`x20` DSP, `x22` TOS,
  `x21` RSP, `x23` UP), running its instructions refines its `Machine.lean`
  model.
- **Hard parts:**
  - `um/mod`'s loop;
  - the data stack being memory on the real machine but a list in the model;
  - `sha256-block`, which is left to V8.
- **Done when:** every primitive the model uses is proven, except the SHA-256
  pair.

### V6: Tasks and semaphores — L

- **Model:** several tasks, interleaved only at `pause`, which is what
  cooperative scheduling guarantees.
- **Properties:**
  - **Mutual exclusion:** two tasks are never both inside `locked` on the
    same semaphore.
  - **Release:** `locked` always releases, which extends the single-task proof
    in `Semaphores.lean` (`locked_releases`).
  - **Lock discipline:** every word that sends a frame holds `tx-lock`, every
    block word holds `blocks-lock`, and `free-conn` holds `conns-lock`
    (#76–78, #109). This is checked statically over the call graph.
  - **A stopped task leaves nothing broken (before players):** when a session
    is stopped at any point, by the watchdog, a dropped connection or an
    error, it holds no semaphore and no dictionary claim, its connection is
    closed, and its task goes back to the pool. Phase 2 needs this one; the
    rest of V6 can wait.
  - **Status** (`Semaphores.lean`, #116; `Sessions.lean`, #117):
    - **Found:** the watchdog fires at any instruction outside `pause`. A task
      stopped inside `get`, or in LOCKED before its `catch`, kept the semaphore
      for good. And a throw caught near the end of the allowance left its
      catcher a few ticks to clean up; a second -262 there escaped every
      catch, and ABORT ran a REPL in the worker. And `session` set up the
      telnet terminal before its `catch`: if the client had already reset the
      connection, that send threw -269 past the cleanup, so the door kept the
      place and the connection was never freed.
    - **Fixed:** every semaphore is on a chain, and `release-all` frees those
      the task holds, run by `retire` (the end of `run-task`), `reset` and
      `restarting`. A caught throw restarts the watchdog's count. A throw
      nothing catches retires any task but the console. `session` sets the
      terminal up inside its `catch`, and gives the door's place back itself.
    - **Proven:** `release_all`, that `release-all` clears exactly the
      semaphores on the chain this task holds and writes nothing else (given
      the chain's semaphores do not overlap); `unclaim_frees`;
      `locked_releases`; and `cleanup_wired`, that `retire`, `run-task`,
      `(quit)`, `reset` and `restarting` call them. `session_closes`: whatever
      the session's work does, returning or throwing, `session` comes to
      `close-connection` with the connection, the caller's return stack and
      the door's count one less (given the work leaves the count alone).
    - **Still to do:** that `close-connection` itself finishes; and the
      cleanup's steps bounded, so its fresh allowance is proven enough rather than
      argued (the chain holds a handful of semaphores, made at boot).
- **Watchdog (done for the system tasks; DECISIONS.md #108):** a task that pauses
  within bounded steps is never stopped (#48–56).
  - `Yield.lean` counts a run in Forth instructions: each thread cell spends one
    step of an allowance, and `pause` refills it. `Cost f n m p` bounds a word's
    steps before its first pause (n) and between or after pauses (m).
  - Costs are proven compositionally, by a certificate per word and the bridge
    `threadT_cost`, like stack effects.
  - Proven: `net-loop` takes at most 3389 steps between pauses, `serve-door` 1010,
    however many connections there are. Two changes made this true:
    - `serve-door` pauses after each connection;
    - the TCP timer sweep pauses after each connection (#109). It used to
      retransmit to all 256 in one stretch.
  - Not counted, each listed in `proofs/yields.txt` with its bound: loops that
    never pause. Most walk the connection list or copy a frame a byte at a time.
    The largest are `(tcp-output)`, up to 128 segments to a peer that claims a
    64-byte MSS, and `count-list` and `half-open`, a walk over every connection
    for each SYN.
  - **Still to do:** prove those bounds. Each needs its input bounded by the
    code above it: a frame's length, a list without a cycle, the pool's size.
    Then turn the step count into time on the slowest platform, which is an
    argument rather than a theorem.

### V7: TCP state machine — XL

`tcp.fs` is the largest file in the base.

- **Invariants:** from any well-formed connection state, any segment, timeout
  or call leaves it well-formed. Well-formed means sequence numbers ordered as
  RFC 9293 requires, buffer indices in bounds, timers consistent.
- **Off-path attacks:** a forged segment from an off-path attacker cannot reset
  or desynchronise a connection without guessing its sequence numbers. This is
  the counterpart of `tcp-attack`. Pool invariants are in V4.

### V8: Cryptography — XL

- **SHA-256:** `sha256-block`, through V5's instruction model, equals
  FIPS 180-4.
- **HMAC and PBKDF2:** equal their RFC definitions.
- **SipHash:** equals its reference.
- **Passwords:** `password?` accepts exactly the passwords whose
  `hash-password` hash is stored.
- **Leverage:** LNSym's SHA work is the precedent here.

### V9: Footprints — M

What a word may read and write, proven compositionally like stack effects and
step counts. V2, V4 and V6 all depend on it.

- **Statement:**
  - **writes:** every address outside the word's footprint keeps its value;
  - **reads:** two memories that agree on its read set give the same result.

  A footprint is described in terms the word can name: its user area, its
  task's buffers, fixed buffers (`rx-frame`, `tx-frame`), and a range given by
  its arguments (a frame of length n).
- **Certificates:** the generator infers each word's footprint, and a bridge
  theorem checks it against its callees' footprints. Words that write through a
  computed address (`buf + i` in a loop) need a bound: the reference-word proofs
  (`cmove-ref`, `fill-ref`) are the pattern.
- **Done when:** `fill`, `cmove` and the stack and arithmetic words have footprints,
  and the bridge proves them for colon words. Then V2 and V4 build on it.
- **Status:** writes done (#111): every primitive's footprint, `thread_foot`
  and `loopThread_foot`, and 903 words' footprints generated and proven.
  Still to do: reads (noninterference); letting callers use a hand-written
  footprint such as `fill-ref`'s in place of the generated one; and
  addresses read from memory, such as a connection's buffer, which need an
  invariant about what that memory holds.

### V10: Proofs for an app — M

An app is verified as the base is, in its own repository, against a tagged
`os4` image.

- **Extraction:** `os4-app` dumps the dictionary with the app loaded, and the
  generator models the app's words over the base's theorems.
- **Yields:** the app's tasks and door handlers are roots in its own
  `yields.txt`.
- **Sandbox:** the app's player-facing commands keep V2's isolation. For the
  MUD, a player's command reaches only that player's own state and the shared
  world through the words meant for it.
- **Done when:** `os4-app proofs` runs an app's proofs, and the MUD's pass.

## Not planned

- **End-to-end correctness of the whole OS:** seL4 scale; not worth it.
- **Device behaviour:** virtio devices and QEMU themselves stay trusted. Our
  drivers are proven safe whatever the device does (V4); the device itself is
  not proven.
- **The memory model:** proofs assume program order. The `dmb` and `dsb`
  barriers are what make that true on real hardware, and they stay trusted.
- **Timing:** constant-time cryptography and performance are out of scope for
  Lean. They need different tools.

## Risks

- **Proof upkeep:** every change to a proven area may need its proof touched.
  Keep proofs behavioural, mostly automatic, and modular (a word's proof uses
  its callees' theorems, not their code).
- **Lean versions:** pin the toolchain, and upgrade deliberately, as a change
  of its own.
- **Build time:** seconds with nothing changed, about a minute after a change
  to a late boot file, but eight or nine minutes after a change to `core.fs`
  or the model (TD-30). Until a typical change re-proves in a minute or two,
  the proofs are a gate of their own: `make proofs`, run at each milestone.
- **Model drift:** each new kind of proof adds generated semantics beside the
  plain one (step counts now). Footprints are proven over the plain one (#111). Proving them equal is cheaper
  while there are few, so do it as part of V9.
