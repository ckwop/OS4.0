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
| Colon words modelled | 525 of 577 |
| Not modelled | The compiler and interpreter primitives (`,`, `parse`, `parse-name`, `search-list` ...) and the words that use them |
| Model covers | Stacks, byte memory, loops, DOES> children, strings, CATCH/THROW/EXECUTE, PAUSE and the outside world as unknown |
| Proven | 651 stack effects and 264 stack comments; the arithmetic and stack words for all inputs; `fill-ref` equal to `fill`; the system tasks' steps between pauses |
| Found | A listener and the TCP timer sweep that could run without pausing, both fixed (#108, #109) |
| Shown to catch | A signed `u>` that passes all 36 hosted tests fails its proof |

Three kinds of compositional proof now exist, all built the same way. The
generator infers a certificate, Lean checks it by `decide`, and one bridge
theorem, proven once, turns the certificate and the callees' theorems into
the word's own theorem:

- **Stack effects** (`Spec.lean`, #107);
- **step counts between pauses** (`Yield.lean`, #108);
- **footprints**, next: what a word may read and write (V9).

Stack effects in detail (DECISIONS.md #107):

- **651 effects proven:** every word with a fixed effect, loops included. Each is proven from a certificate and from its callees' theorems. 525 of 577 colon words are modelled, since the generator decodes `(s")` (now a colon word) and stops at the data a `message:` leaves after a word.
- **264 stack comments proven in their own terms:** none disagree with their code.
- **What is still missing a proven effect:**
  - words whose effect depends on their data (`?dup`, `digit?`, `get-order`);
  - words that reach their callees through `execute` or `catch` (`type`, `emit`, `locked`);
  - every word that calls one of those.

Trusted today:

- **The primitive models:** each is written to mirror its assembly.
- **The CATCH and THROW specifications.**
- **The dumper and the generator.**
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
| | V9: footprints, what a word may read and write | M | V2, V4 and V6 all need it. |
| | V1: models of the interpreter primitives, and `search-list-ref` | S | V2 needs `interpret` modelled. |
| | Course: a lecture and tour on the proofs | S | Explains the approach once, while it has three kinds of proof: the model, certificates and bridges, stack effects, step counts, and what they found. |
| 2. Before players | V2: sandbox isolation | M | The brief's hard rule, and what every player reaches. |
| | V6: a stopped task leaves nothing broken | M | A player can make the watchdog fire, or drop the connection, at any point. |
| | V10: proofs for an app (the MUD first) | M | The MUD's own tasks and commands, on the base's results. |
| | V3: crash-safe records | M | Player data survives a crash at any point. |
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
  - The coverage check described above.
- **Stack comments:** every plain stack comment proven, including words with
  loops. The work left:
  - teach the checker the `?dup if` idiom and branches that end in a THROW;
  - state effects for vectored words (`type`, `key`, `emit`) as hypotheses about their vectors;
  - get the proof build fast enough for every `make test`. It is now
    incremental (#110): seconds unchanged, about a minute for a late boot
    file, eight minutes for `core.fs`; the certificates are the cost left.
- **Reference definitions:** each one proven equal to its primitive's model.
  These are `fill-ref`, `cmove-ref`, `cmove>-ref`, `pick-ref`, `um/mod-ref` and
  `search-list-ref`. Together they give the brief's "keep the Forth definition
  as the reference" a check.
- **TD-13 (stack overflow between checks):** replace the acceptance with a
  check. A static pass over every thread shows that no straight run pushes more
  than the 16 cells of headroom without a call, branch or loop in between.
- **Done when:** proofs run in `make test`; the coverage numbers are recorded
  and checked; every reference word is proven.

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
  on those bytes give the same result.
- **Writes:** a parser writes only its designated buffers and connection state
  (V9's footprints).
- **Overflow:** no length or offset computation wraps into a valid-looking
  address.
- **Pools:** for connections, half-open slots and tasks, free plus live is the
  total, and every path that closes returns its slot. This is the proof
  counterpart of the `soak` peer.
- **Steps:** the loops in `proofs/yields.txt` whose bound a peer sets are proven
  bounded, or made to pause: `(tcp-output)`, and `room?` (`count-list`,
  `half-open`).
- This is the proof counterpart of the `hostile` peer: the tests try many bad
  frames, and the proof covers all of them.
- **Done when:** the invariant holds for the base's protocols, as one theorem
  about any sequence of frames.

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
    drafted in `Semaphores.lean`.
  - **Lock discipline:** every word that sends a frame holds `tx-lock`, every
    block word holds `blocks-lock`, and `free-conn` holds `conns-lock`
    (#76–78, #109). This is checked statically over the call graph.
  - **A stopped task leaves nothing broken (before players):** when a session
    is stopped at any point, by the watchdog, a dropped connection or an
    error, it holds no semaphore and no dictionary claim, its connection is
    closed, and its task goes back to the pool. Phase 2 needs this one; the
    rest of V6 can wait.
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
- **Build time:** about fifteen minutes under emulation, and nearly as long
  after a Forth change (TD-30). Until a typical change re-proves in a minute or
  two, the proofs are a gate of their own: `make proofs`, run at each
  milestone. Phase 1 fixes this first.
- **Model drift:** each new kind of proof adds generated semantics beside the
  plain one (step counts now, footprints next). Proving them equal is cheaper
  while there are few, so do it as part of V9.
