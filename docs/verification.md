# Verification plan

How we use Lean to certify properties of the OS 4.0 base, milestone by
milestone. This is the second track beside the MUD: it strengthens the base,
and it runs in this repository because the proofs are about this code.

## The approach

Proofs are about the system as it is compiled, never about a copy of it.

1. `make proofs-extract` boots the hosted build, which loads every boot file,
   and dumps each word's compiled thread (`tools/dump-words.fs`).
2. `tools/forth2lean.py` turns the threads into Lean definitions
   (`proofs/OS4/Words.lean`, generated) and each plain stack comment into a
   theorem (`proofs/OS4/Effects.lean`, generated).
3. `proofs/OS4/Machine.lean` models what the primitives do. It is the trusted
   base, and every milestone below either uses it or shrinks it.
4. Hand-written theorems (`proofs/OS4/*.lean`) state the properties that
   matter. `lake build` checks them all.

Change a word's Forth, and its generated definition changes with it. A theorem
that no longer holds fails the build, as a test would.

## Where the spike left us (V0)

| | |
| --- | --- |
| Colon words modelled | 472 of 575 (82%) |
| Not modelled | The compiler (`,`, `parse`, `search-list` ...) and some threads with inline data |
| Model covers | Stacks, byte memory, loops, DOES> children, strings, CATCH/THROW/EXECUTE, PAUSE and the outside world as unknown |
| Proven | `within`, `abs`, `min`, `max` and the core stack words for all inputs; `/` on its ambiguous case; reading a cell back after a store |
| Shown to catch | A signed `u>` that passes all 36 hosted tests fails its proof |

V1 has started. Stack effects are now proven compositionally (DECISIONS.md #107):

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

## Milestones

The order puts first what the OS needs soonest. V4 and V5 are what face the
internet, and they should be done before milestone 11 (Fargate). Effort is
relative: S is a session or two, XL is many.

### V1: Proofs in the suite — S

- **Proofs in the build:**
  - Lean in the `os4` image, or a tagged `os4-lean` image built with it.
  - `make proofs` added to `make test`.
  - The coverage check described above.
- **Stack comments:** every plain stack comment proven, including words with
  loops. The work left:
  - teach the checker the `?dup if` idiom and branches that end in a THROW;
  - state effects for vectored words (`type`, `key`, `emit`) as hypotheses about their vectors;
  - get the proof build fast enough for every `make test`.
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

### V4: Parser safety — L

Every byte from the network goes through `eth`, `arp`, `ip`, `icmp`, `udp`,
`tcp` and `telnet` (#65–73).

- **Reads:** for any frame of length n, a parser reads only bytes inside the
  frame and its own state. Stated as noninterference: two memories that agree
  on those bytes give the same result.
- **Writes:** a parser writes only its designated buffers and connection state.
- **Overflow:** no length or offset computation wraps into a valid-looking
  address.
- This is the proof counterpart of the `hostile` peer: the tests try many bad
  frames, and the proof covers all of them.
- **Done before milestone 11.**

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
  - **Lock discipline:** every word that sends a frame holds `tx-lock`, and
    every block word holds `blocks-lock` (#76–78). This is checked statically
    over the call graph.
- **Watchdog (done for the system tasks; DECISIONS.md #108):** a task that pauses
  within bounded steps is never stopped (#48–56).
  - `Yield.lean` counts a run in Forth instructions: each thread cell spends one
    step of an allowance, and `pause` refills it. `Cost f n m p` bounds a word's
    steps before its first pause (n) and between or after pauses (m).
  - Costs are proven compositionally, by a certificate per word and the bridge
    `threadT_cost`, like stack effects.
  - Proven: `net-loop` takes at most 2380 steps between pauses, `serve-door` 937.
    `serve-door` gained a `pause` after each connection to make this true.
  - Not counted, each listed in `proofs/yields.txt` with its bound: loops that
    never pause. Most walk the connection list or copy a frame a byte at a time.
    The largest is `tcp-timers`, a round per connection (up to 256), each of
    which may retransmit a segment.
  - **Still to do:** prove those bounds. Each needs its input bounded by the
    code above it: a frame's length, a list without a cycle, the pool's size.
    Then turn the step count into time on the slowest platform, which is an
    argument rather than a theorem.

### V7: TCP state machine — XL

`tcp.fs` is the largest file in the base.

- **Invariants:** from any well-formed connection state, any segment, timeout
  or call leaves it well-formed. Well-formed means sequence numbers ordered as
  RFC 9293 requires, buffer indices in bounds, timers consistent.
- **Resources:**
  - every path that closes a connection returns it to its pool, which is the
    proof counterpart of the `soak` peer;
  - a forged segment from an off-path attacker cannot reset or desynchronise
    a connection without guessing its sequence numbers, which is the
    counterpart of `tcp-attack`.

### V8: Cryptography — XL

- **SHA-256:** `sha256-block`, through V5's instruction model, equals
  FIPS 180-4.
- **HMAC and PBKDF2:** equal their RFC definitions.
- **SipHash:** equals its reference.
- **Passwords:** `password?` accepts exactly the passwords whose
  `hash-password` hash is stored.
- **Leverage:** LNSym's SHA work is the precedent here.

## Not planned

- **End-to-end correctness of the whole OS:** seL4 scale; not worth it.
- **Device behaviour:** virtio devices and QEMU itself stay trusted.
- **Timing:** constant-time cryptography and performance are out of scope for
  Lean. They need different tools.

## Risks

- **Proof upkeep:** every change to a proven area may need its proof touched.
  Keep proofs behavioural, mostly automatic, and modular (a word's proof uses
  its callees' theorems, not their code).
- **Lean versions:** pin the toolchain, and upgrade deliberately, as a change
  of its own.
- **Build time:** about twenty minutes from clean under emulation, and nearly
  as long after a Forth change (TD-30). Until that is under a minute, the
  proofs are a gate of their own: `make proofs`, run at each milestone.
