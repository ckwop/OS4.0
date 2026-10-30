# Proofs

Lean 4 proofs about the Forth words as the system actually compiles them. The
plan and the state of each milestone are in [docs/verification.md](../docs/verification.md);
lecture 12 of the course ([docs/course](../docs/course/index.html)) walks
through how it all works, with an example of each kind of proof.

```
docker run --rm -v "${PWD}:/src" -v os4-lake:/src/proofs/.lake os4 make proofs
```

Keep Lake's build on the `os4-lake` volume: the working copy is under OneDrive.

## Pipeline

1. `tools/dump-words.fs`, fed to the hosted build, prints every word as
   compiled (`build/words.txt`).
2. `tools/forth2lean.py` decodes the threads and writes, a module per boot
   file (generated, not committed): `OS4/Words/` the words' definitions,
   `OS4/Specs/` their stack effects, `OS4/Foots/` their footprints, and
   `OS4/Costs/` the system tasks' step counts. Its reports go in `build/`:
   `proof-findings.txt`, `footprints.txt` and `yields.txt`.
3. `lake build` checks every theorem, re-proving only what changed.

## Files

- `OS4/Machine.lean`: the model, trusted: the machine state, the primitives
  (each mirroring its assembly) and how a thread runs. Its header lists what
  is assumed.
- `OS4/Spec.lean`, `OS4/PrimSpecs.lean`: stack effects, their certificate
  checker and bridge, and the primitives' effects (DECISIONS.md #107).
- `OS4/Footprint.lean`, `OS4/FootPrims.lean`: what a word may write (#111).
- `OS4/Yield.lean`: steps between pauses (#108); `yields.txt` configures it.
- `OS4/Core.lean`, `OS4/Refs.lean`, `OS4/Memory.lean`, `OS4/Loops.lean`,
  `OS4/Semaphores.lean`: hand-written theorems.
- `roots.txt`: words the proofs need, which must stay modelled.

Hand-written theorems never use `sorry`, and use the generated `.spec` and
`.foot` theorems rather than unfolding callees.
