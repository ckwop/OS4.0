# Proofs (spike)

Lean 4 proofs about the Forth words as the system actually compiles them.

```
docker build -t os4-lean proofs                                     # once
docker run --rm -v "${PWD}:/src" os4 make proofs-extract           # dump and generate
docker run --rm -v "${PWD}:/src" -w /src/proofs os4-lean lake build
```

## Pipeline

1. `make proofs-extract` boots the hosted build, which loads every boot file,
   and feeds it `tools/dump-words.fs`. That prints each word's kind and raw
   thread cells, bounded by the next header, so the Forth side decodes nothing.
2. `tools/forth2lean.py` decodes the threads (`lit`, `branch`, `0branch`,
   calls), takes the words in `roots.txt` and everything they call, and writes
   `OS4/Words.lean` (generated, not committed). It fails on anything it cannot
   represent: unknown operands, loops, recursion, a truncated dump.
3. `OS4/Machine.lean` is the trusted model: the stacks, the thread interpreter
   and the primitives, written to mirror `prims.s`.
4. `OS4/Core.lean` states each word's stack effect as a theorem over all
   inputs. Most are proven by `forth_run` (symbolic execution by `simp`), and
   words with branches by `forth_auto` (split cases, then `bv_decide`).

## What the spike showed

- 29 `core.fs` words proven, in about 40 s, including `within` (the unsigned
  trick equals lo ≤ n < hi when lo ≤ hi), `abs`, `min` and `max`.
- Changing `u>` to use signed `<` passes all 36 hosted tests but fails its
  proof. Refactoring `nip` to `>r drop r>` re-proves untouched.
- `INT_MIN -1 /` gives `INT_MIN`: the standard's ambiguous case, now pinned.

## Limits

Each of these is a next step:

- No memory (`@`, `!`, variables).
- No loops.
- No `does>`, `(s")`, or words that reach below their own return-stack frame.
- The primitives are trusted, not proven against `prims.s`.
