import OS4.Attr

/-!
# The Forth machine

An abstract model of the OS 4.0 inner interpreter: what the kernel's primitives
(`arch/aarch64/prims.s`) do to the stacks, and how a colon definition's thread
runs. Generated words (`OS4.Words`) are threads over these primitives.

This model is trusted, not proven: each primitive is written to mirror its
assembly, instruction by instruction where arithmetic is involved.

Abstractions, which the proofs inherit:
* The data stack is a list whose head is TOS (`x22`). Running out of items is
  an `underflow` error; the real machine checks only at colon calls, branches
  and loops, so theorems are stated for stacks deep enough.
* The return stack holds only what words push with `>r`. Colon calls do not
  push a return address, so words that reach below their own frame on the
  return stack (`(s")`, `catch`, `throw`) cannot be modelled this way.
* There is no memory yet: `@`, `!` and variables are `unmodelled`.
-/

namespace OS4

abbrev Cell := BitVec 64

structure S where
  ds : List Cell
  rs : List Cell
deriving DecidableEq, Repr

inductive Err where
  | underflow | rUnderflow | divZero | fuel | badBranch
  | unmodelled (name : String)
deriving DecidableEq, Repr

/-- What a word does: a new state, or an error. -/
abbrev Sem := S → Except Err S

/-- One cell of a thread, already decoded by tools/forth2lean.py. Branch
targets are cell indexes into the thread. -/
inductive Ins where
  | call (f : Sem)
  | lit (v : Cell)
  | branch (t : Nat)
  | zbranch (t : Nat)
  | exit

/-- Run a thread from cell `pc`, for at most `fuel` steps. -/
@[forth] def run (code : List Ins) : Nat → Nat → S → Except Err S
  | 0, _, _ => .error .fuel
  | n + 1, pc, s =>
    match code[pc]? with
    | none => .error .badBranch
    | some .exit => .ok s
    | some (.call f) =>
      match f s with
      | .ok s' => run code n (pc + 1) s'
      | .error e => .error e
    | some (.lit v) => run code n (pc + 1) { s with ds := v :: s.ds }
    | some (.branch t) => run code n t s
    | some (.zbranch t) =>
      match s.ds with
      | [] => .error .underflow
      | x :: ds => if x = 0 then run code n t { s with ds := ds }
                   else run code n (pc + 1) { s with ds := ds }

/-- A colon definition. The generator emits only threads whose branches all go
forwards, so each cell runs at most once and the thread's length is fuel
enough. -/
@[forth] def thread (code : List Ins) : Sem := fun s => run code code.length 0 s

@[forth] def pushConst (v : Cell) : Sem := fun s => .ok { s with ds := v :: s.ds }
@[forth] def unmodelled (name : String) : Sem := fun _ => .error (.unmodelled name)

/-- A Forth flag: all bits set for true. -/
@[forth] def flag (b : Bool) : Cell := if b then -1 else 0

namespace Prim

@[forth] def dup : Sem
  | ⟨x :: s, r⟩ => .ok ⟨x :: x :: s, r⟩
  | _ => .error .underflow
@[forth] def drop : Sem
  | ⟨_ :: s, r⟩ => .ok ⟨s, r⟩
  | _ => .error .underflow
@[forth] def swap : Sem
  | ⟨b :: a :: s, r⟩ => .ok ⟨a :: b :: s, r⟩
  | _ => .error .underflow
@[forth] def over : Sem
  | ⟨b :: a :: s, r⟩ => .ok ⟨a :: b :: a :: s, r⟩
  | _ => .error .underflow
@[forth] def tor : Sem
  | ⟨x :: s, r⟩ => .ok ⟨s, x :: r⟩
  | _ => .error .underflow
@[forth] def rfrom : Sem
  | ⟨s, x :: r⟩ => .ok ⟨x :: s, r⟩
  | _ => .error .rUnderflow
@[forth] def rfetch : Sem
  | ⟨s, x :: r⟩ => .ok ⟨x :: s, x :: r⟩
  | _ => .error .rUnderflow
/-- `ldr TOS, [DSP, TOS, lsl #3]`: the u-th item below u itself. -/
@[forth] def pick : Sem
  | ⟨u :: s, r⟩ => match s[u.toNat]? with
    | some x => .ok ⟨x :: s, r⟩
    | none => .error .underflow
  | _ => .error .underflow

/-- A primitive ( a b -- f a b ). -/
@[forth] def bin (f : Cell → Cell → Cell) : Sem
  | ⟨b :: a :: s, r⟩ => .ok ⟨f a b :: s, r⟩
  | _ => .error .underflow
/-- A primitive ( a -- f a ). -/
@[forth] def un (f : Cell → Cell) : Sem
  | ⟨a :: s, r⟩ => .ok ⟨f a :: s, r⟩
  | _ => .error .underflow

@[forth] def plus   : Sem := bin (· + ·)
@[forth] def minus  : Sem := bin (· - ·)
@[forth] def star   : Sem := bin (· * ·)
@[forth] def and    : Sem := bin (· &&& ·)
@[forth] def or     : Sem := bin (· ||| ·)
@[forth] def xor    : Sem := bin (· ^^^ ·)
@[forth] def invert : Sem := un (~~~ ·)
/-- `lsl`/`lsr` by a register use the shift amount modulo 64. -/
@[forth] def lshift : Sem := bin fun a b => a <<< (b.toNat % 64)
@[forth] def rshift : Sem := bin fun a b => a >>> (b.toNat % 64)
@[forth] def equal  : Sem := bin fun a b => flag (a == b)
@[forth] def less   : Sem := bin fun a b => flag (a.slt b)
@[forth] def uless  : Sem := bin fun a b => flag (a.ult b)
@[forth] def zequal : Sem := un fun a => flag (a == 0)
/-- `asr TOS, TOS, #63`. -/
@[forth] def zless  : Sem := un fun a => a.sshiftRight 63

/-- `/mod` ( n d -- rem quot ): `sdiv` truncates, then if the remainder is
nonzero and its sign differs from the divisor's, step down to floored. -/
@[forth] def slashmod : Sem
  | ⟨d :: n :: s, r⟩ =>
    if d = 0 then .error .divZero else
    let q := n.sdiv d
    let m := n - q * d
    if m ≠ 0 ∧ (m ^^^ d).msb then .ok ⟨(q - 1) :: (m + d) :: s, r⟩
    else .ok ⟨q :: m :: s, r⟩
  | _ => .error .underflow

end Prim

/-- Unfold words and primitives and run them symbolically. -/
macro "forth_run" : tactic => `(tactic| simp_all [forth])

/-- Run symbolically, split every branch taken, and settle each case as a
bit-vector problem (SAT, by `bv_decide`). -/
macro "forth_auto" : tactic =>
  `(tactic| (forth_run <;> (repeat' split) <;> (try simp_all) <;> bv_decide))

end OS4
