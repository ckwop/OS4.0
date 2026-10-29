import OS4.Attr

/-!
# The Forth machine

An abstract model of the OS 4.0 inner interpreter: what the kernel's primitives
(`arch/aarch64/prims.s`) do to the machine, and how a colon definition's thread
runs. Generated words (`OS4.Words`) are threads over these primitives.

This model is trusted, not proven: each primitive is written to mirror its
assembly, instruction by instruction where arithmetic is involved.

Abstractions, which the proofs inherit:
* The data stack is a list whose head is TOS (`x22`). Running out of items is
  an `underflow` error; the real machine checks only at colon calls, branches
  and loops, so theorems are stated for stacks deep enough.
* The return stack holds only what words push with `>r` and loops. Colon
  calls do not push a return address, so words that reach below their own
  frame on the return stack (`catch`, `throw`) cannot be modelled this way.
  `(s")` is decoded by the generator into the two literals it pushes.
* Memory is bytes, little endian, at 64-bit addresses, all of it readable and
  writable. The data and return stacks are not in it, so `sp@` and `rp@`
  are not modelled.
* Kernel words that push an address or value (`dp`, `base`, `handler`,
  `docol` ...) push `kval name s`, an unknown that may depend on the state.
-/

namespace OS4

abbrev Cell := BitVec 64
abbrev Mem := Cell → BitVec 8

structure S where
  ds  : List Cell
  rs  : List Cell
  mem : Mem
  up  : Cell                    -- the current task's user area (x23)

inductive Err where
  | underflow | rUnderflow | divZero | outOfRange | fuel | badBranch
  | throw (n : Cell)
deriving DecidableEq, Repr

/-- What a word does: a new state, or an error. -/
abbrev Sem := S → Except Err S

/-! ## Memory -/

/-- Store one byte. -/
@[forth] def upd (m : Mem) (a : Cell) (b : BitVec 8) : Mem := fun x => if x = a then b else m x

/-- Read n bytes from a, little endian. -/
@[forth] def rd (m : Mem) (a : Cell) : Nat → Cell
  | 0 => 0
  | n + 1 => (m a).setWidth 64 ||| (rd m (a + 1) n <<< 8)

/-- Write the low n bytes of v at a, little endian. -/
@[forth] def wr (m : Mem) (a : Cell) : Nat → Cell → Mem
  | 0, _ => m
  | n + 1, v => wr (upd m a (v.setWidth 8)) (a + 1) n (v >>> 8)

/-! ## Threads -/

/-- One cell of a thread, already decoded by tools/forth2lean.py. Targets are
indexes of instructions in the thread. -/
inductive Ins where
  | call (f : Sem)
  | lit (v : Cell)
  | branch (t : Nat)
  | zbranch (t : Nat)
  | qdo (t : Nat)             -- (?do): skip to t if limit = start
  | loop (t : Nat)            -- (loop): back to t unless done
  | ploop (t : Nat)           -- (+loop)
  | exit

/-- Run a thread from pc, for at most `fuel` steps. Each branch is an `if`
around the recursive calls, which symbolic execution by `simp` handles well. -/
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
      | x :: ds => if x = 0 then run code n t { s with ds := ds }
                   else run code n (pc + 1) { s with ds := ds }
      | [] => .error .underflow
    | some (.qdo t) =>
      match s.ds with
      | start :: limit :: ds =>
        if limit = start then run code n t { s with ds := ds }
        else run code n (pc + 1) { s with ds := ds, rs := start :: limit :: s.rs }
      | _ => .error .underflow
    | some (.loop t) =>
      match s.rs with
      | i :: l :: rs =>
        if i + 1 = l then run code n (pc + 1) { s with rs := rs }
        else run code n t { s with rs := (i + 1) :: l :: rs }
      | _ => .error .rUnderflow
    | some (.ploop t) =>
      match s.ds, s.rs with
      | k :: ds, i :: l :: rs =>
        -- ends when i - l and i + k - l differ in sign, not by overflow
        let d := i - l
        if ((d ^^^ (d + k)) &&& (d ^^^ k)).msb then run code n (pc + 1) { s with ds := ds, rs := rs }
        else run code n t { s with ds := ds, rs := (i + k) :: l :: rs }
      | [], _ => .error .underflow
      | _, _ => .error .rUnderflow

/-- A colon definition whose branches all go forwards: each cell runs at most
once, so the thread's length is fuel enough. -/
@[forth] def thread (code : List Ins) : Sem := fun s => run code code.length 0 s

/-- A colon definition with loops: its result if it ends, else `fuel`. More
fuel never changes a result that is not `fuel` (`run_mono`), so any fuel that
suffices gives the same answer. -/
noncomputable def loopThread (code : List Ins) : Sem := fun s =>
  open Classical in
  if h : ∃ n, run code n 0 s ≠ .error .fuel then run code (Classical.choose h) 0 s
  else .error .fuel

/-- A DOES> child: push its body, then run the DOES> code. -/
@[forth] def doesChild (body : Cell) (code : Sem) : Sem := fun s => code { s with ds := body :: s.ds }

@[forth] def pushConst (v : Cell) : Sem := fun s => .ok { s with ds := v :: s.ds }

/-- What a kernel constant or user variable pushes: unknown here. -/
opaque kval : String → S → Cell
@[forth] def kconst (name : String) : Sem := fun s => .ok { s with ds := kval name s :: s.ds }

/-- A Forth flag: all bits set for true. -/
@[forth] def flag (b : Bool) : Cell := if b then -1 else 0

/-! ## Primitives -/

namespace Prim

@[forth] def dup : Sem
  | ⟨x :: s, r, m, u⟩ => .ok ⟨x :: x :: s, r, m, u⟩
  | _ => .error .underflow
@[forth] def drop : Sem
  | ⟨_ :: s, r, m, u⟩ => .ok ⟨s, r, m, u⟩
  | _ => .error .underflow
@[forth] def swap : Sem
  | ⟨b :: a :: s, r, m, u⟩ => .ok ⟨a :: b :: s, r, m, u⟩
  | _ => .error .underflow
@[forth] def over : Sem
  | ⟨b :: a :: s, r, m, u⟩ => .ok ⟨a :: b :: a :: s, r, m, u⟩
  | _ => .error .underflow
@[forth] def tor : Sem
  | ⟨x :: s, r, m, u⟩ => .ok ⟨s, x :: r, m, u⟩
  | _ => .error .underflow
@[forth] def rfrom : Sem
  | ⟨s, x :: r, m, u⟩ => .ok ⟨x :: s, r, m, u⟩
  | _ => .error .rUnderflow
@[forth] def rfetch : Sem
  | ⟨s, x :: r, m, u⟩ => .ok ⟨x :: s, x :: r, m, u⟩
  | _ => .error .rUnderflow
/-- `ldr TOS, [DSP, TOS, lsl #3]`: the u-th item below u itself. -/
@[forth] def pick : Sem
  | ⟨u :: s, r, m, p⟩ => match s[u.toNat]? with
    | some x => .ok ⟨x :: s, r, m, p⟩
    | none => .error .underflow
  | _ => .error .underflow
/-- (S0 - DSP) / 8: the number of items, as the stack is a list here. -/
@[forth] def depth : Sem := fun s => .ok { s with ds := BitVec.ofNat 64 s.ds.length :: s.ds }

/-- A primitive ( a b -- f a b ). -/
@[forth] def bin (f : Cell → Cell → Cell) : Sem
  | ⟨b :: a :: s, r, m, u⟩ => .ok ⟨f a b :: s, r, m, u⟩
  | _ => .error .underflow
/-- A primitive ( a -- f a ). -/
@[forth] def un (f : Cell → Cell) : Sem
  | ⟨a :: s, r, m, u⟩ => .ok ⟨f a :: s, r, m, u⟩
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
  | ⟨d :: n :: s, r, m, u⟩ =>
    if d = 0 then .error .divZero else
    let q := n.sdiv d
    let m' := n - q * d
    if m' ≠ 0 ∧ (m' ^^^ d).msb then .ok ⟨(q - 1) :: (m' + d) :: s, r, m, u⟩
    else .ok ⟨q :: m' :: s, r, m, u⟩
  | _ => .error .underflow

/-- `um*` ( u1 u2 -- lo hi ): `mul` and `umulh`. -/
@[forth] def umstar : Sem
  | ⟨b :: a :: s, r, m, u⟩ =>
    .ok ⟨((a.setWidth 128 * b.setWidth 128) >>> 64).setWidth 64 :: (a * b) :: s, r, m, u⟩
  | _ => .error .underflow

/-- One round of `um/mod`'s restoring division: shift (hi, lo) left a bit,
and subtract the divisor from hi if it fits (or a bit carried out). -/
@[forth] def umdivRounds (d : Cell) : Nat → Cell → Cell → Cell × Cell
  | 0, hi, lo => (hi, lo)
  | k + 1, hi, lo =>
    let carry := hi >>> 63
    let hi' := (hi <<< 1) ||| (lo >>> 63)
    let lo' := lo <<< 1
    if carry ≠ 0 ∨ ¬ hi'.ult d then umdivRounds d k (hi' - d) (lo' ||| 1)
    else umdivRounds d k hi' lo'

/-- `um/mod` ( lo hi d -- rem quot ): 64 rounds; hi must be below d. -/
@[forth] def umslashmod : Sem
  | ⟨d :: hi :: lo :: s, r, m, u⟩ =>
    if d = 0 then .error .divZero
    else if ¬ hi.ult d then .error .outOfRange
    else let (rem, quot) := umdivRounds d 64 hi lo
         .ok ⟨quot :: rem :: s, r, m, u⟩
  | _ => .error .underflow

@[forth] def fetch : Sem
  | ⟨a :: s, r, m, u⟩ => .ok ⟨rd m a 8 :: s, r, m, u⟩
  | _ => .error .underflow
@[forth] def store : Sem
  | ⟨a :: x :: s, r, m, u⟩ => .ok ⟨s, r, wr m a 8 x, u⟩
  | _ => .error .underflow
@[forth] def cfetch : Sem
  | ⟨a :: s, r, m, u⟩ => .ok ⟨rd m a 1 :: s, r, m, u⟩
  | _ => .error .underflow
@[forth] def cstore : Sem
  | ⟨a :: x :: s, r, m, u⟩ => .ok ⟨s, r, wr m a 1 x, u⟩
  | _ => .error .underflow
@[forth] def wfetch : Sem
  | ⟨a :: s, r, m, u⟩ => .ok ⟨rd m a 2 :: s, r, m, u⟩
  | _ => .error .underflow
@[forth] def wstore : Sem
  | ⟨a :: x :: s, r, m, u⟩ => .ok ⟨s, r, wr m a 2 x, u⟩
  | _ => .error .underflow
@[forth] def lfetch : Sem
  | ⟨a :: s, r, m, u⟩ => .ok ⟨rd m a 4 :: s, r, m, u⟩
  | _ => .error .underflow
@[forth] def lstore : Sem
  | ⟨a :: x :: s, r, m, u⟩ => .ok ⟨s, r, wr m a 4 x, u⟩
  | _ => .error .underflow

/-- `cmove`'s loop: a byte at a time, lowest address first. -/
def cmoveM : Nat → Mem → Cell → Cell → Mem
  | 0, m, _, _ => m
  | n + 1, m, src, dst => cmoveM n (upd m dst (m src)) (src + 1) (dst + 1)
/-- `cmove>`'s loop: highest address first. -/
def cmoveUpM : Nat → Mem → Cell → Cell → Mem
  | 0, m, _, _ => m
  | n + 1, m, src, dst => cmoveUpM n (upd m (dst + BitVec.ofNat 64 n) (m (src + BitVec.ofNat 64 n))) src dst
def fillM : Nat → Mem → Cell → BitVec 8 → Mem
  | 0, m, _, _ => m
  | n + 1, m, a, c => fillM n (upd m a c) (a + 1) c

@[forth] def cmove : Sem
  | ⟨n :: dst :: src :: s, r, m, u⟩ => .ok ⟨s, r, cmoveM n.toNat m src dst, u⟩
  | _ => .error .underflow
@[forth] def cmoveUp : Sem
  | ⟨n :: dst :: src :: s, r, m, u⟩ => .ok ⟨s, r, cmoveUpM n.toNat m src dst, u⟩
  | _ => .error .underflow
@[forth] def fill : Sem
  | ⟨c :: n :: a :: s, r, m, u⟩ => .ok ⟨s, r, fillM n.toNat m a (c.setWidth 8), u⟩
  | _ => .error .underflow

@[forth] def upfetch : Sem := fun s => .ok { s with ds := s.up :: s.ds }

/-- (do) ( limit start -- ) ( R: -- limit start ). -/
@[forth] def pdo : Sem
  | ⟨start :: limit :: s, r, m, u⟩ => .ok ⟨s, start :: limit :: r, m, u⟩
  | _ => .error .underflow
@[forth] def i : Sem
  | ⟨s, x :: r, m, u⟩ => .ok ⟨x :: s, x :: r, m, u⟩
  | _ => .error .rUnderflow
@[forth] def j : Sem
  | ⟨s, r, m, u⟩ => match r[2]? with
    | some x => .ok ⟨x :: s, r, m, u⟩
    | none => .error .rUnderflow
@[forth] def unloop : Sem
  | ⟨s, _ :: _ :: r, m, u⟩ => .ok ⟨s, r, m, u⟩
  | _ => .error .rUnderflow

end Prim

/-- THROW, as the model sees it: 0 does nothing, anything else ends the word
with that code. (core.fs's THROW unwinds the return stack to CATCH's frame,
which this model cannot express; this is its specification, trusted.) -/
@[forth] def throwM : Sem
  | ⟨n :: s, r, m, u⟩ => if n = 0 then .ok ⟨s, r, m, u⟩ else .error (.throw n)
  | _ => .error .underflow

/-- Unfold words and primitives and run them symbolically. -/
macro "forth_run" : tactic => `(tactic| simp_all [forth])

/-- Run symbolically, split every branch taken, and settle each case as a
bit-vector problem (SAT, by `bv_decide`). -/
macro "forth_auto" : tactic =>
  `(tactic| (forth_run <;> (repeat' split) <;> (try simp_all) <;> bv_decide))

end OS4
