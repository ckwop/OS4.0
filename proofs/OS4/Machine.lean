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
  frame on the return stack (`catch`, `throw`) cannot be modelled this way;
  those two are given specifications instead (`catchM`, `throwM`).
  `(s")` is decoded by the generator into the two literals it pushes.
* Memory is bytes, little endian, at 64-bit addresses, all of it readable and
  writable. The data and return stacks are not in it, so `sp@` and `rp@`
  push unknowns (`kval`).
* Addresses in the dictionary are unknowns: `wordAddr name`, the address of
  the word with that name, plus an offset, or for reserved memory `dictTop`
  less an offset. Nothing proven depends on where
  the dictionary lands, so the generated Lean is the same on every boot.
  Different words' addresses are not known to differ.
* Kernel words that push an address or value: a kernel variable's address
  (`dp`, `latest`) is `kernelAddr name`, a user variable's (`base`,
  `handler`) is the user area plus its offset in kernel.s, a number is
  itself, and anything else (`dict-end`, `docol`) is `kval name s`, an
  unknown that may depend on the state.
* A constant's value, and the offset in the body of a word made by `user`
  or `field`, are taken as compiled: nothing changes them after definition.
* The world outside the task is unknown. While a task pauses, other tasks and
  devices may change any memory; the clock, the console and system calls give
  unknown answers. Each such event counts in `ext`, and its outcome is an
  unknown function of that count, so no two events need agree. Output is not
  recorded. `bye` ends the run (`Err.bye`).
* Step counts (`OS4.Yield`) are a second semantics of the same threads,
  generated beside this one and not proven equal to it. They trust that each
  table of xts in proofs/yields.txt holds only the words listed there, and that
  the loops listed there as not counted end.
-/

namespace OS4

abbrev Cell := BitVec 64
abbrev Mem := Cell → BitVec 8

structure S where
  ds  : List Cell
  rs  : List Cell
  mem : Mem
  up  : Cell                    -- the current task's user area (x23)
  ext : Nat                     -- outside events so far: pauses, clock reads, I/O

inductive Err where
  | underflow | rUnderflow | divZero | outOfRange | fuel | badBranch | bye
  | unknownXt                   -- an xt outside the words a table may hold (OS4.Yield)
  | throw (n : Cell)
deriving DecidableEq, Repr

/-- A failure, with the memory and event count when it happened: memory
changes made before a THROW stay made, as on the real machine. -/
structure Fail where
  err : Err
  mem : Mem
  ext : Nat

/-- What a word does: a new state, or a failure. -/
abbrev Sem := S → Except Fail S

@[forth] def S.fail {α : Type} (s : S) (e : Err) : Except Fail α := .error ⟨e, s.mem, s.ext⟩

/-- Ran out of fuel: the thread did not finish in the steps allowed. -/
def outOfFuel : Except Fail S → Prop
  | .error f => f.err = .fuel
  | .ok _ => False

/-! ## Memory -/

/-- Store one byte. -/
def upd (m : Mem) (a : Cell) (b : BitVec 8) : Mem := fun x => if x = a then b else m x

/-- Read n bytes from a, little endian. -/
def rd (m : Mem) (a : Cell) : Nat → Cell
  | 0 => 0
  | n + 1 => (m a).setWidth 64 ||| (rd m (a + 1) n <<< (8 : Cell))

/-- Write the low n bytes of v at a, little endian. -/
def wr (m : Mem) (a : Cell) : Nat → Cell → Mem
  | 0, _ => m
  | n + 1, v => wr (upd m a (v.setWidth 8)) (a + 1) n (v >>> (8 : Cell))

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
@[forth] def run (code : List Ins) : Nat → Nat → S → Except Fail S
  | 0, _, s => s.fail .fuel
  | n + 1, pc, s =>
    match code[pc]? with
    | none => s.fail .badBranch
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
      | [] => s.fail .underflow
    | some (.qdo t) =>
      match s.ds with
      | start :: limit :: ds =>
        if limit = start then run code n t { s with ds := ds }
        else run code n (pc + 1) { s with ds := ds, rs := start :: limit :: s.rs }
      | _ => s.fail .underflow
    | some (.loop t) =>
      match s.rs with
      | i :: l :: rs =>
        if i + 1 = l then run code n (pc + 1) { s with rs := rs }
        else run code n t { s with rs := (i + 1) :: l :: rs }
      | _ => s.fail .rUnderflow
    | some (.ploop t) =>
      match s.ds, s.rs with
      | k :: ds, i :: l :: rs =>
        -- ends when i - l and i + k - l differ in sign, not by overflow
        let d := i - l
        if ((d ^^^ (d + k)) &&& (d ^^^ k)).msb then run code n (pc + 1) { s with ds := ds, rs := rs }
        else run code n t { s with ds := ds, rs := (i + k) :: l :: rs }
      | [], _ => s.fail .underflow
      | _, _ => s.fail .rUnderflow

/-- A colon definition whose branches all go forwards: each cell runs at most
once, so the thread's length is fuel enough. -/
@[forth] def thread (code : List Ins) : Sem := fun s => run code code.length 0 s

/-- A colon definition with loops: its result if it ends, else `fuel`. More
fuel never changes a result that is not `fuel` (`run_mono`), so any fuel that
suffices gives the same answer. -/
noncomputable def loopThread (code : List Ins) : Sem := fun s =>
  open Classical in
  if h : ∃ n, ¬ outOfFuel (run code n 0 s) then run code (Classical.choose h) 0 s
  else s.fail .fuel

/-- A DOES> child: push its body, then run the DOES> code. -/
@[forth] def doesChild (body : Cell) (code : Sem) : Sem := fun s => code { s with ds := body :: s.ds }

@[forth] def pushConst (v : Cell) : Sem := fun s => .ok { s with ds := v :: s.ds }

/-- Where the boot files put a word (its xt), by its generated name. -/
opaque wordAddr : String → Cell

/-- The end of the dictionary's space: `reserve` takes memory below it. -/
opaque dictTop : Cell

/-- Where the kernel keeps a variable of its own (`dp`, `latest` ...): fixed, unknown here. -/
opaque kernelAddr : String → Cell

/-- What another kernel word pushes (`dict-end`, `docol` ...): unknown here. -/
opaque kval : String → S → Cell
@[forth] def kconst (name : String) : Sem := fun s => .ok { s with ds := kval name s :: s.ds }

/-- A user variable: its address in the current task's user area. The
kernel's (`defuser`: `base`, `handler` ...) and those `user` defines, whose
offset is the one cell of their body. -/
@[forth] def userAt (off : Cell) : Sem := fun s => .ok { s with ds := (s.up + off) :: s.ds }

/-- A Forth flag: all bits set for true. -/
@[forth] def flag (b : Bool) : Cell := if b then -1 else 0

/-! ## Primitives -/

namespace Prim

@[forth] def dup : Sem
  | ⟨x :: s, r, m, u, e⟩ => .ok ⟨x :: x :: s, r, m, u, e⟩
  | s => s.fail .underflow
@[forth] def drop : Sem
  | ⟨_ :: s, r, m, u, e⟩ => .ok ⟨s, r, m, u, e⟩
  | s => s.fail .underflow
@[forth] def swap : Sem
  | ⟨b :: a :: s, r, m, u, e⟩ => .ok ⟨a :: b :: s, r, m, u, e⟩
  | s => s.fail .underflow
@[forth] def over : Sem
  | ⟨b :: a :: s, r, m, u, e⟩ => .ok ⟨a :: b :: a :: s, r, m, u, e⟩
  | s => s.fail .underflow
@[forth] def tor : Sem
  | ⟨x :: s, r, m, u, e⟩ => .ok ⟨s, x :: r, m, u, e⟩
  | s => s.fail .underflow
@[forth] def rfrom : Sem
  | ⟨s, x :: r, m, u, e⟩ => .ok ⟨x :: s, r, m, u, e⟩
  | s => s.fail .rUnderflow
@[forth] def rfetch : Sem
  | ⟨s, x :: r, m, u, e⟩ => .ok ⟨x :: s, x :: r, m, u, e⟩
  | s => s.fail .rUnderflow
/-- `ldr TOS, [DSP, TOS, lsl #3]`: the u-th item below u itself. -/
@[forth] def pick : Sem
  | ⟨u :: s, r, m, p, e⟩ => match s[u.toNat]? with
    | some x => .ok ⟨x :: s, r, m, p, e⟩
    | none => .error ⟨.underflow, m, e⟩
  | s => s.fail .underflow
/-- (S0 - DSP) / 8: the number of items, as the stack is a list here. -/
@[forth] def depth : Sem := fun s => .ok { s with ds := BitVec.ofNat 64 s.ds.length :: s.ds }

/-- A primitive ( a b -- f a b ). -/
@[forth] def bin (f : Cell → Cell → Cell) : Sem
  | ⟨b :: a :: s, r, m, u, e⟩ => .ok ⟨f a b :: s, r, m, u, e⟩
  | s => s.fail .underflow
/-- A primitive ( a -- f a ). -/
@[forth] def un (f : Cell → Cell) : Sem
  | ⟨a :: s, r, m, u, e⟩ => .ok ⟨f a :: s, r, m, u, e⟩
  | s => s.fail .underflow

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
  | ⟨d :: n :: s, r, m, u, e⟩ =>
    if d = 0 then .error ⟨.divZero, m, e⟩ else
    let q := n.sdiv d
    let m' := n - q * d
    if m' ≠ 0 ∧ (m' ^^^ d).msb then .ok ⟨(q - 1) :: (m' + d) :: s, r, m, u, e⟩
    else .ok ⟨q :: m' :: s, r, m, u, e⟩
  | s => s.fail .underflow

/-- `um*` ( u1 u2 -- lo hi ): `mul` and `umulh`. -/
@[forth] def umstar : Sem
  | ⟨b :: a :: s, r, m, u, e⟩ =>
    .ok ⟨((a.setWidth 128 * b.setWidth 128) >>> 64).setWidth 64 :: (a * b) :: s, r, m, u, e⟩
  | s => s.fail .underflow

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
  | ⟨d :: hi :: lo :: s, r, m, u, e⟩ =>
    if d = 0 then .error ⟨.divZero, m, e⟩
    else if ¬ hi.ult d then .error ⟨.outOfRange, m, e⟩
    else let p := umdivRounds d 64 hi lo        -- (rem, quot)
         .ok ⟨p.2 :: p.1 :: s, r, m, u, e⟩
  | s => s.fail .underflow

@[forth] def fetch : Sem
  | ⟨a :: s, r, m, u, e⟩ => .ok ⟨rd m a 8 :: s, r, m, u, e⟩
  | s => s.fail .underflow
@[forth] def store : Sem
  | ⟨a :: x :: s, r, m, u, e⟩ => .ok ⟨s, r, wr m a 8 x, u, e⟩
  | s => s.fail .underflow
@[forth] def cfetch : Sem
  | ⟨a :: s, r, m, u, e⟩ => .ok ⟨rd m a 1 :: s, r, m, u, e⟩
  | s => s.fail .underflow
@[forth] def cstore : Sem
  | ⟨a :: x :: s, r, m, u, e⟩ => .ok ⟨s, r, wr m a 1 x, u, e⟩
  | s => s.fail .underflow
@[forth] def wfetch : Sem
  | ⟨a :: s, r, m, u, e⟩ => .ok ⟨rd m a 2 :: s, r, m, u, e⟩
  | s => s.fail .underflow
@[forth] def wstore : Sem
  | ⟨a :: x :: s, r, m, u, e⟩ => .ok ⟨s, r, wr m a 2 x, u, e⟩
  | s => s.fail .underflow
@[forth] def lfetch : Sem
  | ⟨a :: s, r, m, u, e⟩ => .ok ⟨rd m a 4 :: s, r, m, u, e⟩
  | s => s.fail .underflow
@[forth] def lstore : Sem
  | ⟨a :: x :: s, r, m, u, e⟩ => .ok ⟨s, r, wr m a 4 x, u, e⟩
  | s => s.fail .underflow

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
  | ⟨n :: dst :: src :: s, r, m, u, e⟩ => .ok ⟨s, r, cmoveM n.toNat m src dst, u, e⟩
  | s => s.fail .underflow
@[forth] def cmoveUp : Sem
  | ⟨n :: dst :: src :: s, r, m, u, e⟩ => .ok ⟨s, r, cmoveUpM n.toNat m src dst, u, e⟩
  | s => s.fail .underflow
@[forth] def fill : Sem
  | ⟨c :: n :: a :: s, r, m, u, e⟩ => .ok ⟨s, r, fillM n.toNat m a (c.setWidth 8), u, e⟩
  | s => s.fail .underflow

@[forth] def upfetch : Sem := fun s => .ok { s with ds := s.up :: s.ds }

/-- (do) ( limit start -- ) ( R: -- limit start ). -/
@[forth] def pdo : Sem
  | ⟨start :: limit :: s, r, m, u, e⟩ => .ok ⟨s, start :: limit :: r, m, u, e⟩
  | s => s.fail .underflow
@[forth] def i : Sem
  | ⟨s, x :: r, m, u, e⟩ => .ok ⟨x :: s, x :: r, m, u, e⟩
  | s => s.fail .rUnderflow
@[forth] def j : Sem
  | ⟨s, r, m, u, e⟩ => match r[2]? with
    | some x => .ok ⟨x :: s, r, m, u, e⟩
    | none => .error ⟨.rUnderflow, m, e⟩
@[forth] def unloop : Sem
  | ⟨s, _ :: _ :: r, m, u, e⟩ => .ok ⟨s, r, m, u, e⟩
  | s => s.fail .rUnderflow

/-! ### The outside world -/

/-- Memory after outside event n: what other tasks and devices left. -/
opaque worldMem : Nat → Mem → Mem
/-- The answer to outside event n (a clock reading, a key, a system call's result). -/
opaque worldVal : Nat → S → Cell

/-- PAUSE: other tasks run, and may change any memory. -/
@[forth] def pause : Sem := fun s => .ok { s with mem := worldMem s.ext s.mem, ext := s.ext + 1 }
/-- A primitive ( -- x ) that asks the world: COUNTER, KEY, KEY?. -/
@[forth] def ask : Sem := fun s => .ok { s with ds := worldVal s.ext s :: s.ds, ext := s.ext + 1 }
/-- EMIT ( c -- ): output, not recorded. -/
@[forth] def emit : Sem
  | ⟨_ :: s, r, m, u, e⟩ => .ok ⟨s, r, m, u, e + 1⟩
  | s => s.fail .underflow
/-- SYSCALL ( a b c d n -- r ): may change memory (a read fills a buffer). -/
@[forth] def syscall : Sem
  | ⟨n :: d :: c :: b :: a :: s, r, m, u, e⟩ =>
    let st : S := ⟨n :: d :: c :: b :: a :: s, r, m, u, e⟩
    .ok ⟨worldVal e st :: s, r, worldMem e m, u, e + 1⟩
  | s => s.fail .underflow
@[forth] def bye : Sem := fun s => s.fail .bye
/-- DMB, DSB: order memory accesses; nothing to the single task modelled. -/
@[forth] def barrier : Sem := fun s => .ok s

/-- SHA-256's compression and output: pure functions of memory, unknown here. -/
opaque sha256Block : Mem → Cell → Cell → Cell → Cell → Mem
opaque sha256Out : Mem → Cell → Cell → Mem
@[forth] def sha256block : Sem
  | ⟨k :: w :: st :: b :: s, r, m, u, e⟩ => .ok ⟨s, r, sha256Block m b st w k, u, e⟩
  | s => s.fail .underflow
@[forth] def sha256out : Sem
  | ⟨a :: st :: s, r, m, u, e⟩ => .ok ⟨s, r, sha256Out m st a, u, e⟩
  | s => s.fail .underflow

/-! ### The compiler and the interpreter (compiler.s, text.s) -/

/-- The kernel variables the compiler keeps: the dictionary pointer, the
newest header, and the end of the dictionary's space. -/
abbrev dpA : Cell := kernelAddr "dp"
abbrev latestA : Cell := kernelAddr "latest"
abbrev dictEndA : Cell := kernelAddr "'dict-end"

/-- `,` ( x -- ): store x at the dictionary pointer and step it, or throw
-8 if fewer than 8 bytes are left (`comma_sub`). -/
@[forth] def comma : Sem
  | ⟨x :: s, r, m, u, e⟩ =>
    let dp := rd m dpA 8
    if (rd m dictEndA 8 - 8).ult dp then .error ⟨.throw (-8), m, e⟩
    else .ok ⟨s, r, wr (wr m dp 8 x) dpA 8 (dp + 8), u, e⟩
  | s => s.fail .underflow

/-- TOLOWER: A to Z become a to z. -/
def lowerB (c : BitVec 8) : BitVec 8 := if c.toNat - 65 ≤ 25 ∧ 65 ≤ c.toNat then c + 32 else c

/-- The n bytes at a and at b are equal, ignoring case. -/
def nameEq (m : Mem) : Nat → Cell → Cell → Bool
  | 0, _, _ => true
  | n + 1, a, b => lowerB (m a) == lowerB (m b) && nameEq m n (a + 1) (b + 1)

/-- The header at nt is not hidden, and is named by the u bytes at a. A
header is its link (8 bytes), a flags and length byte, then the name. -/
def nameMatch (m : Mem) (a u nt : Cell) : Bool :=
  let fl := m (nt + 8)
  (fl &&& 0x40) == 0 && (fl &&& 0x1f).setWidth 64 == u && nameEq m u.toNat a (nt + 9)

/-- `search_sub`, walking at most n headers: some result, or none if it
needs more. -/
def walk (m : Mem) (a u : Cell) : Nat → Cell → Option Cell
  | 0, _ => none
  | n + 1, nt => if nt = 0 then some 0 else if nameMatch m a u nt then some nt
                 else walk m a u n (rd m nt 8)

/-- SEARCH-LIST ( addr u nt -- nt' | 0 ): from nt back along the links, the
first header named addr u. On a list that never ends it never returns
(`fuel`). -/
noncomputable def searchList : Sem
  | ⟨nt :: u :: a :: s, r, m, p, e⟩ =>
    open Classical in
    if h : ∃ n, (walk m a u n nt).isSome then
      .ok ⟨(walk m a u (Classical.choose h) nt).get (Classical.choose_spec h) :: s, r, m, p, e⟩
    else .error ⟨.fuel, m, e⟩
  | s => s.fail .underflow

/-- From index i, step on while i < n and the byte at tib + i passes p. -/
def scan (m : Mem) (tib n : Cell) (p : BitVec 8 → Bool) : Nat → Cell → Cell
  | 0, i => i
  | k + 1, i => if n.ule i then i else if p (m (tib + i)) then scan m tib n p k (i + 1) else i

/-- The user area's line: 'tib, #tib and >in (kernel.s's U_TIB, U_NTIB, U_TOIN). -/
abbrev uTib : Cell := 32
abbrev uNtib : Cell := 24
abbrev uToin : Cell := 16

/-- PARSE-NAME ( "name" -- addr u ), the kernel's (`parse_name_sub`): skip
bytes up to a space, take bytes above it, and step past one delimiter. -/
@[forth] def parseName : Sem := fun ⟨s, r, m, p, e⟩ =>
  let tib := rd m (p + uTib) 8
  let n := rd m (p + uNtib) 8
  let i := scan m tib n (fun c => c.ule 32) n.toNat (rd m (p + uToin) 8)
  if n.ule i then .ok ⟨0 :: (tib + i) :: s, r, wr m (p + uToin) 8 i, p, e⟩
  else
    let j := scan m tib n (fun c => 32 < c.toNat) n.toNat (i + 1)
    let toin := if n.ule j then j else j + 1
    .ok ⟨(j - i) :: (tib + i) :: s, r, wr m (p + uToin) 8 toin, p, e⟩

/-- PARSE ( char "ccc<char>" -- addr u ), the kernel's (`parse_sub`): the
bytes up to the delimiter (its low 32 bits) or the end of the line. -/
@[forth] def parse : Sem
  | ⟨c :: s, r, m, p, e⟩ =>
    let tib := rd m (p + uTib) 8
    let n := rd m (p + uNtib) 8
    let i := rd m (p + uToin) 8
    let j := scan m tib n (fun b => b.setWidth 32 != c.setWidth 32) n.toNat i
    let toin := if n.ule j then j else j + 1
    .ok ⟨(j - i) :: (tib + i) :: s, r, wr m (p + uToin) 8 toin, p, e⟩
  | s => s.fail .underflow

/-- `(` ( "ccc<paren>" -- ): a comment, skipped to the next `)` or the end of
the line (`w_paren`: `parse_sub` for `)`, its results dropped). -/
@[forth] def paren : Sem := fun ⟨s, r, m, p, e⟩ =>
  let tib := rd m (p + uTib) 8
  let n := rd m (p + uNtib) 8
  let i := rd m (p + uToin) 8
  let j := scan m tib n (fun b => b.setWidth 32 != (41 : Cell).setWidth 32) n.toNat i
  let toin := if n.ule j then j else j + 1
  .ok ⟨s, r, wr m (p + uToin) 8 toin, p, e⟩

/-- HEADER ( addr u -- ): lay down a header named addr u at the dictionary
pointer, aligned, and link it in as the newest (`header_sub`). -/
@[forth] def header : Sem
  | ⟨u :: a :: s, r, m, p, e⟩ =>
    if u = 0 then .error ⟨.throw (-16), m, e⟩
    else if (31 : Cell).ult u then .error ⟨.throw (-19), m, e⟩
    else
      let dp := rd m dpA 8
      if (rd m dictEndA 8 - 64).ult dp then .error ⟨.throw (-8), m, e⟩
      else
        let h := (dp + 7) &&& ~~~7
        let m1 := wr m h 8 (rd m latestA 8)
        let m2 := wr m1 latestA 8 h
        let m3 := wr m2 (h + 8) 1 u
        let m4 := cmoveM u.toNat m3 a (h + 9)
        .ok ⟨s, r, wr m4 dpA 8 ((h + 9 + u + 7) &&& ~~~7), p, e⟩
  | s => s.fail .underflow

end Prim

/-! ## Exceptions and EXECUTE

CATCH and THROW reach below their own frame on the return stack, which this
model cannot express, so core.fs's definitions are replaced by these
specifications (trusted). -/

/-- THROW: 0 does nothing; anything else fails with that code. -/
@[forth] def throwM : Sem
  | ⟨n :: s, r, m, u, e⟩ => if n = 0 then .ok ⟨s, r, m, u, e⟩ else .error ⟨.throw n, m, e⟩
  | s => s.fail .underflow

/-- The code CATCH sees for a failure, if it catches it: kernel errors are
thrown with the codes in kernel.s. Running out of fuel (not finishing) and
BYE are not caught. -/
def Err.code : Err → Option Cell
  | .underflow => some (-4)
  | .rUnderflow => some (-6)
  | .divZero => some (-10)
  | .outOfRange => some (-11)
  | .throw n => some n
  | _ => none

/-- What the word with execution token xt does. Unknown here: a theorem
proven with it holds whatever the dictionary holds. A theorem that needs to
know what an xt does states it as a hypothesis. -/
opaque dispatch : Cell → Sem

/-- EXECUTE ( i*x xt -- j*x ). -/
@[forth] def executeM : Sem
  | ⟨xt :: s, r, m, u, e⟩ => dispatch xt ⟨s, r, m, u, e⟩
  | s => s.fail .underflow

/-- What is left in the data stack's cells after THROW restores its depth:
whatever the words that ran left there. -/
opaque junk : Nat → Nat → Cell

/-- CATCH ( i*x xt -- j*x 0 | i*x n ): run xt. If it fails with a code, the
return stack, the user area and the data stack's depth are as they were, but
not necessarily the items' values; memory keeps what was done to it. -/
@[forth] def catchM : Sem
  | ⟨xt :: s, r, m, u, e⟩ =>
    match dispatch xt ⟨s, r, m, u, e⟩ with
    | .ok st => .ok { st with ds := 0 :: st.ds }
    | .error f =>
      match f.err.code with
      | some n => .ok ⟨n :: (List.range s.length).map (junk f.ext), r, f.mem, u, f.ext⟩
      | none => .error f
  | s => s.fail .underflow

/-- A word's stack comment: run on some items above the stack `s`, if it
returns, it leaves `outs` items above that same `s`, the return stack as it
was, and the user area unchanged. -/
def Effect (res : Except Fail S) (s r : List Cell) (u : Cell) (outs : Nat) : Prop :=
  match res with
  | .ok st => st.ds.drop outs = s ∧ st.ds.length = outs + s.length ∧ st.rs = r ∧ st.up = u
  | .error _ => True

/-- Unfold words and primitives and run them symbolically. -/
macro "forth_run" : tactic => `(tactic| simp_all [forth])

/-- Run symbolically, split every branch taken, and settle each case as a
bit-vector problem (SAT, by `bv_decide`). -/
macro "forth_auto" : tactic =>
  `(tactic| (forth_run <;> (repeat' split) <;> (try simp_all) <;> bv_decide))

/-- Prove an `Effect`: run symbolically, split every branch, and count. -/
macro "forth_effect" : tactic =>
  `(tactic| (simp [forth] <;> (repeat' split) <;> simp_all [Effect] <;> omega))

end OS4
