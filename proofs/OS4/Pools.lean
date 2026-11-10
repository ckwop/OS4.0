import OS4.Words.NetTcp
import OS4.Loops
import OS4.Memory
import OS4.FootPrims

/-!
# The connection pool (V4)

Live connections and recycled ones sit on two lists linked through each
connection's first cell (`c.link`). `unlink` takes a connection off a list:
here it is proven to leave exactly the list without it, whatever the list
holds, provided the list ends and its cells are apart. That is the step on
which every closing path's return of its slot rests (`(free-conn)`).

Then `hash-out`, the same walk through each connection's hash link, and the
two pool steps: `(free-conn)` moves a live connection to the free list
(`free_conn_step`), `new-conn` moves a free one to the live list
(`new_conn_pool`), each keeping `Pool` (both lists end, their link cells
apart) and the total of live and free.
-/

namespace OS4.Pools
open OS4

/-- The list xs, linked from the cell at a through each element's first cell,
ending in 0. -/
def Chain (m : Mem) (a : Cell) : List Cell → Prop
  | [] => rd m a 8 = 0
  | x :: xs => rd m a 8 = x ∧ x ≠ 0 ∧ Chain m x xs

/-- `unlink`'s memory: the cell before c's first occurrence takes c's link. -/
def unlinkM (m : Mem) (c : Cell) : Cell → List Cell → Mem
  | _, [] => m
  | a, x :: xs => if x = c then wr m a 8 (rd m c 8) else unlinkM m c x xs

/-- Steps `unlink` takes over a list: 11 a connection it passes, 15 for the
one it finds, 5 at the end. -/
def unlinkFuel (c : Cell) : List Cell → Nat
  | [] => 5
  | x :: xs => if x = c then 15 else 11 + unlinkFuel c xs

set_option maxHeartbeats 4000000 in
theorem unlink_run (c : Cell) (s r : List Cell) (u : Cell) (e : Nat) :
    ∀ (xs : List Cell) (a : Cell) (m : Mem) (n : Nat), Chain m a xs →
      run Words.«unlink».code (unlinkFuel c xs + n) 0 ⟨a :: c :: s, r, m, u, e⟩ =
        .ok ⟨s, r, unlinkM m c a xs, u, e⟩ := by
  intro xs
  induction xs with
  | nil =>
    intro a m n h
    simp only [Chain] at h
    simp only [unlinkFuel, unlinkM]
    rw [show 5 + n = n + 1 + 1 + 1 + 1 + 1 by omega]
    simp [forth, h]
  | cons x xs ih =>
    intro a m n h
    obtain ⟨hx, hx0, hc⟩ := h
    by_cases hxc : x = c
    · subst hxc
      simp only [unlinkFuel, unlinkM, if_true]
      rw [show 15 + n = n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 by omega]
      simp [forth, hx, hx0]
      exact fun h => absurd h hx0
    · simp only [unlinkFuel, unlinkM, if_neg hxc]
      rw [show 11 + unlinkFuel c xs + n = (unlinkFuel c xs + n) + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1
        by omega]
      have step := ih x m n hc
      simp [forth, hx, hx0, hxc] at step ⊢
      rw [if_neg (by simpa using hx0)]
      exact step

/-- `unlink` ends, with that memory, on any list that ends. -/
theorem unlink_eq (c a : Cell) (xs : List Cell) (s r : List Cell) (m : Mem) (u : Cell) (e : Nat)
    (h : Chain m a xs) :
    Words.«unlink» ⟨a :: c :: s, r, m, u, e⟩ = .ok ⟨s, r, unlinkM m c a xs, u, e⟩ := by
  have hr := unlink_run c s r u e xs a m 0 h
  exact loopThread_eq _ _ _ _ hr (by simp [outOfFuel])

/-- Two cells that do not overlap. -/
def Apart (x y : Cell) : Prop := 8 ≤ x - y ∧ 8 ≤ y - x

/-- A store to a cell apart from every cell of a chain leaves the chain. -/
theorem chain_wr (q v : Cell) : ∀ (ys : List Cell) (b : Cell) (m : Mem),
    Chain m b ys → (∀ y ∈ b :: ys, Apart q y) → Chain (wr m q 8 v) b ys := by
  intro ys
  induction ys with
  | nil =>
    intro b m h hq
    have hb := hq b (by simp)
    simp only [Chain] at h ⊢
    rw [rd_wr_other m q b v hb.2 hb.1]; exact h
  | cons y ys ih =>
    intro b m h hq
    obtain ⟨hy, hy0, hc⟩ := h
    have hb := hq b (by simp)
    refine ⟨by rw [rd_wr_other m q b v hb.2 hb.1]; exact hy, hy0, ?_⟩
    exact ih y m hc fun z hz => hq z (List.mem_cons_of_mem b hz)

/-- `unlink` stores only into a cell of the chain it walks. -/
theorem unlinkM_rd (m : Mem) (c a : Cell) : ∀ (xs : List Cell) (b : Cell),
    (∀ y ∈ b :: xs, Apart a y) → rd (unlinkM m c b xs) a 8 = rd m a 8 := by
  intro xs
  induction xs with
  | nil => intro b _; rfl
  | cons y ys ih =>
    intro b hb
    simp only [unlinkM]
    split
    · have h := hb b (by simp)
      exact rd_wr_other m b a _ h.1 h.2
    · exact ih y fun z hz => hb z (List.mem_cons_of_mem b hz)

/-- `unlink` takes c off a chain: what is left is the chain without it. The
chain's cells (the list's head cell and each element's) must be apart. -/
theorem unlink_chain (c : Cell) : ∀ (xs : List Cell) (a : Cell) (m : Mem),
    Chain m a xs → (a :: xs).Pairwise Apart → c ∈ xs →
      Chain (unlinkM m c a xs) a (xs.erase c) := by
  intro xs
  induction xs with
  | nil => intro a m _ _ hc; simp at hc
  | cons x xs ih =>
    intro a m h hp hc
    obtain ⟨hx, hx0, hch⟩ := h
    have hpa := List.pairwise_cons.mp hp
    by_cases hxc : x = c
    · subst hxc
      simp only [unlinkM, if_true, List.erase_cons_head]
      -- a now holds x's link: the rest of the chain, which a is apart from
      cases xs with
      | nil =>
        simp only [Chain] at hch ⊢
        rw [hch, rd_wr_same]
      | cons y ys =>
        obtain ⟨hy, hy0, hrest⟩ := hch
        refine ⟨by rw [hy, rd_wr_same], hy0, ?_⟩
        apply chain_wr a _ ys y m hrest
        intro z hz
        exact hpa.1 z (List.mem_cons_of_mem x hz)
    · have hc' : c ∈ xs := (List.mem_cons.mp hc).resolve_left fun h => hxc h.symm
      simp only [unlinkM, if_neg hxc]
      rw [show (x :: xs).erase c = x :: xs.erase c by simp [List.erase_cons, hxc]]
      have hrec := ih x m hch (List.pairwise_cons.mp hp).2 hc'
      refine ⟨?_, hx0, hrec⟩
      -- the store lands on a cell of the rest of the chain, apart from a
      rw [unlinkM_rd m c a xs x hpa.1]
      exact hx

/-- Every connection on a chain is nonzero. -/
theorem chain_ne (m : Mem) : ∀ (a : Cell) (xs : List Cell), Chain m a xs → ∀ c ∈ xs, c ≠ 0 := by
  intro a xs
  induction xs generalizing a with
  | nil => intro _ c hc; simp at hc
  | cons x xs ih =>
    intro h c hc
    obtain ⟨_, hx0, hch⟩ := h
    rcases List.mem_cons.mp hc with rfl | hc
    · exact hx0
    · exact ih x hch c hc

/-- `unlink` leaves a chain whose cells are all apart from those it walks. -/
theorem chain_unlinkM (m : Mem) (c b : Cell) (ys : List Cell) :
    ∀ (L : List Cell) (a : Cell), Chain m b ys → (∀ q ∈ a :: L, ∀ y ∈ b :: ys, Apart q y) →
      Chain (unlinkM m c a L) b ys := by
  intro L
  induction L with
  | nil => intro a h _; exact h
  | cons x xs ih =>
    intro a h hq
    simp only [unlinkM]
    split
    · exact chain_wr a _ ys b m h (hq a (by simp))
    · exact ih x h fun q hq' y hy => hq q (List.mem_cons_of_mem a hq') y hy

/-- In a list whose items are pairwise apart, c is apart from what is left
when it is taken out. -/
theorem erase_apart : ∀ (L : List Cell) (c x : Cell), L.Pairwise Apart → c ∈ L → x ∈ L.erase c →
    Apart c x := by
  intro L
  induction L with
  | nil => intro c x _ hc; simp at hc
  | cons y ys ih =>
    intro c x hp hc hx
    have hpa := List.pairwise_cons.mp hp
    by_cases hyc : y = c
    · subst hyc
      simp only [List.erase_cons_head] at hx
      exact hpa.1 x hx
    · rw [show (y :: ys).erase c = y :: ys.erase c by simp [List.erase_cons, hyc]] at hx
      have hc' : c ∈ ys := (List.mem_cons.mp hc).resolve_left fun h => hyc h.symm
      rcases List.mem_cons.mp hx with hxy | hx'
      · have h2 := hpa.1 c hc'
        rw [hxy]
        exact ⟨h2.2, h2.1⟩
      · exact ih c x hpa.2 hc' hx'

/-! ## The pool: live and free

The live connections hang from `conns`, the recycled ones from `free-conns`,
both through `c.link`. `Pool m L F` says memory m holds those two lists, L and
F, and that every link cell on them, and the two variables, are apart: so no
connection is on both lists, or twice on one. Then the connections in the pool
are L and F together, and `(free-conn)` moves one from L to F. -/

abbrev connsV : Cell := wordAddr "conns" + 8#64
abbrev freeV : Cell := wordAddr "free-conns" + 8#64

structure Pool (m : Mem) (L F : List Cell) : Prop where
  live : Chain m connsV L
  free : Chain m freeV F
  heads : Apart connsV freeV
  liveV : ∀ x ∈ L, Apart connsV x ∧ Apart freeV x
  freeV' : ∀ x ∈ F, Apart connsV x ∧ Apart freeV x
  liveP : L.Pairwise Apart
  freeP : F.Pairwise Apart
  cross : ∀ x ∈ L, ∀ y ∈ F, Apart x y

/-- `(free-conn)`'s memory after `hash-out`: c unlinked from the live list,
then pushed on the free list. -/
def freeConnM (m : Mem) (c : Cell) (L : List Cell) : Mem :=
  wr (wr (unlinkM m c connsV L) c 8 (rd (unlinkM m c connsV L) freeV 8)) freeV 8 c

/-- `(free-conn)` moves c from the live list to the free list, and keeps the
pool whole. -/
theorem free_conn_pool (m : Mem) (c : Cell) (L F : List Cell) (hp : Pool m L F) (hc : c ∈ L) :
    Pool (freeConnM m c L) (L.erase c) (c :: F) := by
  obtain ⟨hl, hf, hh, hlv, hfv, hlp, hfp, hx⟩ := hp
  have hc0 : c ≠ 0 := chain_ne m connsV L hl c hc
  have hcv := hlv c hc
  have hl3 : Chain (unlinkM m c connsV L) connsV (L.erase c) :=
    unlink_chain c L connsV m hl (List.pairwise_cons.mpr ⟨fun x hx' => (hlv x hx').1, hlp⟩) hc
  have hf3 : Chain (unlinkM m c connsV L) freeV F := by
    apply chain_unlinkM m c freeV F L connsV hf
    intro q hq y hy
    rcases List.mem_cons.mp hq with hq1 | hq2
    · rw [hq1]
      rcases List.mem_cons.mp hy with hy1 | hy2
      · rw [hy1]; exact hh
      · exact (hfv y hy2).1
    · rcases List.mem_cons.mp hy with hy1 | hy2
      · rw [hy1]; exact ⟨(hlv q hq2).2.2, (hlv q hq2).2.1⟩
      · exact hx q hq2 y hy2
  simp only [freeConnM]
  generalize unlinkM m c connsV L = m3 at hl3 hf3
  -- c now takes the old head of the free list
  have hcF : Chain (wr m3 c 8 (rd m3 freeV 8)) c F := by
    cases F with
    | nil =>
      simp only [Chain] at hf3 ⊢
      rw [rd_wr_same]; exact hf3
    | cons y ys =>
      obtain ⟨hy, hy0, hys⟩ := hf3
      refine ⟨by rw [rd_wr_same]; exact hy, hy0, ?_⟩
      exact chain_wr c _ ys y m3 hys fun z hz => hx c hc z hz
  have hfa : ∀ y ∈ c :: F, Apart freeV y := by
    intro y hy
    rcases List.mem_cons.mp hy with hy1 | hy2
    · rw [hy1]; exact hcv.2
    · exact (hfv y hy2).2
  refine ⟨?_, ?_, hh, ?_, ?_, ?_, ?_, ?_⟩
  · -- the live list, without c
    apply chain_wr freeV c _ connsV _ _
    · intro y hy
      rcases List.mem_cons.mp hy with hy1 | hy2
      · rw [hy1]; exact ⟨hh.2, hh.1⟩
      · exact (hlv y (List.mem_of_mem_erase hy2)).2
    · apply chain_wr c _ _ connsV m3 hl3
      intro y hy
      rcases List.mem_cons.mp hy with hy1 | hy2
      · rw [hy1]; exact ⟨hcv.1.2, hcv.1.1⟩
      · exact erase_apart L c y hlp hc hy2
  · -- the free list, with c in front
    refine ⟨by rw [rd_wr_same], hc0, ?_⟩
    exact chain_wr freeV c F c _ hcF hfa
  · intro x hx'
    exact hlv x (List.mem_of_mem_erase hx')
  · intro x hx'
    rcases List.mem_cons.mp hx' with hx1 | hx2
    · rw [hx1]; exact hcv
    · exact hfv x hx2
  · exact List.Pairwise.sublist List.erase_sublist hlp
  · exact List.pairwise_cons.mpr ⟨fun y hy => hx c hc y hy, hfp⟩
  · intro x hx' y hy
    rcases List.mem_cons.mp hy with hy1 | hy2
    · rw [hy1]
      have h2 := erase_apart L c x hlp hc hx'
      exact ⟨h2.2, h2.1⟩
    · exact hx x (List.mem_of_mem_erase hx') y hy2

/-- So the pool keeps its size: free plus live is what it was. -/
theorem free_conn_count (L F : List Cell) (c : Cell) (hc : c ∈ L) :
    (L.erase c).length + (c :: F).length = L.length + F.length := by
  have h1 := List.length_erase_of_mem hc
  have h2 := List.length_pos_of_mem hc
  simp only [List.length_cons]
  omega

set_option maxHeartbeats 4000000 in
/-- `(free-conn)` runs `hash-out`, then takes c off the live list and puts it
on the free one. -/
theorem free_conn_eq (c : Cell) (L s r : List Cell) (m m2 : Mem) (u : Cell) (e e2 : Nat)
    (hh : Words.«hash-out» ⟨c :: c :: s, r, m, u, e⟩ = .ok ⟨c :: s, r, m2, u, e2⟩)
    (hl : Chain m2 (wordAddr "conns" + 8#64) L) :
    Words.«(free-conn)» ⟨c :: s, r, m, u, e⟩ = .ok ⟨s, r, freeConnM m2 c L, u, e2⟩ := by
  have hu := unlink_eq c (wordAddr "conns" + 8#64) L (c :: s) r m2 u e2 hl
  simp only [Words.«(free-conn)», Words.«(free-conn)».code, thread]
  generalize Words.«hash-out» = HO at hh ⊢
  generalize Words.«unlink» = UL at hu ⊢
  simp [forth, hh, hu, freeConnM]

/-! ## Hash buckets

`hash-out` takes a connection out of its hash bucket: the same walk as
`unlink`, through each connection's hash link (`c.hlink`, 152 bytes in),
from the bucket `conn-bucket` names. -/

/-- A bucket's list xs: from the cell at a through each connection's hash
link, ending in 0. -/
def HChain (m : Mem) (a : Cell) : List Cell → Prop
  | [] => rd m a 8 = 0
  | x :: xs => rd m a 8 = x ∧ x ≠ 0 ∧ HChain m (x + 152) xs

/-- `hash-out`'s memory: the cell before c takes c's hash link. -/
def hunlinkM (m : Mem) (c : Cell) : Cell → List Cell → Mem
  | _, [] => m
  | a, x :: xs => if x = c then wr m a 8 (rd m (c + 152) 8) else hunlinkM m c (x + 152) xs

/-- Steps of `hash-out`'s walk: 12 a connection it passes, 15 for the one it
finds, 5 at the end. -/
def hashOutFuel (c : Cell) : List Cell → Nat
  | [] => 5
  | x :: xs => if x = c then 15 else 12 + hashOutFuel c xs

/-- `hash-out`'s thread, with `conn-bucket` left as CB. -/
noncomputable def hashOutCode (CB : Sem) : List Ins := [.call Prim.dup, .call CB, .call Prim.dup, .call Prim.fetch,
  .zbranch 20, .call Prim.dup, .call Prim.fetch, .lit 2, .call Prim.pick, .call Prim.equal, .zbranch 17,
  .call Prim.swap, .call Words.«c.hlink», .call Prim.fetch, .call Prim.swap, .call Prim.store, .exit,
  .call Prim.fetch, .call Words.«c.hlink», .branch 2, .call Words.«2drop», .exit]

theorem hashOutCode_eq : Words.«hash-out».code = hashOutCode Words.«conn-bucket» := rfl

set_option maxHeartbeats 4000000 in
theorem hash_out_run (CB : Sem) (c : Cell) (s r : List Cell) (u : Cell) (e : Nat) :
    ∀ (xs : List Cell) (a : Cell) (m : Mem) (n : Nat), HChain m a xs →
      run (hashOutCode CB) (hashOutFuel c xs + n) 2 ⟨a :: c :: s, r, m, u, e⟩ =
        .ok ⟨s, r, hunlinkM m c a xs, u, e⟩ := by
  intro xs
  induction xs with
  | nil =>
    intro a m n h
    simp only [HChain] at h
    simp only [hashOutFuel, hunlinkM]
    rw [show 5 + n = n + 1 + 1 + 1 + 1 + 1 by omega]
    simp [forth, hashOutCode, h]
  | cons x xs ih =>
    intro a m n h
    obtain ⟨hx, hx0, hc⟩ := h
    by_cases hxc : x = c
    · subst hxc
      simp only [hashOutFuel, hunlinkM, if_true]
      rw [show 15 + n = n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 by omega]
      simp [forth, hashOutCode, hx, hx0]
      all_goals (first | exact fun h => absurd h hx0 | simp_all)
    · simp only [hashOutFuel, hunlinkM, if_neg hxc]
      rw [show 12 + hashOutFuel c xs + n =
        (hashOutFuel c xs + n) + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 by omega]
      have step := ih (x + 152) m n hc
      simp [forth, hashOutCode, hx, hx0, hxc] at step ⊢
      all_goals (first | exact step | (rw [if_neg (by simpa using hx0)]; exact step) | simp_all)

/-- `hash-out`, given where `conn-bucket` says c's bucket is (b) and the
bucket's list there (H), ends with that memory. -/
theorem hash_out_gen (CB : Sem) (c b : Cell) (H s r : List Cell) (m m1 : Mem) (u : Cell) (e e1 : Nat)
    (hb : CB ⟨c :: c :: s, r, m, u, e⟩ = .ok ⟨b :: c :: s, r, m1, u, e1⟩) (h : HChain m1 b H) :
    loopThread (hashOutCode CB) ⟨c :: s, r, m, u, e⟩ = .ok ⟨s, r, hunlinkM m1 c b H, u, e1⟩ := by
  have hr := hash_out_run CB c s r u e1 H b m1 0 h
  refine loopThread_eq _ _ (hashOutFuel c H + 0 + 1 + 1) _ ?_ (by simp [outOfFuel])
  simp [run, hashOutCode, Prim.dup, hb]
  simpa using hr

theorem hash_out_eq (c b : Cell) (H s r : List Cell) (m m1 : Mem) (u : Cell) (e e1 : Nat)
    (hb : Words.«conn-bucket» ⟨c :: c :: s, r, m, u, e⟩ = .ok ⟨b :: c :: s, r, m1, u, e1⟩)
    (h : HChain m1 b H) :
    Words.«hash-out» ⟨c :: s, r, m, u, e⟩ = .ok ⟨s, r, hunlinkM m1 c b H, u, e1⟩ := by
  rw [show Words.«hash-out» = loopThread (hashOutCode Words.«conn-bucket») from rfl]
  exact hash_out_gen _ c b H s r m m1 u e e1 hb h

/-- A store apart from every cell of a bucket's list leaves the list. -/
theorem hchain_wr (q v : Cell) : ∀ (ys : List Cell) (b : Cell) (m : Mem),
    HChain m b ys → (∀ y ∈ b :: ys.map (· + 152), Apart q y) → HChain (wr m q 8 v) b ys := by
  intro ys
  induction ys with
  | nil =>
    intro b m h hq
    have hb := hq b (by simp)
    simp only [HChain] at h ⊢
    rw [rd_wr_other m q b v hb.2 hb.1]; exact h
  | cons y ys ih =>
    intro b m h hq
    obtain ⟨hy, hy0, hc⟩ := h
    have hb := hq b (by simp)
    refine ⟨by rw [rd_wr_other m q b v hb.2 hb.1]; exact hy, hy0, ?_⟩
    exact ih (y + 152) m hc fun z hz => hq z (List.mem_cons_of_mem b hz)

/-- `hash-out` stores only into a cell of the bucket's list. -/
theorem hunlinkM_rd (m : Mem) (c a : Cell) : ∀ (xs : List Cell) (b : Cell),
    (∀ y ∈ b :: xs.map (· + 152), Apart a y) → rd (hunlinkM m c b xs) a 8 = rd m a 8 := by
  intro xs
  induction xs with
  | nil => intro b _; rfl
  | cons y ys ih =>
    intro b hb
    simp only [hunlinkM]
    split
    · have h := hb b (by simp)
      exact rd_wr_other m b a _ h.1 h.2
    · exact ih (y + 152) fun z hz => hb z (List.mem_cons_of_mem b hz)

/-- `hash-out` takes c out of its bucket: what is left is the bucket without
it, provided the bucket's cells are apart. -/
theorem hunlink_chain (c : Cell) : ∀ (xs : List Cell) (a : Cell) (m : Mem),
    HChain m a xs → (a :: xs.map (· + 152)).Pairwise Apart → c ∈ xs →
      HChain (hunlinkM m c a xs) a (xs.erase c) := by
  intro xs
  induction xs with
  | nil => intro a m _ _ hc; simp at hc
  | cons x xs ih =>
    intro a m h hp hc
    obtain ⟨hx, hx0, hch⟩ := h
    simp only [List.map_cons] at hp
    have hpa := List.pairwise_cons.mp hp
    by_cases hxc : x = c
    · subst hxc
      simp only [hunlinkM, if_true, List.erase_cons_head]
      cases xs with
      | nil =>
        simp only [HChain] at hch ⊢
        rw [hch, rd_wr_same]
      | cons y ys =>
        obtain ⟨hy, hy0, hrest⟩ := hch
        refine ⟨by rw [hy, rd_wr_same], hy0, ?_⟩
        apply hchain_wr a _ ys (y + 152) m hrest
        intro z hz
        exact hpa.1 z (List.mem_cons_of_mem _ (by simpa using hz))
    · have hc' : c ∈ xs := (List.mem_cons.mp hc).resolve_left fun h => hxc h.symm
      simp only [hunlinkM, if_neg hxc]
      rw [show (x :: xs).erase c = x :: xs.erase c by simp [List.erase_cons, hxc]]
      have hrec := ih (x + 152) m hch (List.pairwise_cons.mp hp).2 hc'
      refine ⟨?_, hx0, hrec⟩
      rw [hunlinkM_rd m c a xs (x + 152) hpa.1]
      exact hx

/-- `hash-out` leaves any chain of `c.link` cells apart from its own cells. -/
theorem chain_hunlinkM (m : Mem) (c b0 : Cell) (ys : List Cell) :
    ∀ (H : List Cell) (a : Cell), Chain m b0 ys →
      (∀ q ∈ a :: H.map (· + 152), ∀ y ∈ b0 :: ys, Apart q y) → Chain (hunlinkM m c a H) b0 ys := by
  intro H
  induction H with
  | nil => intro a h _; exact h
  | cons x xs ih =>
    intro a h hq
    simp only [hunlinkM]
    split
    · exact chain_wr a _ ys b0 m h (hq a (by simp))
    · exact ih (x + 152) h fun q hq' y hy => hq q (List.mem_cons_of_mem a hq') y hy

/-- The hash cells a walk may store into: the bucket's own cell and the hash
links of the connections in it, each apart from the pool's link cells. -/
def HashApart (b : Cell) (H L F : List Cell) : Prop :=
  ∀ q ∈ b :: H.map (· + 152), Apart q connsV ∧ Apart q freeV ∧ ∀ y ∈ L ++ F, Apart q y

/-- `hash-out` keeps the pool. -/
theorem pool_hunlinkM (m : Mem) (c b : Cell) (H L F : List Cell) (hp : Pool m L F)
    (ha : HashApart b H L F) : Pool (hunlinkM m c b H) L F := by
  obtain ⟨hl, hf, hh, hlv, hfv, hlp, hfp, hx⟩ := hp
  refine ⟨?_, ?_, hh, hlv, hfv, hlp, hfp, hx⟩
  · apply chain_hunlinkM m c connsV L H b hl
    intro q hq y hy
    rcases List.mem_cons.mp hy with hy1 | hy2
    · rw [hy1]; exact (ha q hq).1
    · exact (ha q hq).2.2 y (List.mem_append_left F hy2)
  · apply chain_hunlinkM m c freeV F H b hf
    intro q hq y hy
    rcases List.mem_cons.mp hy with hy1 | hy2
    · rw [hy1]; exact (ha q hq).2.1
    · exact (ha q hq).2.2 y (List.mem_append_right L hy2)

/-- **The pool step (H-pool, closing):** `(free-conn)` on a live connection c,
whose bucket (where `conn-bucket` says, b) holds the list H, returns and
moves c from the live list to the free list: the pool stays whole, and live
plus free is what it was. Assumed here: `conn-bucket`'s own stores (its
scratch `tuple` and SipHash state) miss the pool (`hp1`), and the bucket's
cells are apart from the pool's (`ha`). -/
theorem free_conn_step (c b : Cell) (H L F s r : List Cell) (m m1 : Mem) (u : Cell) (e e1 : Nat)
    (hb : Words.«conn-bucket» ⟨c :: c :: c :: s, r, m, u, e⟩ = .ok ⟨b :: c :: c :: s, r, m1, u, e1⟩)
    (hH : HChain m1 b H) (hp1 : Pool m1 L F) (ha : HashApart b H L F) (hc : c ∈ L) :
    ∃ m', Words.«(free-conn)» ⟨c :: s, r, m, u, e⟩ = .ok ⟨s, r, m', u, e1⟩ ∧
      Pool m' (L.erase c) (c :: F) ∧
      (L.erase c).length + (c :: F).length = L.length + F.length := by
  have hho := hash_out_eq c b H (c :: s) r m m1 u e e1 hb hH
  have hp2 := pool_hunlinkM m1 c b H L F hp1 ha
  refine ⟨freeConnM (hunlinkM m1 c b H) c L, ?_, free_conn_pool _ c L F hp2 hc,
    free_conn_count L F c hc⟩
  exact free_conn_eq c L s r m (hunlinkM m1 c b H) u e e1 hho hp2.live

/-! ## A new connection

`new-conn` takes the first connection off the free list (or reserves one when
the list is empty), clears its header, and puts it on the live list. -/

/-- A chain survives a move of its head cell, and any memory that keeps its
connections' link cells. -/
theorem chain_move (m m' : Mem) : ∀ (ys : List Cell) (a a' : Cell), rd m' a' 8 = rd m a 8 →
    (∀ z ∈ ys, rd m' z 8 = rd m z 8) → Chain m a ys → Chain m' a' ys := by
  intro ys
  induction ys with
  | nil =>
    intro a a' ha _ h
    simp only [Chain] at h ⊢
    rw [ha]; exact h
  | cons y ys ih =>
    intro a a' ha hz h
    obtain ⟨hy, hy0, hc⟩ := h
    exact ⟨by rw [ha]; exact hy, hy0,
      ih y y (hz y (by simp)) (fun z hz' => hz z (List.mem_cons_of_mem y hz')) hc⟩

/-- A connection record (its 200-byte header at x) apart from the cell at y. -/
def Away (x y : Cell) : Prop := 200#64 ≤ y - x ∧ 8#64 ≤ x - y

/-- `new-conn`'s thread, with `reserve` left as RS. -/
noncomputable def newConnCode (RS : Sem) : List Ins := [.call Words.«free-conns», .call Prim.fetch,
  .call Words.«?dup», .zbranch 10, .call Prim.dup, .call Words.«c.link», .call Prim.fetch,
  .call Words.«free-conns», .call Prim.store, .branch 12, .call Words.«/conn», .call RS, .call Prim.dup,
  .call Words.«/conn-header», .lit 0, .call Prim.fill, .call Words.«base-rto», .call Prim.over,
  .call Words.«c.rto», .call Prim.store, .call Words.«conns», .call Prim.fetch, .call Prim.over,
  .call Words.«c.link», .call Prim.store, .call Prim.dup, .call Words.«conns», .call Prim.store, .exit]

theorem newConnCode_eq : Words.«new-conn».code = newConnCode Words.«reserve» := rfl

/-- `new-conn`'s memory up to the header: x off the free list, cleared, its
retransmission timeout set. -/
def newConnM3 (m : Mem) (x : Cell) : Mem :=
  wr (Prim.fillM 200 (wr m freeV 8 (rd m x 8)) x 0) (x + 112#64) 8 1000#64

/-- Then x on the live list. -/
def newConnM (m : Mem) (x : Cell) : Mem :=
  wr (wr (newConnM3 m x) x 8 (rd (newConnM3 m x) connsV 8)) connsV 8 x

set_option maxHeartbeats 4000000 in
/-- `new-conn` with a recycled connection x at the head of the free list. -/
theorem new_conn_eq (x : Cell) (s r : List Cell) (m : Mem) (u : Cell) (e : Nat)
    (hx : rd m (wordAddr "free-conns" + 8#64) 8 = x) (hx0 : x ≠ 0) :
    Words.«new-conn» ⟨s, r, m, u, e⟩ = .ok ⟨x :: s, r, newConnM m x, u, e⟩ := by
  have hx0' : ¬ x = 0#64 := hx0
  rw [show Words.«new-conn» = thread (newConnCode Words.«reserve») from rfl]
  generalize Words.«reserve» = RS
  simp [forth, newConnCode, newConnM, newConnM3, hx, hx0']

/-- The header's stores (the clearing and the timeout) leave a cell the
record is away from. -/
theorem header_rd (m1 : Mem) (x z : Cell) (h : Away x z) :
    rd (wr (Prim.fillM 200 m1 x 0) (x + 112#64) 8 1000#64) z 8 = rd m1 z 8 := by
  obtain ⟨h1, h2⟩ := h
  rw [rd_wr_other _ _ _ _ (by bv_omega) (by bv_omega)]
  apply rd_congr
  intro i hi
  apply fillM_other
  intro j hj hij
  have hi' : (BitVec.ofNat 64 i).toNat = i := by simp; omega
  have hj' : (BitVec.ofNat 64 j).toNat = j := by simp; omega
  bv_omega

theorem newConnM3_rd (m : Mem) (x z : Cell) (h1 : Apart freeV z) (h2 : Away x z) :
    rd (newConnM3 m x) z 8 = rd m z 8 := by
  unfold newConnM3
  rw [header_rd _ x z h2, rd_wr_other _ _ _ _ h1.2 h1.1]

theorem newConnM_rd (m : Mem) (x z : Cell) (h1 : Apart freeV z) (h2 : Away x z)
    (h3 : Apart connsV z) : rd (newConnM m x) z 8 = rd m z 8 := by
  unfold newConnM
  rw [rd_wr_other _ _ _ _ h3.2 h3.1, rd_wr_other _ _ _ _ (by obtain ⟨a, b⟩ := h2; bv_omega)
    (by obtain ⟨a, b⟩ := h2; bv_omega)]
  exact newConnM3_rd m x z h1 h2

/-- **The pool step (H-pool, opening):** `new-conn` with x first on the free
list moves x to the live list, keeping the pool whole: live plus free is
what it was. Assumed: x's header is apart from the pool's other link cells
(`hfar`, which a pool of disjoint records gives). -/
theorem new_conn_pool (m : Mem) (x : Cell) (L F : List Cell) (hp : Pool m L (x :: F))
    (hfar : Away x connsV ∧ Away x freeV ∧ ∀ y ∈ L ++ F, Away x y) :
    Pool (newConnM m x) (x :: L) F ∧ (x :: L).length + F.length = L.length + (x :: F).length := by
  obtain ⟨hl, hf, hh, hlv, hfv, hlp, hfp, hx⟩ := hp
  obtain ⟨hxv, hx0, hxF⟩ := hf
  obtain ⟨hfc, hff, hfy⟩ := hfar
  have hxa := hfv x (by simp)
  have hfpa := List.pairwise_cons.mp hfp
  -- a cell the stores leave
  have keep : ∀ z, Apart freeV z → Away x z → Apart connsV z → rd (newConnM m x) z 8 = rd m z 8 :=
    fun z h1 h2 h3 => newConnM_rd m x z h1 h2 h3
  refine ⟨⟨?_, ?_, hh, ?_, ?_, ?_, hfpa.2, ?_⟩, by simp only [List.length_cons]; omega⟩
  · -- live: x, then the old live list
    refine ⟨?_, hx0, ?_⟩
    · unfold newConnM; exact rd_wr_same _ _ _
    · apply chain_move m _ L connsV x
      · unfold newConnM
        rw [rd_wr_other _ _ _ _ hxa.1.2 hxa.1.1, rd_wr_same]
        exact newConnM3_rd m x connsV ⟨hh.2, hh.1⟩ hfc
      · intro z hz
        exact keep z (hlv z hz).2 (hfy z (List.mem_append_left F hz)) (hlv z hz).1
      · exact hl
  · -- free: the rest of the old free list
    apply chain_move m _ F x freeV
    · unfold newConnM
      rw [rd_wr_other _ _ _ _ hh.2 hh.1, rd_wr_other _ _ _ _ hxa.2.1 hxa.2.2]
      unfold newConnM3
      rw [header_rd _ x freeV hff, rd_wr_same]
    · intro z hz
      have hz' : z ∈ x :: F := List.mem_cons_of_mem x hz
      exact keep z (hfv z hz').2 (hfy z (List.mem_append_right L hz)) (hfv z hz').1
    · exact hxF
  · intro y hy
    rcases List.mem_cons.mp hy with hy1 | hy2
    · rw [hy1]; exact hxa
    · exact hlv y hy2
  · intro y hy
    exact hfv y (List.mem_cons_of_mem x hy)
  · refine List.pairwise_cons.mpr ⟨fun y hy => ?_, hlp⟩
    have h2 := hx y hy x (by simp)
    exact ⟨h2.2, h2.1⟩
  · intro a ha b hb
    rcases List.mem_cons.mp ha with ha1 | ha2
    · rw [ha1]; exact hfpa.1 b hb
    · exact hx a ha2 b (List.mem_cons_of_mem x hb)

end OS4.Pools
