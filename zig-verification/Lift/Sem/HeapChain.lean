module

public import Lift.Sem.Heap

@[expose] public section

namespace Lift.Sem

open Lift.P2.Total

/-- The pointers of the walk from `p` over the words at `p + off`, with the fuel `n`: `p`, then the word at `p + off`,
and so on. The walk stops at a pointer `0`, when the fuel is `0`, or after a pointer whose word at `p + off` is not an
`.ok` load. -/
def Heap.chainFuel (h : Heap) (off : Nat) : Nat → BitVec 64 → List (BitVec 64)
  | 0, _ => []
  | n + 1, p =>
    if p = 0 then [] else
    match h.load (p + BitVec.ofNat 64 off) .W64 with
    | .ok q => p :: Heap.chainFuel h off n q
    | _ => [p]

/-- The pointers of the walk from `p` over the words at `p + off` (the `next` word of a node is at `off`): the pointer
values that `while p ≠ 0 do p := load (p + off)` takes. The fuel is the number of objects of `h`. -/
def Heap.chain (h : Heap) (off : Nat) : BitVec 64 → List (BitVec 64) :=
  Heap.chainFuel h off h.length

/-- The walk from `p` over the words at `p + off` reaches the pointer `0` within the fuel `n`, and each load on the way is
`.ok`. The test of `p = 0` takes no fuel. -/
def Heap.endsFuel (h : Heap) (off : Nat) : Nat → BitVec 64 → Bool
  | 0, p => p = 0
  | n + 1, p =>
    if p = 0 then true else
    match h.load (p + BitVec.ofNat 64 off) .W64 with
    | .ok q => Heap.endsFuel h off n q
    | _ => false

/-- The walk from `p` reaches `0` within the fuel of `Heap.chain` (the number of objects of `h`), with each load `.ok`.
Then `Heap.chain h off p` is the list of the pointers before `0`, and a step of the walk removes its head
(`Heap.chain_next`). -/
def Heap.ends (h : Heap) (off : Nat) (p : BitVec 64) : Bool :=
  Heap.endsFuel h off h.length p

/-- The word at `p + off`, if its load is `.ok`, else `0`: the next pointer of the walk. -/
def Heap.nextOf (h : Heap) (off : Nat) (p : BitVec 64) : BitVec 64 :=
  match h.load (p + BitVec.ofNat 64 off) .W64 with
  | .ok q => q
  | _ => 0

/-- Each object of `os` has the address of `ps` at its index and, at `off`, the word of the next address of `ps` (the
last one `0`): the objects of a list of nodes, read from `ps.headD 0`. -/
def Heap.Linked (off : Nat) : List Obj → List (BitVec 64) → Prop
  | [], [] => True
  | o :: os, p :: ps => o.addr = p ∧ o.get (p + BitVec.ofNat 64 off) .W64 = some (ps.headD 0) ∧ Heap.Linked off os ps
  | _, _ => False

instance Heap.instDecidableLinked (off : Nat) : ∀ os ps, Decidable (Heap.Linked off os ps)
  | [], [] => isTrue trivial
  | o :: os, p :: ps =>
    have := Heap.instDecidableLinked off os ps
    inferInstanceAs (Decidable (o.addr = p ∧ o.get (p + BitVec.ofNat 64 off) .W64 = some (ps.headD 0) ∧
      Heap.Linked off os ps))
  | [], _ :: _ => isFalse id
  | _ :: _, [] => isFalse id

theorem Heap.chainFuel_zero_ptr (h : Heap) (off n : Nat) : Heap.chainFuel h off n 0 = [] := by
  cases n <;> simp [Heap.chainFuel]

theorem Heap.chain_zero (h : Heap) (off : Nat) : Heap.chain h off 0 = [] :=
  Heap.chainFuel_zero_ptr h off h.length

theorem Heap.endsFuel_zero_ptr (h : Heap) (off n : Nat) : Heap.endsFuel h off n 0 = true := by
  cases n <;> simp [Heap.endsFuel]

/-- The walk from the null pointer ends. -/
theorem Heap.ends_zero (h : Heap) (off : Nat) : Heap.ends h off 0 = true :=
  Heap.endsFuel_zero_ptr h off h.length

/-- A walk that ends within the fuel `n` ends within more fuel, with the same pointers. -/
theorem Heap.endsFuel_mono {h : Heap} {off : Nat} :
    ∀ {n m : Nat} {p : BitVec 64}, Heap.endsFuel h off n p = true → n ≤ m →
      Heap.endsFuel h off m p = true ∧ Heap.chainFuel h off m p = Heap.chainFuel h off n p
  | 0, m, p, he, _ => by
    have hp : p = 0 := by simpa [Heap.endsFuel] using he
    subst hp
    exact ⟨Heap.endsFuel_zero_ptr .., by rw [Heap.chainFuel_zero_ptr, Heap.chainFuel_zero_ptr]⟩
  | n + 1, 0, p, _, hm => absurd hm (by omega)
  | n + 1, m + 1, p, he, hm => by
    by_cases hp : p = 0
    · subst hp
      exact ⟨Heap.endsFuel_zero_ptr .., by rw [Heap.chainFuel_zero_ptr, Heap.chainFuel_zero_ptr]⟩
    · simp only [Heap.endsFuel, hp, ↓reduceIte] at he
      split at he
      · rename_i q hl
        obtain ⟨e₁, e₂⟩ := Heap.endsFuel_mono (m := m) he (by omega)
        simp only [Heap.endsFuel, Heap.chainFuel, hp, ↓reduceIte, hl, e₁, e₂, and_self]
      · cases he

/-- One step of a walk that ends: the load at `p + off` is `.ok`, the chain is `p` and the chain from the next pointer,
and the walk from the next pointer ends. -/
theorem Heap.ends_step {h : Heap} {off : Nat} {p : BitVec 64} (he : Heap.ends h off p = true) (hp : p ≠ 0) :
    h.load (p + BitVec.ofNat 64 off) .W64 = .ok (Heap.nextOf h off p) ∧
      Heap.chain h off p = p :: Heap.chain h off (Heap.nextOf h off p) ∧
      Heap.ends h off (Heap.nextOf h off p) = true := by
  unfold Heap.ends at he
  unfold Heap.chain Heap.ends
  generalize h.length = n at he ⊢
  cases n with
  | zero => exact absurd (by simpa [Heap.endsFuel] using he) hp
  | succ n =>
    simp only [Heap.endsFuel, hp, ↓reduceIte] at he
    split at he
    · rename_i q hl
      have hq : Heap.nextOf h off p = q := by simp [Heap.nextOf, hl]
      obtain ⟨e₁, e₂⟩ := Heap.endsFuel_mono (m := n + 1) he (by omega)
      have hc : Heap.chainFuel h off (n + 1) p = p :: Heap.chainFuel h off n q := by
        simp only [Heap.chainFuel, hp, ↓reduceIte, hl]
      rw [hq]
      exact ⟨hl, by rw [hc, e₂], e₁⟩
    · cases he

/-- The load of the next word of a walk that ends, for `simp`. The pointer is a register value (`UInt64.ofBitVec p`). -/
theorem Heap.load_next_of_ends {h : Heap} {off : Nat} {p : BitVec 64} (he : Heap.ends h off p = true)
    (hp : ¬ UInt64.ofBitVec p = 0) : h.load (p + BitVec.ofNat 64 off) .W64 = .ok (Heap.nextOf h off p) :=
  (Heap.ends_step he fun e => hp (by rw [e]; rfl)).1

/-- `Heap.load_next_of_ends` with the offset as a word `c` (a literal of the code, such as `8`). -/
theorem Heap.load_next_of_ends' {h : Heap} {off : Nat} {p c : BitVec 64} (he : Heap.ends h off p = true)
    (hp : ¬ UInt64.ofBitVec p = 0) (hc : BitVec.ofNat 64 off = c) :
    h.load (p + c) .W64 = .ok (Heap.nextOf h off p) :=
  hc ▸ Heap.load_next_of_ends he hp

theorem Heap.chain_ofNat_zero (h : Heap) (off : Nat) : Heap.chain h off (BitVec.ofNat 64 0) = [] :=
  Heap.chain_zero h off

/-- The chain of a walk that ends, for `simp`: its head and the chain from the next pointer. -/
theorem Heap.chain_next {h : Heap} {off : Nat} {p : BitVec 64} (he : Heap.ends h off p = true)
    (hp : ¬ UInt64.ofBitVec p = 0) : Heap.chain h off p = p :: Heap.chain h off (Heap.nextOf h off p) :=
  (Heap.ends_step he fun e => hp (by rw [e]; rfl)).2.1

/-- The walk from the next pointer of a walk that ends ends, for `simp`. -/
theorem Heap.ends_next {h : Heap} {off : Nat} {p : BitVec 64} (he : Heap.ends h off p = true)
    (hp : ¬ UInt64.ofBitVec p = 0) : Heap.ends h off (Heap.nextOf h off p) = true :=
  (Heap.ends_step he fun e => hp (by rw [e]; rfl)).2.2

/-- The walk over linked objects of a heap that a memory holds: from the first address it gives the addresses, and it
ends, for each fuel that is at least the number of objects. -/
theorem Heap.chainFuel_of_linked {policy : CpuPolicy} {h : Heap} {m : DataMem} {off : Nat} (hh : h.Holds policy m) :
    ∀ {os : List Obj} {ps : List (BitVec 64)} {n : Nat}, (∀ o ∈ os, o ∈ h) → Heap.Linked off os ps →
      (∀ p ∈ ps, p ≠ 0) → ps.length ≤ n →
      Heap.chainFuel h off n (ps.headD 0) = ps ∧ Heap.endsFuel h off n (ps.headD 0) = true
  | [], [], n, _, _, _, _ => ⟨Heap.chainFuel_zero_ptr .., Heap.endsFuel_zero_ptr ..⟩
  | o :: os, p :: ps, n + 1, hs, ⟨ha, hg, hl⟩, hne, hn => by
    have hp : p ≠ 0 := hne p (List.mem_cons_self ..)
    have hload : h.load (p + BitVec.ofNat 64 off) .W64 = .ok (ps.headD 0) := by
      obtain ⟨x, hx, hax, hc⟩ := Obj.get_some hg
      have := Heap.load_of_mem hh (hs o (List.mem_cons_self ..)) hx
      rw [hax, hc] at this
      exact this
    obtain ⟨e₁, e₂⟩ := Heap.chainFuel_of_linked hh (fun o' ho' => hs o' (List.mem_cons_of_mem _ ho')) hl
      (fun q hq => hne q (List.mem_cons_of_mem _ hq)) (n := n) (by simp at hn; omega)
    simp only [List.headD_cons, Heap.chainFuel, Heap.endsFuel, hp, ↓reduceIte, hload, e₁, e₂, and_self]
  | _ :: _, p :: ps, 0, _, _, _, hn => by simp at hn
  | [], _ :: _, _, _, hl, _, _ => hl.elim
  | _ :: _, [], _, _, hl, _, _ => hl.elim

/-- The chain from the first address of linked objects at the front of a heap that a memory holds: the addresses, and the
walk ends. -/
theorem Heap.chain_of_linked {policy : CpuPolicy} {os frame : Heap} {m : DataMem} {off : Nat} {ps : List (BitVec 64)}
    (hh : (os ++ frame).Holds policy m) (hl : Heap.Linked off os ps) (hne : ∀ p ∈ ps, p ≠ 0) :
    Heap.chain (os ++ frame) off (ps.headD 0) = ps ∧ Heap.ends (os ++ frame) off (ps.headD 0) = true := by
  have hlen : ps.length = os.length := by
    clear hh hne
    induction os generalizing ps with
    | nil => cases ps <;> simp_all [Heap.Linked]
    | cons o os ih => cases ps <;> simp_all [Heap.Linked]
  exact Heap.chainFuel_of_linked hh (fun o ho => List.mem_append_left _ ho) hl hne (by simp; omega)

/-! ## The values of the nodes of a chain (AF2-C)

A loop that reads the value word of each node (`sum += p.val; p = p.next`) has, besides the `next` word at `off`, a value word at
`voff`. `Heap.chainVals` is the list of the value words of the nodes of the chain, and `Heap.endsV` says that the walk ends and
that each load of a value word is `.ok`. -/

/-- The load of the word at `q + voff` is `.ok`. -/
def Heap.valsOk (h : Heap) (voff : Nat) (q : BitVec 64) : Bool :=
  match h.load (q + BitVec.ofNat 64 voff) .W64 with
  | .ok _ => true
  | _ => false

/-- The walk from `p` over the words at `p + off` ends (`Heap.ends`), and the load of the word at `q + voff` is `.ok` for each
pointer `q` of the chain. -/
def Heap.endsV (h : Heap) (off voff : Nat) (p : BitVec 64) : Bool :=
  Heap.ends h off p && (Heap.chain h off p).all (Heap.valsOk h voff)

/-- The value words of the nodes of the chain from `p`: the word at `q + voff` (`Heap.nextOf h voff q`) of each pointer `q`. -/
def Heap.chainVals (h : Heap) (off voff : Nat) (p : BitVec 64) : List (BitVec 64) :=
  (Heap.chain h off p).map (Heap.nextOf h voff)

/-- One step of a walk with values: the load of the value word at `p + voff` is `.ok`, and the walk from the next pointer
ends with values. -/
theorem Heap.endsV_step {h : Heap} {off voff : Nat} {p : BitVec 64} (he : Heap.endsV h off voff p = true) (hp : p ≠ 0) :
    h.load (p + BitVec.ofNat 64 voff) .W64 = .ok (Heap.nextOf h voff p) ∧
      Heap.endsV h off voff (Heap.nextOf h off p) = true := by
  unfold Heap.endsV at he ⊢
  rw [Bool.and_eq_true] at he ⊢
  obtain ⟨he₁, he₂⟩ := he
  obtain ⟨-, hc, hn⟩ := Heap.ends_step he₁ hp
  rw [hc, List.all_cons, Bool.and_eq_true] at he₂
  obtain ⟨hv, hrest⟩ := he₂
  have hl : ∃ v, h.load (p + BitVec.ofNat 64 voff) .W64 = .ok v := by
    unfold Heap.valsOk at hv
    split at hv
    · rename_i v hl
      exact ⟨v, hl⟩
    · cases hv
  obtain ⟨v, hl⟩ := hl
  refine ⟨by simp [Heap.nextOf, hl], hn, hrest⟩

/-- The load of the value word of a walk with values, for `simp`. The pointer is a register value (`UInt64.ofBitVec p`), and
the offset is a word `c` of the code. -/
theorem Heap.load_val_of_endsV {h : Heap} {off voff : Nat} {p c : BitVec 64} (he : Heap.endsV h off voff p = true)
    (hp : ¬ UInt64.ofBitVec p = 0) (hc : BitVec.ofNat 64 voff = c) : h.load (p + c) .W64 = .ok (Heap.nextOf h voff p) :=
  hc ▸ (Heap.endsV_step he fun e => hp (by rw [e]; rfl)).1

/-- The load of the value word at the offset `0`: the address is the pointer `p`, with no `+`. -/
theorem Heap.load_val_of_endsV_zero {h : Heap} {off : Nat} {p : BitVec 64} (he : Heap.endsV h off 0 p = true)
    (hp : ¬ UInt64.ofBitVec p = 0) : h.load p .W64 = .ok (Heap.nextOf h 0 p) := by
  have e := Heap.load_val_of_endsV he hp (c := BitVec.ofNat 64 0) rfl
  have h0 : p + BitVec.ofNat 64 0 = p := BitVec.add_zero p
  rwa [h0] at e

/-- The walk from the next pointer of a walk with values ends with values, for `simp`. -/
theorem Heap.endsV_next {h : Heap} {off voff : Nat} {p : BitVec 64} (he : Heap.endsV h off voff p = true)
    (hp : ¬ UInt64.ofBitVec p = 0) : Heap.endsV h off voff (Heap.nextOf h off p) = true :=
  (Heap.endsV_step he fun e => hp (by rw [e]; rfl)).2

/-- The values of a chain that ends, for `simp`: the value of the head and the values of the chain from the next pointer. -/
theorem Heap.chainVals_next {h : Heap} {off voff : Nat} {p : BitVec 64} (he : Heap.ends h off p = true)
    (hp : ¬ UInt64.ofBitVec p = 0) :
    Heap.chainVals h off voff p = Heap.nextOf h voff p :: Heap.chainVals h off voff (Heap.nextOf h off p) := by
  unfold Heap.chainVals
  rw [Heap.chain_next he hp, List.map_cons]

theorem Heap.chainVals_zero (h : Heap) (off voff : Nat) : Heap.chainVals h off voff 0 = [] := by
  unfold Heap.chainVals
  rw [Heap.chain_zero]
  rfl

theorem Heap.chainVals_ofNat_zero (h : Heap) (off voff : Nat) : Heap.chainVals h off voff (BitVec.ofNat 64 0) = [] :=
  Heap.chainVals_zero h off voff

/-- Each object of `os` has, at `voff`, the word of the value at its index. -/
def Heap.LinkedVals (voff : Nat) : List Obj → List (BitVec 64) → List (BitVec 64) → Prop
  | [], [], [] => True
  | o :: os, p :: ps, v :: vs => o.get (p + BitVec.ofNat 64 voff) .W64 = some v ∧ Heap.LinkedVals voff os ps vs
  | _, _, _ => False

/-- The values of linked objects of a heap that a memory holds: the value words of the addresses `ps` are `vs`, and each
load of a value word is `.ok`. -/
theorem Heap.vals_of_linked {policy : CpuPolicy} {h : Heap} {m : DataMem} {voff : Nat} (hh : h.Holds policy m) :
    ∀ {os : List Obj} {ps vs : List (BitVec 64)}, (∀ o ∈ os, o ∈ h) → Heap.LinkedVals voff os ps vs →
      (∀ q ∈ ps, Heap.valsOk h voff q = true) ∧ ps.map (Heap.nextOf h voff) = vs
  | [], [], [], _, _ => ⟨by simp, rfl⟩
  | o :: os, p :: ps, v :: vs, hs, ⟨hg, hl⟩ => by
    have hload : h.load (p + BitVec.ofNat 64 voff) .W64 = .ok v := by
      obtain ⟨x, hx, hax, hc⟩ := Obj.get_some hg
      have := Heap.load_of_mem hh (hs o (List.mem_cons_self ..)) hx
      rw [hax, hc] at this
      exact this
    obtain ⟨r₁, r₂⟩ := Heap.vals_of_linked hh (fun o' ho' => hs o' (List.mem_cons_of_mem _ ho')) hl
    refine ⟨?_, ?_⟩
    · intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · simp [Heap.valsOk, hload]
      · exact r₁ q hq
    · simp [List.map_cons, Heap.nextOf, hload, r₂]
  | _ :: _, [], _, _, hl => hl.elim
  | _ :: _, _ :: _, [], _, hl => hl.elim
  | [], _ :: _, _, _, hl => hl.elim
  | [], [], _ :: _, _, hl => hl.elim

/-- The chain from the first address of linked objects at the front of a heap that a memory holds, with values: the addresses,
the walk ends (with and without the values), and the value words of the addresses are `vs`. -/
theorem Heap.chain_of_linked_v {policy : CpuPolicy} {os frame : Heap} {m : DataMem} {off voff : Nat}
    {ps vs : List (BitVec 64)} (hh : (os ++ frame).Holds policy m) (hl : Heap.Linked off os ps)
    (hv : Heap.LinkedVals voff os ps vs) (hne : ∀ p ∈ ps, p ≠ 0) :
    Heap.chain (os ++ frame) off (ps.headD 0) = ps ∧ Heap.ends (os ++ frame) off (ps.headD 0) = true ∧
      Heap.endsV (os ++ frame) off voff (ps.headD 0) = true ∧ ps.map (Heap.nextOf (os ++ frame) voff) = vs := by
  obtain ⟨hc, he⟩ := Heap.chain_of_linked hh hl hne
  obtain ⟨v₁, v₂⟩ := Heap.vals_of_linked hh (fun o ho => List.mem_append_left _ ho) hv
  refine ⟨hc, he, ?_, v₂⟩
  unfold Heap.endsV
  rw [Bool.and_eq_true, hc]
  exact ⟨he, List.all_eq_true.mpr v₁⟩

/-- Each pointer of the chain of a walk that ends is not `0`, starts a walk that ends, and its chain is a suffix of the
chain. The chain has at most `n` pointers. -/
theorem Heap.mem_chain_closed {h : Heap} {off : Nat} :
    ∀ (n : Nat) {q : BitVec 64}, (Heap.chain h off q).length ≤ n → Heap.ends h off q = true →
      ∀ p ∈ Heap.chain h off q, p ≠ 0 ∧ Heap.ends h off p = true ∧
        (Heap.chain h off p).IsSuffix (Heap.chain h off q) := by
  intro n
  induction n with
  | zero =>
    intro q hn _ p hp
    have : Heap.chain h off q = [] := List.length_eq_zero_iff.mp (by omega)
    rw [this] at hp
    exact absurd hp (by simp)
  | succ n ih =>
    intro q hn he p hp
    by_cases hq : q = 0
    · subst hq
      rw [Heap.chain_zero] at hp
      exact absurd hp (by simp)
    · obtain ⟨_, hc, he'⟩ := Heap.ends_step he hq
      rw [hc] at hp hn
      rcases List.mem_cons.mp hp with rfl | hp'
      · exact ⟨hq, he, by rw [hc]; exact List.suffix_refl _⟩
      · obtain ⟨e₀, e₁, e₂⟩ := ih (by simp at hn; omega) he' p hp'
        exact ⟨e₀, e₁, by rw [hc]; exact e₂.trans (List.suffix_cons _ _)⟩

/-- A pointer of the chain of a walk that ends starts a walk that ends. -/
theorem Heap.ends_of_mem_chain {h : Heap} {off : Nat} {q p : BitVec 64} (he : Heap.ends h off q = true)
    (hp : p ∈ Heap.chain h off q) : Heap.ends h off p = true :=
  (Heap.mem_chain_closed _ (Nat.le_refl _) he p hp).2.1

/-- The next pointer of a pointer of the chain of a walk that ends is `0` or a pointer of the chain. -/
theorem Heap.next_mem_chain_or_zero {h : Heap} {off : Nat} {q p : BitVec 64} (he : Heap.ends h off q = true)
    (hp : p ∈ Heap.chain h off q) : Heap.nextOf h off p = 0 ∨ Heap.nextOf h off p ∈ Heap.chain h off q := by
  obtain ⟨hne, hep, hsuf⟩ := Heap.mem_chain_closed _ (Nat.le_refl _) he p hp
  obtain ⟨_, hc, he'⟩ := Heap.ends_step hep hne
  by_cases h0 : Heap.nextOf h off p = 0
  · exact Or.inl h0
  · right
    obtain ⟨_, hc2, _⟩ := Heap.ends_step he' h0
    have hm : Heap.nextOf h off p ∈ Heap.chain h off (Heap.nextOf h off p) := by
      rw [hc2]; exact List.mem_cons_self ..
    have hs : (Heap.chain h off (Heap.nextOf h off p)).IsSuffix (Heap.chain h off q) :=
      List.IsSuffix.trans (by rw [hc]; exact List.suffix_cons _ _) hsuf
    exact hs.subset hm

end Lift.Sem
