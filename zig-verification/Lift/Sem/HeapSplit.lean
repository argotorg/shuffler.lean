module

public import Lift.Sem.Split
public import Lift.Sem.HeapWF
public import Lift.Sem.HeapLemmas

@[expose] public section

/-! The split of one object of a typed heap into two adjacent objects, and the reorder of the
objects of a heap. An object with the cells `cs ++ ds` is the object of `cs` at its address and the
object of `ds` right after it. The split holds in both directions when the object does not wrap past
`2^64`; the join needs also that no other object has no byte at a point inside the object.
The lemmas about the cells (`offsets_append`) are the forms of `Lift.Sem.Split` for `Cell`. -/

namespace Lift.Sem

open Lift.P2.Total

/-! ### Cells -/

theorem offsets_append (n : Nat) (cs ds : List Cell) :
    offsets n (cs ++ ds) = offsets n cs ++ offsets (n + (cs.map fun c => c.w.bytes).sum) ds := by
  induction cs generalizing n with
  | nil => simp [offsets]
  | cons c cs ih =>
    simp only [List.cons_append, offsets, ih, List.map_cons, List.sum_cons, List.cons.injEq,
      true_and]
    congr 2
    omega

theorem offsets_shift (n k : Nat) (cs : List Cell) :
    offsets (n + k) cs = (offsets k cs).map fun x => (n + x.1, x.2) := by
  induction cs generalizing k with
  | nil => rfl
  | cons c cs ih =>
    simp only [offsets, List.map_cons, List.cons.injEq, true_and]
    rw [show n + k + c.w.bytes = n + (k + c.w.bytes) by omega, ih]

/-- A cell of the sequence `cs ++ ds` is a cell of `cs`, or a cell of `ds` shifted by the bytes
of `cs`. -/
theorem mem_offsets_append {cs ds : List Cell} {y : Nat × Cell} :
    y ∈ offsets 0 (cs ++ ds) ↔ y ∈ offsets 0 cs ∨
      ∃ x ∈ offsets 0 ds, y = ((cs.map fun c => c.w.bytes).sum + x.1, x.2) := by
  have e := offsets_shift (cs.map fun c => c.w.bytes).sum 0 ds
  rw [Nat.add_zero] at e
  rw [offsets_append, Nat.zero_add, e, List.mem_append, List.mem_map]
  exact or_congr_right ⟨fun ⟨x, hx, e⟩ => ⟨x, hx, e.symm⟩, fun ⟨x, hx, e⟩ => ⟨x, hx, e.symm⟩⟩

theorem Obj.size_append (a a' : BitVec 64) (wr wr' : Bool) (cs ds : List Cell) :
    (Obj.mk a wr (cs ++ ds)).size = (Obj.mk a wr cs).size + (Obj.mk a' wr' ds).size := by
  simp [Obj.size]

/-- The address `a + s₁` of the second part: the same as the address of the cell `s₁ + k`. -/
theorem add_ofNat_add (a : BitVec 64) (s k : Nat) :
    a + BitVec.ofNat 64 (s + k) = a + BitVec.ofNat 64 s + BitVec.ofNat 64 k := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]

/-- The address of the second part, as a natural number: `a + s₁`, or `0` when the second part
has no byte and the first ends at `2^64`. -/
theorem toNat_second (a : BitVec 64) (s₁ s₂ : Nat) (hw : a.toNat + (s₁ + s₂) ≤ 2 ^ 64) :
    (a + BitVec.ofNat 64 s₁).toNat = a.toNat + s₁ ∨ ((a + BitVec.ofNat 64 s₁).toNat = 0 ∧ s₂ = 0) := by
  rw [Split.toNat_add_ofNat]
  by_cases hl : a.toNat + s₁ < 2 ^ 64
  · exact .inl (Nat.mod_eq_of_lt hl)
  · have e : a.toNat + s₁ = 2 ^ 64 := by omega
    rw [e, Nat.mod_self]
    exact .inr ⟨rfl, by omega⟩

/-! ### Apart -/

theorem Obj.Apart.symm {o o' : Obj} (h : o.Apart o') : o'.Apart o := Or.symm h

/-- Two objects that are apart, or an object and a writable object. -/
def Obj.Sep (o o' : Obj) : Prop := (o.writable ∨ o'.writable) → o.Apart o'

theorem Obj.Sep.symm {o o' : Obj} (h : o.Sep o') : o'.Sep o := fun hw => (h (Or.symm hw)).symm

/-- A part of the object is apart from each object that the object is apart from. -/
theorem Obj.apart_parts {p : Obj} {a : BitVec 64} {wr : Bool} {cs ds : List Cell}
    (hw : a.toNat + (Obj.mk a wr (cs ++ ds)).size ≤ 2 ^ 64) (h : p.Apart ⟨a, wr, cs ++ ds⟩) :
    p.Apart ⟨a, wr, cs⟩ ∧ p.Apart ⟨a + BitVec.ofNat 64 (Obj.mk a wr cs).size, wr, ds⟩ := by
  have hs := Obj.size_append a (a + BitVec.ofNat 64 (Obj.mk a wr cs).size) wr wr cs ds
  rcases toNat_second a (Obj.mk a wr cs).size
      (Obj.mk (a + BitVec.ofNat 64 (Obj.mk a wr cs).size) wr ds).size (by omega) with h2 | ⟨h2, h0⟩
  · simp only [Obj.Apart, hs, h2] at h ⊢
    omega
  · simp only [Obj.Apart, hs, h2] at h ⊢
    omega

/-- An object with a byte that is apart from the two parts is apart from the object. -/
theorem Obj.apart_join {p : Obj} {a : BitVec 64} {wr : Bool} {cs ds : List Cell}
    (hw : a.toNat + (Obj.mk a wr (cs ++ ds)).size ≤ 2 ^ 64) (hp : 0 < p.size)
    (h₁ : p.Apart ⟨a, wr, cs⟩) (h₂ : p.Apart ⟨a + BitVec.ofNat 64 (Obj.mk a wr cs).size, wr, ds⟩) :
    p.Apart ⟨a, wr, cs ++ ds⟩ := by
  have hs := Obj.size_append a (a + BitVec.ofNat 64 (Obj.mk a wr cs).size) wr wr cs ds
  rcases toNat_second a (Obj.mk a wr cs).size
      (Obj.mk (a + BitVec.ofNat 64 (Obj.mk a wr cs).size) wr ds).size (by omega) with h2 | ⟨h2, h0⟩
  · simp only [Obj.Apart, hs, h2] at h₁ h₂ ⊢
    omega
  · simp only [Obj.Apart, hs, h2] at h₁ h₂ ⊢
    omega

/-- The two parts of a split have no byte in common. -/
theorem Obj.apart_split {a : BitVec 64} {wr : Bool} {cs ds : List Cell}
    (hw : a.toNat + (Obj.mk a wr (cs ++ ds)).size ≤ 2 ^ 64) :
    (Obj.mk a wr cs).Apart ⟨a + BitVec.ofNat 64 (Obj.mk a wr cs).size, wr, ds⟩ := by
  have hs := Obj.size_append a (a + BitVec.ofNat 64 (Obj.mk a wr cs).size) wr wr cs ds
  rcases toNat_second a (Obj.mk a wr cs).size
      (Obj.mk (a + BitVec.ofNat 64 (Obj.mk a wr cs).size) wr ds).size (by omega) with h2 | ⟨h2, h0⟩
  · simp only [Obj.Apart, h2]
    omega
  · simp only [Obj.Apart, h2]
    omega

/-! ### The list of the objects -/

/-- The objects before and after one object, when the object is replaced by two. -/
theorem pairwise_split_of {R : Obj → Obj → Prop} (hsym : ∀ {x y}, R x y → R y x)
    {pre post : Heap} {W O₁ O₂ : Obj} (hs : ∀ p, R p W → R p O₁ ∧ R p O₂) (h12 : R O₁ O₂)
    (h : (pre ++ W :: post).Pairwise R) : (pre ++ O₁ :: O₂ :: post).Pairwise R := by
  simp only [List.pairwise_append, List.pairwise_cons, List.mem_cons, forall_eq_or_imp] at h ⊢
  obtain ⟨hpre, ⟨hW, hpost⟩, hcross⟩ := h
  refine ⟨hpre, ⟨⟨h12, fun b hb => hsym (hs b (hsym (hW b hb))).1⟩,
    fun b hb => hsym (hs b (hsym (hW b hb))).2, hpost⟩, fun p hp => ⟨?_, ?_, fun b hb => ?_⟩⟩
  · exact (hs p (hcross p hp).1).1
  · exact (hs p (hcross p hp).1).2
  · exact (hcross p hp).2 b hb

theorem pairwise_join_of {R : Obj → Obj → Prop} (hsym : ∀ {x y}, R x y → R y x)
    {pre post : Heap} {W O₁ O₂ : Obj} (hj : ∀ p ∈ pre ++ post, R p O₁ → R p O₂ → R p W)
    (h : (pre ++ O₁ :: O₂ :: post).Pairwise R) : (pre ++ W :: post).Pairwise R := by
  simp only [List.pairwise_append, List.pairwise_cons, List.mem_cons, forall_eq_or_imp] at h ⊢
  obtain ⟨hpre, ⟨⟨_, h1⟩, h2, hpost⟩, hcross⟩ := h
  refine ⟨hpre, ⟨fun b hb => hsym (hj b (List.mem_append_right _ hb) (hsym (h1 b hb))
    (hsym (h2 b hb))), hpost⟩, fun p hp => ⟨?_, fun b hb => (hcross p hp).2.2 b hb⟩⟩
  exact hj p (List.mem_append_left _ hp) (hcross p hp).1 (hcross p hp).2.1

/-! ### One object -/

/-- The memory and the policy hold the object (without the apart condition). -/
def Obj.Has (policy : CpuPolicy) (m : DataMem) (o : Obj) : Prop :=
  o.addr.toNat + o.size ≤ 2 ^ 64 ∧
    (∀ x ∈ offsets 0 o.cells, readRam policy m (o.addr + BitVec.ofNat 64 x.1) x.2.w = .ok x.2.v) ∧
    (o.writable → ∀ x ∈ offsets 0 o.cells,
      policy.permits (.write (o.addr + BitVec.ofNat 64 x.1) x.2.w))

/-- An object with the cells `cs ++ ds` is the object of `cs` and the object of `ds` right after
it, when the whole object does not wrap past `2^64`. -/
theorem Obj.Has_append (policy : CpuPolicy) (m : DataMem) (a : BitVec 64) (wr : Bool)
    (cs ds : List Cell) (hw : a.toNat + (Obj.mk a wr (cs ++ ds)).size ≤ 2 ^ 64) :
    Obj.Has policy m ⟨a, wr, cs ++ ds⟩ ↔ Obj.Has policy m ⟨a, wr, cs⟩ ∧
      Obj.Has policy m ⟨a + BitVec.ofNat 64 (Obj.mk a wr cs).size, wr, ds⟩ := by
  have hs := Obj.size_append a (a + BitVec.ofNat 64 (Obj.mk a wr cs).size) wr wr cs ds
  have hs1 : (Obj.mk a wr cs).size = (cs.map fun c => c.w.bytes).sum := rfl
  have hnw2 : (a + BitVec.ofNat 64 (Obj.mk a wr cs).size).toNat +
      (Obj.mk (a + BitVec.ofNat 64 (Obj.mk a wr cs).size) wr ds).size ≤ 2 ^ 64 :=
    Split.second_part_fits a _ _ (by omega)
  have hnw1 : a.toNat + (Obj.mk a wr cs).size ≤ 2 ^ 64 := by omega
  unfold Obj.Has
  constructor
  · rintro ⟨-, hr, hwr⟩
    refine ⟨⟨hnw1, fun x hx => hr x (mem_offsets_append.mpr (.inl hx)),
      fun hw' x hx => hwr hw' x (mem_offsets_append.mpr (.inl hx))⟩, hnw2, fun x hx => ?_,
      fun hw' x hx => ?_⟩
    · have := hr _ (mem_offsets_append.mpr (.inr ⟨x, hx, rfl⟩))
      rw [← hs1, add_ofNat_add] at this
      exact this
    · have := hwr hw' _ (mem_offsets_append.mpr (.inr ⟨x, hx, rfl⟩))
      rw [← hs1, add_ofNat_add] at this
      exact this
  · rintro ⟨⟨-, hr1, hw1⟩, -, hr2, hw2⟩
    refine ⟨hw, fun x hx => ?_, fun hw' x hx => ?_⟩
    · rcases mem_offsets_append.mp hx with hx | ⟨y, hy, rfl⟩
      · exact hr1 x hx
      · have := hr2 y hy
        rw [← add_ofNat_add] at this
        exact this
    · rcases mem_offsets_append.mp hx with hx | ⟨y, hy, rfl⟩
      · exact hw1 hw' x hx
      · have := hw2 hw' y hy
        rw [← add_ofNat_add] at this
        exact this

/-! ### The split of `Heap.Holds` -/

theorem Heap.Holds_iff {policy : CpuPolicy} {h : Heap} {m : DataMem} :
    h.Holds policy m ↔ (∀ o ∈ h, o.Has policy m) ∧ h.Pairwise Obj.Sep :=
  ⟨fun hh => ⟨fun o ho => ⟨hh.noWrap o ho, hh.read o ho, hh.write o ho⟩, hh.apart⟩,
    fun ⟨h1, h2⟩ => ⟨fun o ho => (h1 o ho).2.1, fun o ho => (h1 o ho).2.2,
      fun o ho => (h1 o ho).1, h2⟩⟩

/-- The heap with one object, and the heap with the two parts of the object: if the memory holds
the first, it holds the second. -/
theorem Heap.Holds.split {policy : CpuPolicy} {m : DataMem} {pre post : Heap} {a : BitVec 64}
    {wr : Bool} {cs ds : List Cell} (hh : Heap.Holds policy (pre ++ ⟨a, wr, cs ++ ds⟩ :: post) m) :
    Heap.Holds policy
      (pre ++ ⟨a, wr, cs⟩ :: ⟨a + BitVec.ofNat 64 (Obj.mk a wr cs).size, wr, ds⟩ :: post) m := by
  have hw : a.toNat + (Obj.mk a wr (cs ++ ds)).size ≤ 2 ^ 64 :=
    hh.noWrap _ (List.mem_append_right _ (List.mem_cons_self ..))
  rw [Heap.Holds_iff] at hh ⊢
  obtain ⟨h1, h2⟩ := hh
  refine ⟨fun o ho => ?_, pairwise_split_of Obj.Sep.symm (fun p hp => ?_)
    (fun hw' => Obj.apart_split hw) h2⟩
  · simp only [List.mem_append, List.mem_cons] at ho
    rcases ho with ho | rfl | rfl | ho
    · exact h1 o (List.mem_append_left _ ho)
    · exact ((Obj.Has_append policy m a wr cs ds hw).mp
        (h1 _ (List.mem_append_right _ (List.mem_cons_self ..)))).1
    · exact ((Obj.Has_append policy m a wr cs ds hw).mp
        (h1 _ (List.mem_append_right _ (List.mem_cons_self ..)))).2
    · exact h1 o (List.mem_append_right _ (List.mem_cons_of_mem _ ho))
  · exact ⟨fun hw' => (Obj.apart_parts hw (hp hw')).1, fun hw' => (Obj.apart_parts hw (hp hw')).2⟩

/-- The join, with the condition on each other object in the form of `Obj.Sep`. -/
theorem Heap.Holds.join_of {policy : CpuPolicy} {m : DataMem} {pre post : Heap} {a : BitVec 64}
    {wr : Bool} {cs ds : List Cell}
    (hh : Heap.Holds policy
      (pre ++ ⟨a, wr, cs⟩ :: ⟨a + BitVec.ofNat 64 (Obj.mk a wr cs).size, wr, ds⟩ :: post) m)
    (hw : a.toNat + (Obj.mk a wr (cs ++ ds)).size ≤ 2 ^ 64)
    (hj : ∀ p ∈ pre ++ post, p.Sep ⟨a, wr, cs⟩ →
      p.Sep ⟨a + BitVec.ofNat 64 (Obj.mk a wr cs).size, wr, ds⟩ → p.Sep ⟨a, wr, cs ++ ds⟩) :
    Heap.Holds policy (pre ++ ⟨a, wr, cs ++ ds⟩ :: post) m := by
  rw [Heap.Holds_iff] at hh ⊢
  obtain ⟨h1, h2⟩ := hh
  refine ⟨fun o ho => ?_, pairwise_join_of Obj.Sep.symm hj h2⟩
  simp only [List.mem_append, List.mem_cons] at ho
  rcases ho with ho | rfl | ho
  · exact h1 o (List.mem_append_left _ ho)
  · exact (Obj.Has_append policy m a wr cs ds hw).mpr
      ⟨h1 _ (List.mem_append_right _ (List.mem_cons_self ..)),
        h1 _ (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))⟩
  · exact h1 o (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ho)))

/-- The join: the memory holds the two parts, the whole object does not wrap, and each other
object that can conflict with it has no byte in common with the whole object. -/
theorem Heap.Holds.join {policy : CpuPolicy} {m : DataMem} {pre post : Heap} {a : BitVec 64}
    {wr : Bool} {cs ds : List Cell}
    (hh : Heap.Holds policy
      (pre ++ ⟨a, wr, cs⟩ :: ⟨a + BitVec.ofNat 64 (Obj.mk a wr cs).size, wr, ds⟩ :: post) m)
    (hw : a.toNat + (Obj.mk a wr (cs ++ ds)).size ≤ 2 ^ 64)
    (hap : ∀ p ∈ pre ++ post, (p.writable ∨ wr) → p.Apart ⟨a, wr, cs ++ ds⟩) :
    Heap.Holds policy (pre ++ ⟨a, wr, cs ++ ds⟩ :: post) m :=
  Heap.Holds.join_of hh hw fun p hp _ _ hw' => hap p hp hw'

/-- The memory holds the heap with one object exactly when it holds the heap with the two parts of
the object, if the object does not wrap past `2^64` and each other object that can conflict with
it has a byte. -/
theorem Heap.Holds_append_split {policy : CpuPolicy} {m : DataMem} (pre post : Heap)
    (a : BitVec 64) (wr : Bool) (cs ds : List Cell)
    (hw : a.toNat + (Obj.mk a wr (cs ++ ds)).size ≤ 2 ^ 64)
    (hpos : ∀ p ∈ pre ++ post, (p.writable ∨ wr) → 0 < p.size) :
    Heap.Holds policy (pre ++ ⟨a, wr, cs ++ ds⟩ :: post) m ↔
      Heap.Holds policy
        (pre ++ ⟨a, wr, cs⟩ :: ⟨a + BitVec.ofNat 64 (Obj.mk a wr cs).size, wr, ds⟩ :: post) m :=
  ⟨Heap.Holds.split, fun hh => Heap.Holds.join_of hh hw fun p hp h1 h2 hw' =>
    Obj.apart_join hw (hpos p hp hw') (h1 hw') (h2 hw')⟩

/-! ### The split of `Heap.WF` -/

theorem Heap.WF_iff {h : Heap} :
    h.WF = true ↔ (∀ o ∈ h, o.addr.toNat + o.size ≤ 2 ^ 64) ∧ h.Pairwise Obj.Apart := by
  simp only [Heap.WF, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]

/-- Each part of an object that does not wrap does not wrap. -/
theorem Obj.noWrap_parts {a : BitVec 64} {wr : Bool} {cs ds : List Cell}
    (hw : a.toNat + (Obj.mk a wr (cs ++ ds)).size ≤ 2 ^ 64) :
    a.toNat + (Obj.mk a wr cs).size ≤ 2 ^ 64 ∧
      (a + BitVec.ofNat 64 (Obj.mk a wr cs).size).toNat +
        (Obj.mk (a + BitVec.ofNat 64 (Obj.mk a wr cs).size) wr ds).size ≤ 2 ^ 64 := by
  have hs := Obj.size_append a (a + BitVec.ofNat 64 (Obj.mk a wr cs).size) wr wr cs ds
  exact ⟨by omega, Split.second_part_fits a _ _ (by omega)⟩

/-- `WF` of the heap with one object gives `WF` of the heap with the two parts. -/
theorem Heap.WF.split {pre post : Heap} {a : BitVec 64} {wr : Bool} {cs ds : List Cell}
    (hh : (pre ++ ⟨a, wr, cs ++ ds⟩ :: post).WF = true) :
    (pre ++ ⟨a, wr, cs⟩ :: ⟨a + BitVec.ofNat 64 (Obj.mk a wr cs).size, wr, ds⟩ :: post).WF =
      true := by
  rw [Heap.WF_iff] at hh ⊢
  obtain ⟨h1, h2⟩ := hh
  have hw := h1 _ (List.mem_append_right _ (List.mem_cons_self ..))
  refine ⟨fun o ho => ?_, pairwise_split_of Obj.Apart.symm
    (fun p hp => Obj.apart_parts hw hp) (Obj.apart_split hw) h2⟩
  simp only [List.mem_append, List.mem_cons] at ho
  rcases ho with ho | rfl | rfl | ho
  · exact h1 o (List.mem_append_left _ ho)
  · exact (Obj.noWrap_parts hw).1
  · exact (Obj.noWrap_parts hw).2
  · exact h1 o (List.mem_append_right _ (List.mem_cons_of_mem _ ho))

/-- The join, with the condition on each other object in terms of the two parts. -/
theorem Heap.WF.join_of {pre post : Heap} {a : BitVec 64} {wr : Bool} {cs ds : List Cell}
    (hh : (pre ++ ⟨a, wr, cs⟩ :: ⟨a + BitVec.ofNat 64 (Obj.mk a wr cs).size, wr, ds⟩ :: post).WF =
      true)
    (hw : a.toNat + (Obj.mk a wr (cs ++ ds)).size ≤ 2 ^ 64)
    (hj : ∀ p ∈ pre ++ post, p.Apart ⟨a, wr, cs⟩ →
      p.Apart ⟨a + BitVec.ofNat 64 (Obj.mk a wr cs).size, wr, ds⟩ → p.Apart ⟨a, wr, cs ++ ds⟩) :
    (pre ++ ⟨a, wr, cs ++ ds⟩ :: post).WF = true := by
  rw [Heap.WF_iff] at hh ⊢
  obtain ⟨h1, h2⟩ := hh
  refine ⟨fun o ho => ?_, pairwise_join_of Obj.Apart.symm hj h2⟩
  simp only [List.mem_append, List.mem_cons] at ho
  rcases ho with ho | rfl | ho
  · exact h1 o (List.mem_append_left _ ho)
  · exact hw
  · exact h1 o (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ho)))

/-- The join: the object does not wrap and each other object is apart from it. -/
theorem Heap.WF.join {pre post : Heap} {a : BitVec 64} {wr : Bool} {cs ds : List Cell}
    (hh : (pre ++ ⟨a, wr, cs⟩ :: ⟨a + BitVec.ofNat 64 (Obj.mk a wr cs).size, wr, ds⟩ :: post).WF =
      true)
    (hw : a.toNat + (Obj.mk a wr (cs ++ ds)).size ≤ 2 ^ 64)
    (hap : ∀ p ∈ pre ++ post, p.Apart ⟨a, wr, cs ++ ds⟩) :
    (pre ++ ⟨a, wr, cs ++ ds⟩ :: post).WF = true :=
  Heap.WF.join_of hh hw fun p hp _ _ => hap p hp

/-- `WF` of the heap with one object is `WF` of the heap with the two parts, if the object does
not wrap past `2^64` and each other object has a byte. -/
theorem Heap.WF_append_split (pre post : Heap) (a : BitVec 64) (wr : Bool) (cs ds : List Cell)
    (hw : a.toNat + (Obj.mk a wr (cs ++ ds)).size ≤ 2 ^ 64)
    (hpos : ∀ p ∈ pre ++ post, 0 < p.size) :
    (pre ++ ⟨a, wr, cs ++ ds⟩ :: post).WF = true ↔
      (pre ++ ⟨a, wr, cs⟩ :: ⟨a + BitVec.ofNat 64 (Obj.mk a wr cs).size, wr, ds⟩ :: post).WF =
        true :=
  ⟨Heap.WF.split, fun hh => Heap.WF.join_of hh hw fun p hp h1 h2 =>
    Obj.apart_join hw (hpos p hp) h1 h2⟩

/-! ### Permutations -/

theorem Heap.Holds_perm {policy : CpuPolicy} {m : DataMem} {h h' : Heap} (hp : h.Perm h') :
    h.Holds policy m ↔ h'.Holds policy m := by
  rw [Heap.Holds_iff, Heap.Holds_iff, hp.pairwise_iff Obj.Sep.symm]
  exact and_congr_left' ⟨fun H o ho => H o (hp.symm.subset ho), fun H o ho => H o (hp.subset ho)⟩

theorem Heap.WF_perm {h h' : Heap} (hp : h.Perm h') : h.WF = true ↔ h'.WF = true := by
  rw [Heap.WF_iff, Heap.WF_iff, hp.pairwise_iff Obj.Apart.symm]
  exact and_congr_left' ⟨fun H o ho => H o (hp.symm.subset ho), fun H o ho => H o (hp.subset ho)⟩

/-! ### A load -/

/-- A cell of width `w` is at `a` in the object. -/
theorem Obj.get_isSome_iff {o : Obj} {a : BitVec 64} {w : Width} :
    (o.get a w).isSome ↔
      ∃ x ∈ offsets 0 o.cells, o.addr + BitVec.ofNat 64 x.1 = a ∧ x.2.w = w := by
  constructor
  · intro h
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h
    obtain ⟨x, hx, ha, hc⟩ := Obj.get_some hv
    exact ⟨x, hx, ha, by rw [hc]⟩
  · rintro ⟨x, hx, ha, hw⟩
    subst ha hw
    exact Obj.get_isSome_of_mem hx

/-- Two heaps that the same memory holds, and an object with a cell of width `w` at `a` in the
one for each such object of the other: the same load. -/
theorem Heap.load_eq_of_holds {policy : CpuPolicy} {m : DataMem} {h h' : Heap}
    (hh : h.Holds policy m) (hh' : h'.Holds policy m) (a : BitVec 64) (w : Width)
    (hsub : ∀ o ∈ h, (o.get a w).isSome → ∃ o' ∈ h', (o'.get a w).isSome)
    (hsub' : ∀ o ∈ h', (o.get a w).isSome → ∃ o' ∈ h, (o'.get a w).isSome) :
    h.load a w = h'.load a w := by
  have key : ∀ {l l' : Heap}, l.Holds policy m → l'.Holds policy m →
      (∀ o ∈ l, (o.get a w).isSome → ∃ o' ∈ l', (o'.get a w).isSome) →
      ∀ v, l.findSome? (fun o => o.get a w) = some v →
        ∃ v', l'.findSome? (fun o => o.get a w) = some v' ∧ v' = v := by
    intro l l' hl hl' hs v hf
    obtain ⟨o, ho, hg⟩ := List.exists_of_findSome?_eq_some hf
    obtain ⟨o', ho', hg'⟩ := hs o ho (by rw [hg]; rfl)
    rcases hf' : l'.findSome? (fun o => o.get a w) with _ | v'
    · rw [List.findSome?_eq_none_iff.mp hf' o' ho'] at hg'
      cases hg'
    · refine ⟨v', hf', ?_⟩
      have e := (Heap.load_sound hl (show l.load a w = .ok v by unfold Heap.load; rw [hf])).symm.trans
        (Heap.load_sound hl' (show l'.load a w = .ok v' by unfold Heap.load; rw [hf']))
      exact (Except.ok.inj e).symm
  unfold Heap.load
  rcases hf : h.findSome? (fun o => o.get a w) with _ | v
  · rcases hf' : h'.findSome? (fun o => o.get a w) with _ | v'
    · rw [hf, hf']
    · obtain ⟨v'', hv, -⟩ := key hh' hh hsub' v' hf'
      rw [hf] at hv
      cases hv
  · obtain ⟨v', hv, e⟩ := key hh hh' hsub v hf
    rw [hf, hv, e]

/-- A cell of width `w` is at `a` in the object of `cs ++ ds` exactly when it is in the object of
`cs` or in the object of `ds` right after it. -/
theorem Obj.get_isSome_append (a₀ : BitVec 64) (wr : Bool) (cs ds : List Cell) (a : BitVec 64)
    (w : Width) :
    ((Obj.mk a₀ wr (cs ++ ds)).get a w).isSome ↔ ((Obj.mk a₀ wr cs).get a w).isSome ∨
      ((Obj.mk (a₀ + BitVec.ofNat 64 (Obj.mk a₀ wr cs).size) wr ds).get a w).isSome := by
  rw [Obj.get_isSome_iff, Obj.get_isSome_iff, Obj.get_isSome_iff]
  constructor
  · rintro ⟨x, hx, ha, hw⟩
    rcases mem_offsets_append.mp hx with hx | ⟨y, hy, rfl⟩
    · exact .inl ⟨x, hx, ha, hw⟩
    · refine .inr ⟨y, hy, ?_, hw⟩
      show a₀ + BitVec.ofNat 64 (Obj.mk a₀ wr cs).size + BitVec.ofNat 64 y.1 = a
      rw [← add_ofNat_add]
      exact ha
  · rintro (⟨x, hx, ha, hw⟩ | ⟨y, hy, ha, hw⟩)
    · exact ⟨x, mem_offsets_append.mpr (.inl hx), ha, hw⟩
    · refine ⟨_, mem_offsets_append.mpr (.inr ⟨y, hy, rfl⟩), ?_, hw⟩
      have : a₀ + BitVec.ofNat 64 (Obj.mk a₀ wr cs).size + BitVec.ofNat 64 y.1 = a := ha
      rw [← add_ofNat_add] at this
      exact this

/-- A load in the heap with the two parts of an object is the load in the heap with the object,
when the memory holds the heap with the object. -/
theorem Heap.load_append_split {policy : CpuPolicy} {m : DataMem} {pre post : Heap}
    {a₀ : BitVec 64} {wr : Bool} {cs ds : List Cell}
    (hh : Heap.Holds policy (pre ++ ⟨a₀, wr, cs ++ ds⟩ :: post) m) (a : BitVec 64) (w : Width) :
    Heap.load (pre ++ ⟨a₀, wr, cs⟩ :: ⟨a₀ + BitVec.ofNat 64 (Obj.mk a₀ wr cs).size, wr, ds⟩ :: post)
        a w = Heap.load (pre ++ ⟨a₀, wr, cs ++ ds⟩ :: post) a w := by
  refine Heap.load_eq_of_holds (Heap.Holds.split hh) hh a w (fun o ho hg => ?_) (fun o ho hg => ?_)
  · simp only [List.mem_append, List.mem_cons] at ho
    rcases ho with ho | rfl | rfl | ho
    · exact ⟨o, List.mem_append_left _ ho, hg⟩
    · exact ⟨_, List.mem_append_right _ (List.mem_cons_self ..),
        (Obj.get_isSome_append a₀ wr cs ds a w).mpr (.inl hg)⟩
    · exact ⟨_, List.mem_append_right _ (List.mem_cons_self ..),
        (Obj.get_isSome_append a₀ wr cs ds a w).mpr (.inr hg)⟩
    · exact ⟨o, List.mem_append_right _ (List.mem_cons_of_mem _ ho), hg⟩
  · simp only [List.mem_append, List.mem_cons] at ho
    rcases ho with ho | rfl | ho
    · exact ⟨o, List.mem_append_left _ ho, hg⟩
    · rcases (Obj.get_isSome_append a₀ wr cs ds a w).mp hg with hg | hg
      · exact ⟨_, List.mem_append_right _ (List.mem_cons_self ..), hg⟩
      · exact ⟨_, List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), hg⟩
    · exact ⟨o, List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ho)), hg⟩

/-- A load does not depend on the order of the objects of a heap that a memory holds. -/
theorem Heap.load_perm_of_holds {policy : CpuPolicy} {m : DataMem} {h h' : Heap}
    (hh : h.Holds policy m) (hp : h.Perm h') (a : BitVec 64) (w : Width) :
    h.load a w = h'.load a w :=
  Heap.load_eq_of_holds hh ((Heap.Holds_perm hp).mp hh) a w
    (fun o ho hg => ⟨o, hp.subset ho, hg⟩) (fun o ho hg => ⟨o, hp.symm.subset ho, hg⟩)

/-- A load does not depend on the order of the objects of a well formed heap. Without `WF` it can:
two read-only objects with different values at one address. -/
theorem Heap.load_perm {h h' : Heap} (hw : h.WF = true) (hp : h.Perm h') (a : BitVec 64)
    (w : Width) : h.load a w = h'.load a w := by
  obtain ⟨policy, m, hh⟩ := Heap.WF.holds hw
  exact Heap.load_perm_of_holds hh hp a w

/-- A store gives the same heap up to the order of the objects, when the order of the objects
changes. -/
theorem Heap.store_perm {h h' : Heap} (hp : h.Perm h') {a : BitVec 64} {w : Width} {v : w.type}
    {k : Heap} (hs : h.store a w v = .ok k) :
    ∃ k', h'.store a w v = .ok k' ∧ k.Perm k' := by
  obtain ⟨rfl, O, hO, hw, x, hx, ha, hxw⟩ := Heap.store_ok hs
  have hc : (h'.any fun o => o.writable && (o.get a w).isSome) = true :=
    List.any_eq_true.mpr ⟨O, hp.subset hO, by
      simp only [hw, Bool.true_and, Obj.get_isSome_iff]
      exact ⟨x, hx, ha, hxw⟩⟩
  refine ⟨h'.map (Obj.set a w v), ?_, hp.map _⟩
  unfold Heap.store
  simp only [hc, ↓reduceIte]

/-! ### A store -/

theorem setCells_append (base a : BitVec 64) (w : Width) (v : w.type) (n : Nat)
    (cs ds : List Cell) :
    setCells base a w v n (cs ++ ds) =
      setCells base a w v n cs ++ setCells base a w v (n + (cs.map fun c => c.w.bytes).sum) ds := by
  induction cs generalizing n with
  | nil => simp [setCells]
  | cons c cs ih =>
    simp only [List.cons_append, setCells, ih, List.map_cons, List.sum_cons, List.cons.injEq,
      true_and]
    rw [Nat.add_assoc]

theorem setCells_shift (base a : BitVec 64) (w : Width) (v : w.type) (n k : Nat)
    (cs : List Cell) :
    setCells base a w v (n + k) cs = setCells (base + BitVec.ofNat 64 n) a w v k cs := by
  induction cs generalizing k with
  | nil => rfl
  | cons c cs ih =>
    simp only [setCells]
    rw [show n + k + c.w.bytes = n + (k + c.w.bytes) by omega, ih, add_ofNat_add]

/-- A store to an object of `cs ++ ds` is a store to the object of `cs` and a store to the object
of `ds` right after it. -/
theorem Obj.set_append (a : BitVec 64) (w : Width) (v : w.type) (a₀ : BitVec 64) (wr : Bool)
    (cs ds : List Cell) :
    Obj.set a w v ⟨a₀, wr, cs ++ ds⟩ = ⟨a₀, wr, (Obj.set a w v ⟨a₀, wr, cs⟩).cells ++
      (Obj.set a w v ⟨a₀ + BitVec.ofNat 64 (Obj.mk a₀ wr cs).size, wr, ds⟩).cells⟩ := by
  unfold Obj.set
  cases wr
  · rfl
  · simp only [↓reduceIte]
    rw [setCells_append, Nat.zero_add]
    have := setCells_shift a₀ a w v (cs.map fun c => c.w.bytes).sum 0 ds
    rw [Nat.add_zero] at this
    rw [this]
    rfl

theorem Obj.set_eq (a : BitVec 64) (w : Width) (v : w.type) (o : Obj) :
    Obj.set a w v o = ⟨o.addr, o.writable, (Obj.set a w v o).cells⟩ := by
  have h1 := Obj.set_addr a w v o
  have h2 := Obj.set_writable a w v o
  cases e : Obj.set a w v o
  rw [e] at h1 h2
  simp only at h1 h2
  subst h1 h2
  rfl

/-- A store succeeds when a writable object has a cell at the address, and gives the store of each
object. -/
theorem Heap.store_eq_ok_iff {h k : Heap} {a : BitVec 64} {w : Width} {v : w.type} :
    h.store a w v = .ok k ↔
      (h.any fun o => o.writable && (o.get a w).isSome) = true ∧ k = h.map (Obj.set a w v) := by
  constructor
  · intro hs
    obtain ⟨rfl, O, hO, hw, x, hx, ha, hxw⟩ := Heap.store_ok hs
    refine ⟨List.any_eq_true.mpr ⟨O, hO, ?_⟩, rfl⟩
    simp only [hw, Bool.true_and, Obj.get_isSome_iff]
    exact ⟨x, hx, ha, hxw⟩
  · rintro ⟨hc, rfl⟩
    unfold Heap.store
    simp only [hc, ↓reduceIte]

/-- A writable object with a cell at the address is in the heap with one object exactly when it
is in the heap with the two parts. -/
theorem any_store_split (pre post : Heap) (a₀ : BitVec 64) (wr : Bool) (cs ds : List Cell)
    (a : BitVec 64) (w : Width) :
    ((pre ++ ⟨a₀, wr, cs ++ ds⟩ :: post).any fun o => o.writable && (o.get a w).isSome) =
      ((pre ++ ⟨a₀, wr, cs⟩ :: ⟨a₀ + BitVec.ofNat 64 (Obj.mk a₀ wr cs).size, wr, ds⟩ :: post).any
        fun o => o.writable && (o.get a w).isSome) := by
  have e : (wr && ((Obj.mk a₀ wr (cs ++ ds)).get a w).isSome) =
      ((wr && ((Obj.mk a₀ wr cs).get a w).isSome) ||
        (wr && ((Obj.mk (a₀ + BitVec.ofNat 64 (Obj.mk a₀ wr cs).size) wr ds).get a w).isSome)) := by
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, Bool.or_eq_true, Obj.get_isSome_append]
    exact and_or_left
  simp only [List.any_append, List.any_cons, e, Bool.or_assoc]

/-- A store in the heap with one object is a store in the heap with its two parts: the new heap
has the two parts of the new object. -/
theorem Heap.store_append_split {pre post : Heap} {a₀ : BitVec 64} {wr : Bool} {cs ds : List Cell}
    {a : BitVec 64} {w : Width} {v : w.type} {k : Heap}
    (hs : (pre ++ ⟨a₀, wr, cs ++ ds⟩ :: post).store a w v = .ok k) :
    ∃ cs' ds', k = pre.map (Obj.set a w v) ++ ⟨a₀, wr, cs' ++ ds'⟩ :: post.map (Obj.set a w v) ∧
      (pre ++ ⟨a₀, wr, cs⟩ :: ⟨a₀ + BitVec.ofNat 64 (Obj.mk a₀ wr cs).size, wr, ds⟩ :: post).store
          a w v =
        .ok (pre.map (Obj.set a w v) ++ ⟨a₀, wr, cs'⟩ ::
          ⟨a₀ + BitVec.ofNat 64 (Obj.mk a₀ wr cs).size, wr, ds'⟩ :: post.map (Obj.set a w v)) := by
  obtain ⟨hc, rfl⟩ := Heap.store_eq_ok_iff.mp hs
  refine ⟨(Obj.set a w v ⟨a₀, wr, cs⟩).cells,
    (Obj.set a w v ⟨a₀ + BitVec.ofNat 64 (Obj.mk a₀ wr cs).size, wr, ds⟩).cells, ?_, ?_⟩
  · simp only [List.map_append, List.map_cons, Obj.set_append]
  · rw [Heap.store_eq_ok_iff]
    refine ⟨by rw [← any_store_split]; exact hc, ?_⟩
    simp only [List.map_append, List.map_cons]
    rw [← Obj.set_eq a w v ⟨a₀, wr, cs⟩, ← Obj.set_eq a w v ⟨_, wr, ds⟩]

/-- The reverse: a store in the heap with the two parts of an object is a store in the heap with
the object. -/
theorem Heap.store_append_join {pre post : Heap} {a₀ : BitVec 64} {wr : Bool} {cs ds : List Cell}
    {a : BitVec 64} {w : Width} {v : w.type} {k' : Heap}
    (hs : (pre ++ ⟨a₀, wr, cs⟩ :: ⟨a₀ + BitVec.ofNat 64 (Obj.mk a₀ wr cs).size, wr, ds⟩ :: post).store
      a w v = .ok k') :
    ∃ cs' ds', k' = pre.map (Obj.set a w v) ++ ⟨a₀, wr, cs'⟩ ::
          ⟨a₀ + BitVec.ofNat 64 (Obj.mk a₀ wr cs).size, wr, ds'⟩ :: post.map (Obj.set a w v) ∧
      (pre ++ ⟨a₀, wr, cs ++ ds⟩ :: post).store a w v =
        .ok (pre.map (Obj.set a w v) ++ ⟨a₀, wr, cs' ++ ds'⟩ :: post.map (Obj.set a w v)) := by
  obtain ⟨hc, rfl⟩ := Heap.store_eq_ok_iff.mp hs
  refine ⟨(Obj.set a w v ⟨a₀, wr, cs⟩).cells,
    (Obj.set a w v ⟨a₀ + BitVec.ofNat 64 (Obj.mk a₀ wr cs).size, wr, ds⟩).cells, ?_, ?_⟩
  · simp only [List.map_append, List.map_cons]
    rw [← Obj.set_eq a w v ⟨a₀, wr, cs⟩, ← Obj.set_eq a w v ⟨_, wr, ds⟩]
  · rw [Heap.store_eq_ok_iff]
    refine ⟨by rw [any_store_split]; exact hc, ?_⟩
    simp only [List.map_append, List.map_cons, Obj.set_append]

end Lift.Sem
