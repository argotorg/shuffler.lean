module

public import Lift.Sem.Model
public import Lift.P2.Total.Footprint

@[expose] public section

namespace Lift.Sem

open Lift.P2.Total

/-- A value of a width. -/
structure Cell where
  w : Width
  v : w.type

/-- An object: its address, whether a store can change it, and its cells in sequence. -/
structure Obj where
  addr : BitVec 64
  writable : Bool
  cells : List Cell

/-- A flat typed heap. -/
abbrev Heap := List Obj

/-- The cells, each with its offset; the first offset is `off`. -/
def offsets : Nat → List Cell → List (Nat × Cell)
  | _, [] => []
  | off, c :: cs => (off, c) :: offsets (off + c.w.bytes) cs

/-- The number of bytes of the object. -/
def Obj.size (o : Obj) : Nat := (o.cells.map fun c => c.w.bytes).sum

/-- The value of the cell, if the cell has the width `w`. -/
def Cell.get (c : Cell) (w : Width) : Option w.type :=
  if h : c.w = w then some (h ▸ c.v) else none

/-- The value of the cell of width `w` that starts at `a`. -/
def Obj.get (o : Obj) (a : BitVec 64) (w : Width) : Option w.type :=
  (offsets 0 o.cells).findSome? fun x =>
    if o.addr + BitVec.ofNat 64 x.1 = a then x.2.get w else none

/-- A load: the value of a cell of width `w` that starts at `a`. -/
def Heap.load (h : Heap) (a : BitVec 64) (w : Width) : Res w.type :=
  match h.findSome? fun o => o.get a w with
  | some v => .ok v
  | none => .stuck "load: no cell of this width at this address"

/-- The cells (the first at `base + off`) with the value `v` in each cell of width `w` at `a`. -/
def setCells (base a : BitVec 64) (w : Width) (v : w.type) : Nat → List Cell → List Cell
  | _, [] => []
  | off, c :: cs =>
    (if base + BitVec.ofNat 64 off = a ∧ c.w = w then ⟨w, v⟩ else c) ::
      setCells base a w v (off + c.w.bytes) cs

/-- The object after a store of `v` at `a`; an object that is not writable does not change. -/
def Obj.set (a : BitVec 64) (w : Width) (v : w.type) (o : Obj) : Obj :=
  if o.writable then { o with cells := setCells o.addr a w v 0 o.cells } else o

/-- A store: a writable object must have a cell of width `w` at `a`. -/
def Heap.store (h : Heap) (a : BitVec 64) (w : Width) (v : w.type) : Res Heap :=
  if h.any fun o => o.writable && (o.get a w).isSome then .ok (h.map (Obj.set a w v))
  else if h.any fun o => (o.get a w).isSome then .stuck "store: the object is not writable"
  else .stuck "store: no cell of this width at this address"

/-- An array of values of one width. -/
def Obj.words (addr : BitVec 64) (writable : Bool) (w : Width) (xs : List w.type) : Obj :=
  ⟨addr, writable, xs.map (Cell.mk w)⟩

/-- The two objects have no byte in common. -/
def Obj.Apart (o o' : Obj) : Prop :=
  o.addr.toNat + o.size ≤ o'.addr.toNat ∨ o'.addr.toNat + o'.size ≤ o.addr.toNat

/-- The byte at `b` is a byte of the object. -/
def Obj.Covers (o : Obj) (b : BitVec 64) : Prop :=
  o.addr.toNat ≤ b.toNat ∧ b.toNat < o.addr.toNat + o.size

/-- The memory and the policy hold the heap. -/
structure Heap.Holds (policy : CpuPolicy) (h : Heap) (m : DataMem) : Prop where
  /-- A read of each cell is permitted and gives the value of the cell. -/
  read : ∀ o ∈ h, ∀ x ∈ offsets 0 o.cells,
    readRam policy m (o.addr + BitVec.ofNat 64 x.1) x.2.w = .ok x.2.v
  /-- A write of each cell of a writable object is permitted. -/
  write : ∀ o ∈ h, o.writable → ∀ x ∈ offsets 0 o.cells,
    policy.permits (.write (o.addr + BitVec.ofNat 64 x.1) x.2.w)
  /-- No object wraps around the end of the address space. -/
  noWrap : ∀ o ∈ h, o.addr.toNat + o.size ≤ 2 ^ 64
  /-- A writable object has no byte in common with another object. -/
  apart : h.Pairwise fun o o' => (o.writable ∨ o'.writable) → o.Apart o'

/-! ### Lemmas -/

theorem width_bits_eq (w : Width) : w.bits = 8 * w.bytes := by cases w <;> rfl

theorem width_bytes_pos (w : Width) : 0 < w.bytes := by cases w <;> decide

theorem Cell.get_eq_some {c : Cell} {w : Width} {v : w.type} :
    c.get w = some v ↔ c = ⟨w, v⟩ := by
  obtain ⟨w', v'⟩ := c
  unfold Cell.get
  constructor
  · intro h
    split at h
    · rename_i e
      subst e
      cases h
      rfl
    · cases h
  · intro h
    cases h
    simp

theorem Obj.get_some {o : Obj} {a : BitVec 64} {w : Width} {v : w.type} (h : o.get a w = some v) :
    ∃ x ∈ offsets 0 o.cells, o.addr + BitVec.ofNat 64 x.1 = a ∧ x.2 = ⟨w, v⟩ := by
  obtain ⟨x, hx, he⟩ := List.exists_of_findSome?_eq_some h
  split at he
  · exact ⟨x, hx, ‹_›, Cell.get_eq_some.mp he⟩
  · cases he

theorem pairwise_of_mem {α : Type} {R : α → α → Prop} (sym : ∀ {a b}, R a b → R b a)
    {l : List α} (hl : l.Pairwise R) {a b : α} (ha : a ∈ l) (hb : b ∈ l) (hne : a ≠ b) :
    R a b := by
  induction hl with
  | nil => cases ha
  | cons hr _ ih =>
    rename_i c l _
    rcases List.mem_cons.mp ha with ea | ma <;> rcases List.mem_cons.mp hb with eb | mb
    · exact absurd (ea.trans eb.symm) hne
    · exact ea ▸ hr _ mb
    · exact eb ▸ sym (hr _ ma)
    · exact ih ma mb

theorem offsets_bound {n : Nat} {cs : List Cell} {x : Nat × Cell} (hx : x ∈ offsets n cs) :
    n ≤ x.1 ∧ x.1 + x.2.w.bytes ≤ n + (cs.map fun c => c.w.bytes).sum := by
  induction cs generalizing n with
  | nil => cases hx
  | cons c cs ih =>
    simp only [offsets, List.mem_cons] at hx
    rcases hx with rfl | hx
    · simp only [List.map_cons, List.sum_cons]; omega
    · have := ih hx; simp only [List.map_cons, List.sum_cons]; omega

theorem offsets_pairwise (n : Nat) (cs : List Cell) :
    (offsets n cs).Pairwise fun x y => x.1 + x.2.w.bytes ≤ y.1 := by
  induction cs generalizing n with
  | nil => exact .nil
  | cons c cs ih => exact .cons (fun y hy => (offsets_bound hy).1) (ih _)

theorem toNat_add_ofNat (a : BitVec 64) (i : Nat) (h : a.toNat + i < 2 ^ 64) :
    (a + BitVec.ofNat 64 i).toNat = a.toNat + i := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : i < 2 ^ 64)]
  exact Nat.mod_eq_of_lt h

theorem byteDisjoint_of_nat {a b : BitVec 64} {n k : Nat} (ha : a.toNat + n ≤ 2 ^ 64)
    (hb : b.toNat + k ≤ 2 ^ 64) (h : a.toNat + n ≤ b.toNat ∨ b.toNat + k ≤ a.toNat) :
    ByteDisjoint a n b k := by
  intro i hi j hj e
  have := congrArg BitVec.toNat e
  rw [toNat_add_ofNat a i (by omega), toNat_add_ofNat b j (by omega)] at this
  omega

/-- The address of a cell of an object that does not wrap. -/
theorem Obj.toNat_cell {o : Obj} {x : Nat × Cell} (hw : o.addr.toNat + o.size ≤ 2 ^ 64)
    (hx : x ∈ offsets 0 o.cells) :
    (o.addr + BitVec.ofNat 64 x.1).toNat = o.addr.toNat + x.1 ∧ x.1 + x.2.w.bytes ≤ o.size := by
  have hb := offsets_bound hx
  have := width_bytes_pos x.2.w
  unfold Obj.size at hw ⊢
  exact ⟨toNat_add_ofNat _ _ (by omega), by omega⟩

/-- A cell of a writable object and another cell have no byte in common. -/
theorem Heap.Holds.disjoint {policy : CpuPolicy} {h : Heap} {m : DataMem}
    (hh : h.Holds policy m) {O o : Obj} {x₀ x : Nat × Cell} (hO : O ∈ h) (hw : O.writable)
    (hx₀ : x₀ ∈ offsets 0 O.cells) (ho : o ∈ h) (hx : x ∈ offsets 0 o.cells)
    (hne : ¬ (o = O ∧ x = x₀)) :
    ByteDisjoint (O.addr + BitVec.ofNat 64 x₀.1) x₀.2.w.bytes
      (o.addr + BitVec.ofNat 64 x.1) x.2.w.bytes := by
  have n₀ := hh.noWrap O hO
  have n₁ := hh.noWrap o ho
  obtain ⟨e₀, b₀⟩ := Obj.toNat_cell n₀ hx₀
  obtain ⟨e₁, b₁⟩ := Obj.toNat_cell n₁ hx
  apply byteDisjoint_of_nat (by omega) (by omega)
  rw [e₀, e₁]
  by_cases hoO : o = O
  · subst hoO
    have hxx : x₀ ≠ x := fun e => hne ⟨rfl, e.symm⟩
    have := pairwise_of_mem
      (R := fun x y => x.1 + x.2.w.bytes ≤ y.1 ∨ y.1 + y.2.w.bytes ≤ x.1)
      (fun h => h.symm) ((offsets_pairwise 0 o.cells).imp Or.inl) hx₀ hx hxx
    omega
  · have := pairwise_of_mem (R := fun o o' => (o.writable ∨ o'.writable) → o.Apart o')
      (fun h hw' => Or.symm (h (Or.symm hw'))) hh.apart hO ho (Ne.symm hoO) (.inl hw)
    unfold Obj.Apart at this
    omega

theorem readRam_ok {policy : CpuPolicy} {m : DataMem} {a : BitVec 64} {w : Width}
    {v : w.type} (h : readRam policy m a w = .ok v) :
    policy.permits (.read a w) = true ∧ ∃ x, Mem.loadInt m a w.bytes = some x := by
  unfold readRam at h
  split at h
  · rename_i hp
    split at h
    · exact ⟨hp, _, ‹_›⟩
    · cases h
  · cases h

/-- A read gives the same value from a memory with the same bytes. -/
theorem readRam_congr {policy : CpuPolicy} {m m' : DataMem} {a : BitVec 64} {w : Width}
    {v : w.type} (h : readRam policy m a w = .ok v)
    (e : Mem.loadInt m' a w.bytes = Mem.loadInt m a w.bytes) : readRam policy m' a w = .ok v := by
  unfold readRam at h ⊢
  rw [e]
  split at h
  · rename_i hp
    simp only [hp, ↓reduceIte]
    split at h
    · exact h
    · cases h
  · cases h

/-- A read of a cell after a store to the cell. -/
theorem readRam_storeInt {policy : CpuPolicy} {m : DataMem} {a : BitVec 64} {w : Width}
    {v v₀ : w.type} (h : readRam policy m a w = .ok v₀) :
    readRam policy (Mem.storeInt m a w.bytes v.toInt) a w = .ok v := by
  obtain ⟨hp, _⟩ := readRam_ok h
  unfold readRam
  simp only [hp, ↓reduceIte]
  rw [Mem.loadInt_storeInt m a w.bytes v.toInt (by cases w <;> decide)]
  show Except.ok (BitVec.ofInt w.bits _) = _
  rw [BitVec.ofInt_ofBytes_toBytes _ _ (width_bits_eq w), BitVec.ofInt_toInt]

theorem writeRam_of_readRam {policy : CpuPolicy} {m : DataMem} {a : BitVec 64} {w : Width}
    {v v₀ : w.type} (h : readRam policy m a w = .ok v₀)
    (hp : policy.permits (.write a w) = true) :
    writeRam policy m a w v = .ok (Mem.storeInt m a w.bytes v.toInt) := by
  obtain ⟨_, x, hx⟩ := readRam_ok h
  unfold writeRam
  simp only [hp, ↓reduceIte, hx]

theorem offsets_setCells (base a : BitVec 64) (w : Width) (v : w.type) (n : Nat)
    (cs : List Cell) :
    offsets n (setCells base a w v n cs) = (offsets n cs).map fun x =>
      (x.1, if base + BitVec.ofNat 64 x.1 = a ∧ x.2.w = w then ⟨w, v⟩ else x.2) := by
  induction cs generalizing n with
  | nil => rfl
  | cons c cs ih =>
    have e : (if base + BitVec.ofNat 64 n = a ∧ c.w = w then (⟨w, v⟩ : Cell) else c).w.bytes =
        c.w.bytes := by
      split
      · rename_i hc; show w.bytes = c.w.bytes; rw [hc.2]
      · rfl
    simp only [setCells, offsets, List.map_cons, e, ih]

theorem setCells_bytes (base a : BitVec 64) (w : Width) (v : w.type) (n : Nat)
    (cs : List Cell) :
    (setCells base a w v n cs).map (fun c => c.w.bytes) = cs.map fun c => c.w.bytes := by
  induction cs generalizing n with
  | nil => rfl
  | cons c cs ih =>
    simp only [setCells, List.map_cons, ih, List.cons.injEq, and_true]
    split
    · rename_i hc; show w.bytes = c.w.bytes; rw [hc.2]
    · rfl

theorem Obj.set_addr (a : BitVec 64) (w : Width) (v : w.type) (o : Obj) :
    (o.set a w v).addr = o.addr := by
  unfold Obj.set; split <;> rfl

theorem Obj.set_writable (a : BitVec 64) (w : Width) (v : w.type) (o : Obj) :
    (o.set a w v).writable = o.writable := by
  unfold Obj.set; split <;> rfl

theorem Obj.set_size (a : BitVec 64) (w : Width) (v : w.type) (o : Obj) :
    (o.set a w v).size = o.size := by
  unfold Obj.set
  split
  · simp only [Obj.size, setCells_bytes]
  · rfl

/-- A cell after a store: the same cell, or the cell of the store with the new value. -/
theorem Obj.mem_offsets_set {a : BitVec 64} {w : Width} {v : w.type} {o : Obj}
    {x' : Nat × Cell} (hx' : x' ∈ offsets 0 (o.set a w v).cells) :
    ∃ x ∈ offsets 0 o.cells, x'.1 = x.1 ∧ x'.2.w = x.2.w ∧
      ((x'.2 = x.2 ∧ ¬ (o.writable ∧ o.addr + BitVec.ofNat 64 x.1 = a ∧ x.2.w = w)) ∨
        (o.writable ∧ o.addr + BitVec.ofNat 64 x.1 = a ∧ x.2.w = w ∧ x'.2 = ⟨w, v⟩)) := by
  unfold Obj.set at hx'
  split at hx'
  · rename_i hw
    rw [offsets_setCells] at hx'
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hx'
    refine ⟨x, hx, rfl, ?_, ?_⟩
    · split
      · rename_i hc; exact hc.2.symm
      · rfl
    · by_cases hc : o.addr + BitVec.ofNat 64 x.1 = a ∧ x.2.w = w
      · exact .inr ⟨hw, hc.1, hc.2, by simp [hc]⟩
      · exact .inl ⟨by simp [hc], fun h => hc h.2⟩
  · rename_i hw
    exact ⟨x', hx', rfl, rfl, .inl ⟨rfl, fun h => hw h.1⟩⟩

/-- A load is a read of the memory. -/
theorem Heap.load_sound {policy : CpuPolicy} {h : Heap} {m : DataMem} {a : BitVec 64}
    {w : Width} {v : w.type} (hh : h.Holds policy m) (hl : h.load a w = .ok v) :
    readRam policy m a w = .ok v := by
  unfold Heap.load at hl
  split at hl
  · rename_i v' hf
    cases hl
    obtain ⟨o, ho, hg⟩ := List.exists_of_findSome?_eq_some hf
    obtain ⟨x, hx, hax, hxc⟩ := Obj.get_some hg
    have hr := hh.read o ho x hx
    rw [hax, hxc] at hr
    exact hr
  · cases hl

/-- A store is a write of the memory; the memory holds the new heap; each byte outside the
object of the cell does not change. -/
theorem Heap.store_sound {policy : CpuPolicy} {h h' : Heap} {m : DataMem} {a : BitVec 64}
    {w : Width} {v : w.type} (hh : h.Holds policy m) (hs : h.store a w v = .ok h') :
    ∃ m', writeRam policy m a w v = .ok m' ∧ h'.Holds policy m' ∧
      ∃ o ∈ h, o.writable ∧ ∀ b, ¬ o.Covers b → m'.get? b = m.get? b := by
  unfold Heap.store at hs
  split at hs
  · rename_i hc
    cases hs
    obtain ⟨O, hO, hc⟩ := List.any_eq_true.mp hc
    simp only [Bool.and_eq_true, Option.isSome_iff_exists] at hc
    obtain ⟨hw, v₀, hg⟩ := hc
    obtain ⟨x₀, hx₀, rfl, hc₀⟩ := Obj.get_some hg
    have hx₀w : x₀.2.w = w := by rw [hc₀]
    have hr₀ : readRam policy m (O.addr + BitVec.ofNat 64 x₀.1) w = .ok v₀ := by
      have := hh.read O hO x₀ hx₀
      rw [hc₀] at this
      exact this
    have hp : policy.permits (.write (O.addr + BitVec.ofNat 64 x₀.1) w) := by
      have := hh.write O hO hw x₀ hx₀
      rw [hc₀] at this
      exact this
    refine ⟨_, writeRam_of_readRam hr₀ hp, ⟨?_, ?_, ?_, ?_⟩, O, hO, hw, ?_⟩
    · intro o' ho' x' hx'
      obtain ⟨o, ho, rfl⟩ := List.mem_map.mp ho'
      obtain ⟨x, hx, e₁, e₂, hcase⟩ := Obj.mem_offsets_set hx'
      rw [Obj.set_addr, e₁]
      rcases hcase with ⟨e₃, hn⟩ | ⟨_, hax, _, e₃⟩
      · rw [e₃]
        apply readRam_congr (hh.read o ho x hx)
        have hd := hh.disjoint hO hw hx₀ ho hx (by
          rintro ⟨rfl, rfl⟩
          exact hn ⟨hw, rfl, hx₀w⟩)
        rw [hx₀w] at hd
        exact loadInt_storeInt_separate _ _ _ _ _ _ hd
      · rw [e₃, hax]
        exact readRam_storeInt hr₀
    · intro o' ho' hw' x' hx'
      obtain ⟨o, ho, rfl⟩ := List.mem_map.mp ho'
      rw [Obj.set_writable] at hw'
      obtain ⟨x, hx, e₁, e₂, -⟩ := Obj.mem_offsets_set hx'
      rw [Obj.set_addr, e₁, e₂]
      exact hh.write o ho hw' x hx
    · intro o' ho'
      obtain ⟨o, ho, rfl⟩ := List.mem_map.mp ho'
      rw [Obj.set_addr, Obj.set_size]
      exact hh.noWrap o ho
    · rw [List.pairwise_map]
      refine hh.apart.imp fun h' => ?_
      simp only [Obj.Apart, Obj.set_addr, Obj.set_size, Obj.set_writable]
      exact h'
    · intro b hb
      apply Mem.get?_storeInt_of_ne
      intro i hi e
      apply hb
      subst e
      have n₀ := hh.noWrap O hO
      obtain ⟨e₀, b₀⟩ := Obj.toNat_cell n₀ hx₀
      rw [hx₀w] at b₀
      unfold Obj.Covers
      rw [toNat_add_ofNat (O.addr + BitVec.ofNat 64 x₀.1) i (by omega), e₀]
      constructor <;> omega
  · split at hs <;> cases hs

/-- The cell at index `k` of an array. -/
theorem mem_offsets_words (w : Width) (xs : List w.type) (n k : Nat) (hk : k < xs.length) :
    (n + w.bytes * k, (⟨w, xs[k]⟩ : Cell)) ∈ offsets n (xs.map (Cell.mk w)) := by
  induction xs generalizing n k with
  | nil => cases hk
  | cons x xs ih =>
    cases k with
    | zero => simp [offsets]
    | succ k =>
      have := ih (n + w.bytes) k (by simpa using hk)
      simp only [List.map_cons, offsets, List.mem_cons, List.getElem_cons_succ]
      right
      rw [show n + w.bytes * (k + 1) = n + w.bytes + w.bytes * k by
        rw [Nat.mul_succ]; omega]
      exact this

/-- A load of each cell of each object of a heap that the memory holds. -/
theorem Heap.load_of_mem {policy : CpuPolicy} {h : Heap} {m : DataMem} {o : Obj}
    {x : Nat × Cell} (hh : h.Holds policy m) (ho : o ∈ h) (hx : x ∈ offsets 0 o.cells) :
    h.load (o.addr + BitVec.ofNat 64 x.1) x.2.w = .ok x.2.v := by
  have hg : (o.get (o.addr + BitVec.ofNat 64 x.1) x.2.w).isSome := by
    cases hgo : o.get (o.addr + BitVec.ofNat 64 x.1) x.2.w with
    | some _ => rfl
    | none =>
      unfold Obj.get at hgo
      have := List.findSome?_eq_none_iff.mp hgo x hx
      simp [Cell.get] at this
  unfold Heap.load
  split
  · rename_i v hf
    have hr := Heap.load_sound hh (show h.load _ _ = .ok v by unfold Heap.load; rw [hf])
    have hr' := hh.read o ho x hx
    rw [hr] at hr'
    cases hr'
    rfl
  · rename_i hf
    rw [List.findSome?_eq_none_iff.mp hf o ho] at hg
    cases hg

/-- A load of the element at index `k` of an array. -/
theorem Heap.load_words {policy : CpuPolicy} {h : Heap} {m : DataMem} {base : BitVec 64}
    {wr : Bool} {w : Width} {xs : List w.type} {k : Nat} (hh : h.Holds policy m)
    (ho : Obj.words base wr w xs ∈ h) (hk : k < xs.length) :
    h.load (base + BitVec.ofNat 64 (w.bytes * k)) w = .ok xs[k] := by
  have := Heap.load_of_mem hh ho (mem_offsets_words w xs 0 k hk)
  rw [Nat.zero_add] at this
  exact this

/-- The read of the memory at index `k` of an array. -/
theorem Heap.readRam_words {policy : CpuPolicy} {h : Heap} {m : DataMem} {base : BitVec 64}
    {wr : Bool} {w : Width} {xs : List w.type} {k : Nat} (hh : h.Holds policy m)
    (ho : Obj.words base wr w xs ∈ h) (hk : k < xs.length) :
    readRam policy m (base + BitVec.ofNat 64 (w.bytes * k)) w = .ok xs[k] :=
  Heap.load_sound hh (Heap.load_words hh ho hk)

/-- A load of the word at index `i` of an array of words. -/
theorem Heap.load_words64 {policy : CpuPolicy} {h : Heap} {m : DataMem} {base : BitVec 64}
    {wr : Bool} {xs : List (BitVec 64)} {i : BitVec 64} (hh : h.Holds policy m)
    (ho : Obj.words base wr .W64 xs ∈ h) (hi : i.toNat < xs.length) :
    h.load (base + 8 * i) .W64 = .ok xs[i.toNat] := by
  have e : BitVec.ofNat 64 (Width.W64.bytes * i.toNat) = 8 * i := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_mul]
  have := Heap.load_words (w := .W64) hh ho hi
  rw [e] at this
  exact this

theorem words_bytes (w : Width) (xs : List w.type) :
    ((xs.map (Cell.mk w)).map fun c => c.w.bytes).sum = w.bytes * xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, ih, List.length_cons]
    rw [Nat.mul_succ]
    omega

/-- In a heap with only an array, a load after the end of the array is stuck. -/
theorem Heap.load_words_stuck (base : BitVec 64) (wr : Bool) (w : Width) (xs : List w.type)
    (k : Nat) (hk : xs.length ≤ k) (hlt : base.toNat + w.bytes * k < 2 ^ 64) :
    ∃ why, Heap.load [Obj.words base wr w xs] (base + BitVec.ofNat 64 (w.bytes * k)) w =
      .stuck why := by
  have hn : List.findSome? (fun o => o.get (base + BitVec.ofNat 64 (w.bytes * k)) w)
      [Obj.words base wr w xs] = none := by
    rw [List.findSome?_eq_none_iff]
    intro o ho
    rw [List.mem_singleton] at ho
    subst ho
    unfold Obj.get
    rw [List.findSome?_eq_none_iff]
    intro x hx
    split
    · rename_i e
      exfalso
      have hb := offsets_bound hx
      simp only [Obj.words, words_bytes] at hb
      have hmul : w.bytes * xs.length ≤ w.bytes * k := Nat.mul_le_mul_left _ hk
      have hpos := width_bytes_pos x.2.w
      have := congrArg BitVec.toNat e
      simp only [Obj.words] at this
      rw [toNat_add_ofNat _ _ (by omega), toNat_add_ofNat _ _ hlt] at this
      omega
    · rfl
  exact ⟨_, by unfold Heap.load; rw [hn]⟩

end Lift.Sem
