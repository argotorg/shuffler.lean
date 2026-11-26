module

public import Lift.Sem.HeapLemmas
public import Lift.Sem.HeapBytes

@[expose] public section

/-! The cells of an object by byte offset (task UP-OBJ): `cellGet cs d w` is the value of the cell of width `w` at the
byte offset `d` of the cells `cs`, and `cellSet cs d w v` writes it. A load or a store at `a` on an object `o` is the
access at the offset `(a - o.addr).toNat`. The rules of `cellGet` and `cellSet` on `::`, `++` and `flatMap` (an array
of elements of one size) take the offset as a natural number, so that `omega` decides their side conditions; they
hold for each record and each offset of the `Encode` layout, padding included (padding is a cell).

`Heap.Found a w v h` and `Heap.StoreAt a w v h h'` say which object of `h` has the cell; a search over the list proves
them (`heap_found` in `Lift/Tactic/LoopClose.lean`). Under `Heap.Holds`, a load gives the value of the cell
(`Heap.load_of_found`) and a store changes only that cell (`Heap.store_of_storeAt`): a writable object is apart from
the other objects. -/

namespace Lift.Sem

open Lift.P2.Total

/-- The number of bytes of the cells. -/
def cellsSize (cs : List Cell) : Nat := (cs.map fun c => c.w.bytes).sum

/-- The value of the cell of width `w` that starts at the byte offset `d` of `cs`. -/
def cellGet : List Cell → Nat → (w : Width) → Option w.type
  | [], _, _ => none
  | c :: cs, d, w => if d < c.w.bytes then (if d = 0 then c.get w else none) else cellGet cs (d - c.w.bytes) w

/-- The cells `cs` with the value `v` in the cell of width `w` that starts at the byte offset `d`. -/
def cellSet : List Cell → Nat → (w : Width) → w.type → List Cell
  | [], _, _, _ => []
  | c :: cs, d, w, v =>
    if d < c.w.bytes then (if d = 0 ∧ c.w = w then ⟨w, v⟩ else c) :: cs else c :: cellSet cs (d - c.w.bytes) w v

/-! ### The cells of an offset -/

theorem cellsSize_nil : cellsSize [] = 0 := rfl

theorem cellsSize_cons (c : Cell) (cs : List Cell) : cellsSize (c :: cs) = c.w.bytes + cellsSize cs := rfl

theorem cellsSize_append (l₁ l₂ : List Cell) : cellsSize (l₁ ++ l₂) = cellsSize l₁ + cellsSize l₂ := by
  simp [cellsSize]

theorem cellsSize_flatMap {α : Type} (l : List α) (g : α → List Cell) :
    cellsSize (l.flatMap g) = (l.map fun x => cellsSize (g x)).sum := by
  induction l with
  | nil => rfl
  | cons x l ih => simp only [List.flatMap_cons, cellsSize_append, ih, List.map_cons, List.sum_cons]

theorem sum_map_const {α : Type} (l : List α) (c : Nat) : (l.map fun _ => c).sum = l.length * c := by
  induction l with
  | nil => simp
  | cons x l ih => simp [ih, Nat.succ_mul, Nat.add_comm]

theorem cellsSize_eq (cs : List Cell) : (cs.map fun c => c.w.bytes).sum = cellsSize cs := rfl

/-- The size of an object is the size of its cells (for the bound `Holds.noWrap` of each object). -/
theorem Obj.size_eq_cellsSize (o : Obj) : o.size = cellsSize o.cells := rfl

theorem cellGet_nil (d : Nat) (w : Width) : cellGet [] d w = none := rfl

theorem cellGet_cons_zero (c : Cell) (cs : List Cell) (w : Width) : cellGet (c :: cs) 0 w = c.get w := by
  simp [cellGet, width_bytes_pos]

theorem cellGet_cons_ge {c : Cell} {cs : List Cell} {d : Nat} (w : Width) (h : c.w.bytes ≤ d) :
    cellGet (c :: cs) d w = cellGet cs (d - c.w.bytes) w := by
  simp [cellGet, Nat.not_lt.mpr h]

theorem cellGet_cons_mid {c : Cell} {cs : List Cell} {d : Nat} (w : Width) (h0 : 0 < d) (h : d < c.w.bytes) :
    cellGet (c :: cs) d w = none := by
  simp [cellGet, h, Nat.ne_of_gt h0]

theorem cellGet_append_left {l₁ l₂ : List Cell} {d : Nat} (w : Width) (h : d < cellsSize l₁) :
    cellGet (l₁ ++ l₂) d w = cellGet l₁ d w := by
  induction l₁ generalizing d with
  | nil => simp [cellsSize] at h
  | cons c cs ih =>
    rw [cellsSize_cons] at h
    simp only [List.cons_append, cellGet]
    split
    · rfl
    · exact ih (by omega)

theorem cellGet_append_right {l₁ l₂ : List Cell} {d : Nat} (w : Width) (h : cellsSize l₁ ≤ d) :
    cellGet (l₁ ++ l₂) d w = cellGet l₂ (d - cellsSize l₁) w := by
  induction l₁ generalizing d with
  | nil => rfl
  | cons c cs ih =>
    rw [cellsSize_cons] at h
    simp only [List.cons_append, cellGet]
    rw [if_neg (by omega), ih (by omega), cellsSize_cons, Nat.sub_add_eq]

/-- The cell at the offset `k * s + r` of an array of elements of `s` bytes: the offset `r` of the element `k`. -/
theorem cellGet_flatMap {α : Type} {l : List α} {g : α → List Cell} {s k r : Nat} (w : Width)
    (hs : ∀ x, cellsSize (g x) = s) (hk : k < l.length) (hr : r < s) :
    cellGet (l.flatMap g) (k * s + r) w = cellGet (g l[k]) r w := by
  induction l generalizing k with
  | nil => cases hk
  | cons x l ih =>
    rw [List.flatMap_cons]
    cases k with
    | zero =>
      rw [cellGet_append_left w (by rw [hs]; omega)]
      simp
    | succ k =>
      rw [cellGet_append_right w (by rw [hs]; rw [Nat.succ_mul]; omega), hs,
        show (k + 1) * s + r - s = k * s + r by rw [Nat.succ_mul]; omega, ih (by simpa using hk)]
      simp

theorem cellGet_flatMap_zero {α : Type} {l : List α} {g : α → List Cell} {s k : Nat} (w : Width)
    (hs : ∀ x, cellsSize (g x) = s) (hk : k < l.length) (h0 : 0 < s) :
    cellGet (l.flatMap g) (k * s) w = cellGet (g l[k]) 0 w := by
  have := cellGet_flatMap (r := 0) w hs hk h0
  simpa using this

theorem cellSet_nil (d : Nat) (w : Width) (v : w.type) : cellSet [] d w v = [] := rfl

theorem cellSet_cons_zero (c : Cell) (cs : List Cell) (w : Width) (v : w.type) :
    cellSet (c :: cs) 0 w v = (if c.w = w then ⟨w, v⟩ else c) :: cs := by
  simp [cellSet, width_bytes_pos]

theorem cellSet_cons_ge {c : Cell} {cs : List Cell} {d : Nat} (w : Width) (v : w.type) (h : c.w.bytes ≤ d) :
    cellSet (c :: cs) d w v = c :: cellSet cs (d - c.w.bytes) w v := by
  simp [cellSet, Nat.not_lt.mpr h]

theorem cellSet_append_left {l₁ l₂ : List Cell} {d : Nat} (w : Width) (v : w.type) (h : d < cellsSize l₁) :
    cellSet (l₁ ++ l₂) d w v = cellSet l₁ d w v ++ l₂ := by
  induction l₁ generalizing d with
  | nil => simp [cellsSize] at h
  | cons c cs ih =>
    rw [cellsSize_cons] at h
    simp only [List.cons_append, cellSet]
    split
    · rfl
    · rw [ih (by omega)]; rfl

theorem cellSet_append_right {l₁ l₂ : List Cell} {d : Nat} (w : Width) (v : w.type) (h : cellsSize l₁ ≤ d) :
    cellSet (l₁ ++ l₂) d w v = l₁ ++ cellSet l₂ (d - cellsSize l₁) w v := by
  induction l₁ generalizing d with
  | nil => rfl
  | cons c cs ih =>
    rw [cellsSize_cons] at h
    simp only [List.cons_append, cellSet]
    rw [if_neg (by omega), ih (by omega), cellsSize_cons, Nat.sub_add_eq]

/-- A store at the offset `k * s + r` of an array of elements of `s` bytes: the elements before `k`, the store in the
element `k`, and the elements after `k`. -/
theorem cellSet_flatMap {α : Type} {l : List α} {g : α → List Cell} {s k r : Nat} (w : Width) (v : w.type)
    (hs : ∀ x, cellsSize (g x) = s) (hk : k < l.length) (hr : r < s) :
    cellSet (l.flatMap g) (k * s + r) w v =
      (l.take k).flatMap g ++ cellSet (g l[k]) r w v ++ (l.drop (k + 1)).flatMap g := by
  induction l generalizing k with
  | nil => cases hk
  | cons x l ih =>
    rw [List.flatMap_cons]
    cases k with
    | zero =>
      rw [cellSet_append_left w v (by rw [hs]; omega)]
      simp
    | succ k =>
      rw [cellSet_append_right w v (by rw [hs]; rw [Nat.succ_mul]; omega), hs,
        show (k + 1) * s + r - s = k * s + r by rw [Nat.succ_mul]; omega, ih (by simpa using hk)]
      simp

theorem cellSet_flatMap_zero {α : Type} {l : List α} {g : α → List Cell} {s k : Nat} (w : Width) (v : w.type)
    (hs : ∀ x, cellsSize (g x) = s) (hk : k < l.length) (h0 : 0 < s) :
    cellSet (l.flatMap g) (k * s) w v =
      (l.take k).flatMap g ++ cellSet (g l[k]) 0 w v ++ (l.drop (k + 1)).flatMap g := by
  have := cellSet_flatMap (r := 0) w v hs hk h0
  simpa using this

/-- An array after a store to its element `k`: the elements before `k`, the new element, and the elements after `k`;
the form of `cellSet_flatMap`. -/
theorem flatMap_set {α : Type} {l : List α} {g : α → List Cell} {k : Nat} (x : α) (hk : k < l.length) :
    (l.set k x).flatMap g = (l.take k).flatMap g ++ g x ++ (l.drop (k + 1)).flatMap g := by
  rw [List.set_eq_take_append_cons_drop, if_pos hk]
  simp [List.flatMap_append]

theorem Cell.get_self (w : Width) (v : w.type) : (Cell.mk w v).get w = some v := by
  simp [Cell.get]

theorem Cell.get_ne {w w' : Width} (v : w.type) (h : w ≠ w') : (Cell.mk w v).get w' = none := by
  simp [Cell.get, h]

/-! ### The cells of an offset and the offsets of the cells -/

theorem mem_offsets_of_cellGet {cs : List Cell} {d : Nat} {w : Width} {v : w.type} (n : Nat)
    (h : cellGet cs d w = some v) : (n + d, (⟨w, v⟩ : Cell)) ∈ offsets n cs := by
  induction cs generalizing n d with
  | nil => cases h
  | cons c cs ih =>
    simp only [cellGet] at h
    split at h
    · split at h
      · rename_i _ h0
        subst h0
        have := Cell.get_eq_some.mp h
        simp [offsets, this]
      · cases h
    · have := ih (n + c.w.bytes) h
      simp only [offsets, List.mem_cons]
      right
      rwa [show n + c.w.bytes + (d - c.w.bytes) = n + d by omega] at this

theorem mem_offsets_of_cellGet_isSome {cs : List Cell} {d : Nat} {w : Width} (n : Nat)
    (h : (cellGet cs d w).isSome) : ∃ c : Cell, c.w = w ∧ (n + d, c) ∈ offsets n cs := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h
  exact ⟨⟨w, v⟩, rfl, mem_offsets_of_cellGet n hv⟩

theorem cellGet_lt_size {cs : List Cell} {d : Nat} {w : Width} (h : (cellGet cs d w).isSome) : d < cellsSize cs := by
  obtain ⟨c, _, hc⟩ := mem_offsets_of_cellGet_isSome 0 h
  have h1 := offsets_bound hc
  have h2 := width_bytes_pos c.w
  simp only [cellsSize]
  simp only at h1
  omega

theorem setCells_eq_cellSet (base : BitVec 64) (w : Width) (v : w.type) :
    ∀ (cs : List Cell) (n d : Nat), n + cellsSize cs ≤ 2 ^ 64 → n + d < 2 ^ 64 →
      setCells base (base + BitVec.ofNat 64 (n + d)) w v n cs = cellSet cs d w v
  | [], _, _, _, _ => rfl
  | c :: cs, n, d, hb, hd => by
    rw [cellsSize_cons] at hb
    have hcs : cellsSize cs = (cs.map fun c => c.w.bytes).sum := rfl
    have hp := width_bytes_pos c.w
    simp only [setCells, cellSet]
    have he : (base + BitVec.ofNat 64 n = base + BitVec.ofNat 64 (n + d)) ↔ d = 0 := by
      constructor
      · intro e
        have := ofNat_inj_of_lt (by omega) hd ((BitVec.add_right_inj _).mp e)
        omega
      · intro e; subst e; rfl
    by_cases hlt : d < c.w.bytes
    · rw [if_pos hlt]
      congr 1
      · by_cases h0 : d = 0
        · simp [h0]
        · simp [he, h0]
      · rw [setCells_of_no_match]
        intro x hx ⟨e, _⟩
        have := offsets_bound hx
        have := width_bytes_pos x.2.w
        have := ofNat_inj_of_lt (by omega) hd ((BitVec.add_right_inj _).mp e)
        omega
    · rw [if_neg hlt]
      have h0 : ¬ d = 0 := by omega
      simp only [he, h0, false_and, ↓reduceIte]
      congr 1
      rw [show n + d = n + c.w.bytes + (d - c.w.bytes) by omega]
      exact setCells_eq_cellSet base w v cs (n + c.w.bytes) (d - c.w.bytes) (by omega) (by omega)

/-- The address of the offset of `a` in an object at `base`. -/
theorem add_toNat_sub (base a : BitVec 64) : base + BitVec.ofNat 64 (a - base).toNat = a := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  bv_omega

/-! ### Loads and stores on the objects of a heap -/

/-- The object of `h` that has the cell of width `w` and value `v` at `a`. -/
inductive Heap.Found (a : BitVec 64) (w : Width) (v : w.type) : Heap → Prop
  | head {o : Obj} {t : Heap} : cellGet o.cells (a - o.addr).toNat w = some v → Heap.Found a w v (o :: t)
  | tail {o : Obj} {t : Heap} : Heap.Found a w v t → Heap.Found a w v (o :: t)

theorem Heap.Found.mem {a : BitVec 64} {w : Width} {v : w.type} {h : Heap} (hf : Heap.Found a w v h) :
    ∃ o ∈ h, cellGet o.cells (a - o.addr).toNat w = some v := by
  induction hf with
  | head hc => exact ⟨_, List.mem_cons_self .., hc⟩
  | tail _ ih =>
    obtain ⟨o, ho, hc⟩ := ih
    exact ⟨o, List.mem_cons_of_mem _ ho, hc⟩

/-- A load of a cell of an object of a heap that the memory holds. -/
theorem Heap.load_of_found {policy : CpuPolicy} {h : Heap} {m : DataMem} {a : BitVec 64} {w : Width} {v : w.type}
    (hh : h.Holds policy m) (hf : Heap.Found a w v h) : h.load a w = .ok v := by
  obtain ⟨o, ho, hc⟩ := hf.mem
  have := Heap.load_of_mem hh ho (mem_offsets_of_cellGet 0 hc)
  rw [Nat.zero_add, add_toNat_sub] at this
  exact this

theorem Heap.loadB_of_found {policy : CpuPolicy} {h : Heap} {m : DataMem} {a : BitVec 64} {w : Width}
    {v : w.type} (hh : h.Holds policy m) (hf : Heap.Found a w v h) : h.loadB a w = .ok v :=
  Heap.loadB_of_load (Heap.load_of_found hh hf)

/-- The object after a store of `v` to its cell of width `w` at `a`. -/
def Obj.setAt (a : BitVec 64) (w : Width) (v : w.type) (o : Obj) : Obj :=
  { o with cells := cellSet o.cells (a - o.addr).toNat w v }

/-- `h'` is `h` after a store of `v` to the cell of width `w` at `a` of a writable object of `h`. -/
inductive Heap.StoreAt (a : BitVec 64) (w : Width) (v : w.type) : Heap → Heap → Prop
  | head {o : Obj} {t : Heap} : o.writable = true → (cellGet o.cells (a - o.addr).toNat w).isSome →
      Heap.StoreAt a w v (o :: t) (o.setAt a w v :: t)
  | tail {o : Obj} {t t' : Heap} : Heap.StoreAt a w v t t' → Heap.StoreAt a w v (o :: t) (o :: t')

theorem Heap.StoreAt.mem {a : BitVec 64} {w : Width} {v : w.type} {h h' : Heap} (hs : Heap.StoreAt a w v h h') :
    ∃ o ∈ h, o.writable = true ∧ (cellGet o.cells (a - o.addr).toNat w).isSome := by
  induction hs with
  | head hw hc => exact ⟨_, List.mem_cons_self .., hw, hc⟩
  | tail _ ih =>
    obtain ⟨o, ho, hw, hc⟩ := ih
    exact ⟨o, List.mem_cons_of_mem _ ho, hw, hc⟩

theorem Obj.set_eq_setAt {o : Obj} {a : BitVec 64} {w : Width} (v : w.type) (hw : o.writable = true)
    (hn : o.addr.toNat + o.size ≤ 2 ^ 64) (hc : (cellGet o.cells (a - o.addr).toNat w).isSome) :
    o.set a w v = o.setAt a w v := by
  have hlt := cellGet_lt_size hc
  have hsz : o.size = cellsSize o.cells := rfl
  unfold Obj.set Obj.setAt
  simp only [hw, ↓reduceIte]
  have := setCells_eq_cellSet o.addr w v o.cells 0 (a - o.addr).toNat (by omega) (by omega)
  simp only [Nat.zero_add, add_toNat_sub] at this
  rw [this]

/-- Under `Holds`, an object is not twice in the heap when it is writable and has a cell. -/
theorem not_mem_of_holds_cell {policy : CpuPolicy} {o : Obj} {t : Heap} {m : DataMem}
    (hh : Heap.Holds policy (o :: t) m) (hw : o.writable = true) {d : Nat} {w : Width}
    (hc : (cellGet o.cells d w).isSome) : o ∉ t :=
  not_mem_of_holds hh hw (by have := cellGet_lt_size hc; exact Nat.lt_of_le_of_lt (Nat.zero_le _) this)

/-- A store to a cell of a writable object of a heap that the memory holds: only that cell changes. -/
theorem Heap.store_of_storeAt {policy : CpuPolicy} {h h' : Heap} {m : DataMem} {a : BitVec 64} {w : Width}
    {v : w.type} (hh : h.Holds policy m) (hs : Heap.StoreAt a w v h h') : h.store a w v = .ok h' := by
  obtain ⟨O, hO, hOw, hOc⟩ := hs.mem
  obtain ⟨⟨cw, cv⟩, hcw, hx₀⟩ := mem_offsets_of_cellGet_isSome 0 hOc
  dsimp only at hcw
  subst hcw
  have hst := Heap.store_cell hO hOw hx₀ v
  simp only [Nat.zero_add, add_toNat_sub] at hst
  rw [hst]
  congr 1
  -- each object other than `O` does not change; `O` takes the store
  have key : ∀ (h₀ h₁ : Heap), h₀.Sublist h → Heap.StoreAt a cw v h₀ h₁ → h₀.map (Obj.set a cw v) = h₁ := by
    intro h₀ h₁ hsub hs₀
    induction hs₀ with
    | @head o t hw hc =>
      have hh₀ := hh.sublist hsub
      have hno := not_mem_of_holds_cell hh₀ hw hc
      rw [List.map_cons, Obj.set_eq_setAt v hw (hh₀.noWrap o (List.mem_cons_self ..)) hc]
      congr 1
      obtain ⟨⟨cw, cv⟩, hc'w, hx'⟩ := mem_offsets_of_cellGet_isSome 0 hc
      dsimp only at hc'w
      subst hc'w
      have e := add_toNat_sub o.addr a
      conv => rhs; rw [← List.map_id t]
      apply List.map_congr_left
      intro p hp
      have hne : p ≠ o := fun e => hno (e ▸ hp)
      have := hh₀.set_other (List.mem_cons_self ..) hw hx' (List.mem_cons_of_mem _ hp) hne v
      rw [Nat.zero_add, add_toNat_sub] at this
      exact this
    | @tail o t t' hs₁ ih =>
      have hh₀ := hh.sublist hsub
      rw [List.map_cons, ih ((List.sublist_cons_self o t).trans hsub)]
      congr 1
      obtain ⟨O', hO', hO'w, hO'c⟩ := hs₁.mem
      obtain ⟨⟨cw, cv⟩, hc'w, hx'⟩ := mem_offsets_of_cellGet_isSome 0 hO'c
      dsimp only at hc'w
      subst hc'w
      have hne : o ≠ O' := by
        intro e
        subst e
        have hh₁ : Heap.Holds policy (o :: t) m := hh₀
        exact not_mem_of_holds_cell hh₁ hO'w hO'c hO'
      have := hh₀.set_other (List.mem_cons_of_mem _ hO') hO'w hx' (List.mem_cons_self ..) hne v
      rw [Nat.zero_add, add_toNat_sub] at this
      exact this
  exact key h h' (List.Sublist.refl h) hs

/-- After a store, a memory holds the new heap (`Heap.store_sound`): the next load or store of a chain has a `Holds`. -/
theorem Heap.store_holds {policy : CpuPolicy} {h h' : Heap} {m : DataMem} {a : BitVec 64} {w : Width} {v : w.type}
    (hh : h.Holds policy m) (hs : h.store a w v = .ok h') : ∃ m', h'.Holds policy m' :=
  let ⟨m', _, hm', _⟩ := Heap.store_sound hh hs
  ⟨m', hm'⟩

theorem Heap.storeB_of_storeAt {policy : CpuPolicy} {h h' : Heap} {m : DataMem} {a : BitVec 64} {w : Width}
    {v : w.type} (hh : h.Holds policy m) (hs : Heap.StoreAt a w v h h') : h.storeB a w v = .ok h' :=
  Heap.storeB_of_store (Heap.store_of_storeAt hh hs)

end Lift.Sem
