module

public import Lift.Sem.Heap

@[expose] public section

namespace Lift.Sem

open Lift.P2.Total

/-! ### A sub-heap holds -/

/-- A sub-heap of a heap that the memory holds is held by the memory. -/
theorem Heap.Holds.sublist {policy : CpuPolicy} {h h' : Heap} {m : DataMem}
    (hh : h.Holds policy m) (hs : h'.Sublist h) : h'.Holds policy m where
  read o ho := hh.read o (hs.subset ho)
  write o ho := hh.write o (hs.subset ho)
  noWrap o ho := hh.noWrap o (hs.subset ho)
  apart := hh.apart.sublist hs

/-! ### A load of a cell -/

/-- A load of a cell of an object of a heap that the memory holds. -/
theorem Heap.load_cell {policy : CpuPolicy} {h : Heap} {m : DataMem} {o : Obj} {off : Nat}
    {c : Cell} (hh : h.Holds policy m) (ho : o ∈ h) (hc : (off, c) ∈ offsets 0 o.cells) :
    h.load (o.addr + BitVec.ofNat 64 off) c.w = .ok c.v :=
  Heap.load_of_mem hh ho hc

/-! ### Helpers on cells -/

/-- The offset of the cell at index `i`. -/
def Obj.fieldOff (o : Obj) (i : Nat) : Nat := ((o.cells.take i).map fun c => c.w.bytes).sum

theorem sum_take_le (cs : List Cell) (i : Nat) :
    ((cs.take i).map fun c => c.w.bytes).sum ≤ (cs.map fun c => c.w.bytes).sum := by
  have := List.take_append_drop i cs
  conv => rhs; rw [← this]
  simp only [List.map_append, List.sum_append]
  omega

/-- The cell at index `i` and its offset. -/
theorem mem_offsets_index (cs : List Cell) (n i : Nat) (hi : i < cs.length) :
    (n + ((cs.take i).map fun c => c.w.bytes).sum, cs[i]) ∈ offsets n cs := by
  induction cs generalizing n i with
  | nil => cases hi
  | cons c cs ih =>
    cases i with
    | zero => simp [offsets]
    | succ i =>
      have := ih (n + c.w.bytes) i (by simpa using hi)
      simp only [offsets, List.mem_cons, List.take_succ_cons, List.map_cons, List.sum_cons,
        List.getElem_cons_succ]
      right
      rw [show n + (c.w.bytes + ((cs.take i).map fun c => c.w.bytes).sum) =
        n + c.w.bytes + ((cs.take i).map fun c => c.w.bytes).sum by omega]
      exact this

/-- No cell changes when no cell matches the store. -/
theorem setCells_of_no_match (base a : BitVec 64) (w : Width) (v : w.type) (n : Nat)
    (cs : List Cell)
    (h : ∀ x ∈ offsets n cs, ¬ (base + BitVec.ofNat 64 x.1 = a ∧ x.2.w = w)) :
    setCells base a w v n cs = cs := by
  induction cs generalizing n with
  | nil => rfl
  | cons c cs ih =>
    simp only [setCells]
    have hn := h (n, c) (by simp [offsets])
    simp only [hn, ↓reduceIte]
    rw [ih (n + c.w.bytes) (fun x hx => h x (by simp [offsets, hx]))]

theorem ofNat_inj_of_lt {n k : Nat} (hn : n < 2 ^ 64) (hk : k < 2 ^ 64)
    (e : BitVec.ofNat 64 n = BitVec.ofNat 64 k) : n = k := by
  have := congrArg BitVec.toNat e
  rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hk] at this

/-- In an object that does not wrap, a store to the cell at index `i` changes only this cell. -/
theorem setCells_at (base : BitVec 64) (w : Width) (v : w.type) (cs : List Cell) (n i : Nat)
    (hi : i < cs.length) (hw : cs[i].w = w)
    (hb : base.toNat + n + (cs.map fun c => c.w.bytes).sum ≤ 2 ^ 64) :
    setCells base (base + BitVec.ofNat 64 (n + ((cs.take i).map fun c => c.w.bytes).sum)) w v n cs
      = cs.set i ⟨w, v⟩ := by
  induction cs generalizing n i with
  | nil => cases hi
  | cons c cs ih =>
    have hpos := width_bytes_pos c.w
    simp only [List.map_cons, List.sum_cons] at hb
    cases i with
    | zero =>
      simp only [List.take_zero, List.map_nil, List.sum_nil, Nat.add_zero, setCells,
        List.set_cons_zero]
      have hc : c.w = w := hw
      subst hc
      simp only [and_self, ↓reduceIte]
      rw [setCells_of_no_match]
      intro x hx ⟨e, _⟩
      have hx' := (offsets_bound hx).1
      have hx'' := (offsets_bound hx).2
      have := width_bytes_pos x.2.w
      have := ofNat_inj_of_lt (by omega) (by omega) ((BitVec.add_right_inj _).mp e)
      omega
    | succ i =>
      have hi' : i < cs.length := by simpa using hi
      have hs := offsets_bound (mem_offsets_index cs 0 i hi')
      have := width_bytes_pos cs[i].w
      simp only [Nat.zero_add] at hs
      have hne : ¬ (base + BitVec.ofNat 64 n = base + BitVec.ofNat 64
          (n + (c.w.bytes + ((cs.take i).map fun c => c.w.bytes).sum)) ∧ c.w = w) := by
        rintro ⟨e, _⟩
        have := ofNat_inj_of_lt (by omega) (by omega) ((BitVec.add_right_inj _).mp e)
        omega
      simp only [List.take_succ_cons, List.map_cons, List.sum_cons, setCells,
        List.set_cons_succ, hne, ↓reduceIte]
      rw [show n + (c.w.bytes + ((cs.take i).map fun c => c.w.bytes).sum) =
        n + c.w.bytes + ((cs.take i).map fun c => c.w.bytes).sum by omega,
        ih (n + c.w.bytes) i hi' (by simpa using hw) (by omega)]

/-- A store to the cell at index `i` of a writable object that does not wrap. -/
theorem Obj.set_field {o : Obj} (hw : o.writable) (hn : o.addr.toNat + o.size ≤ 2 ^ 64)
    (i : Nat) (hi : i < o.cells.length) (w : Width) (hc : o.cells[i].w = w) (v : w.type) :
    o.set (o.addr + BitVec.ofNat 64 (o.fieldOff i)) w v =
      { o with cells := o.cells.set i ⟨w, v⟩ } := by
  unfold Obj.set
  simp only [hw, ↓reduceIte]
  have := setCells_at o.addr w v o.cells 0 i hi hc (by simpa [Obj.size] using hn)
  simp only [Nat.zero_add] at this
  unfold Obj.fieldOff
  rw [this]

theorem Obj.get_isSome_of_mem {o : Obj} {x : Nat × Cell} (hx : x ∈ offsets 0 o.cells) :
    (o.get (o.addr + BitVec.ofNat 64 x.1) x.2.w).isSome := by
  cases hgo : o.get (o.addr + BitVec.ofNat 64 x.1) x.2.w with
  | some _ => rfl
  | none =>
    unfold Obj.get at hgo
    have := List.findSome?_eq_none_iff.mp hgo x hx
    simp [Cell.get] at this

/-- The store to a cell of a writable object succeeds. -/
theorem Heap.store_cell {h : Heap} {O : Obj} {x₀ : Nat × Cell} (hO : O ∈ h) (hw : O.writable)
    (hx₀ : x₀ ∈ offsets 0 O.cells) (v : x₀.2.w.type) :
    h.store (O.addr + BitVec.ofNat 64 x₀.1) x₀.2.w v =
      .ok (h.map (Obj.set (O.addr + BitVec.ofNat 64 x₀.1) x₀.2.w v)) := by
  unfold Heap.store
  have hc : (h.any fun o => o.writable && (o.get (O.addr + BitVec.ofNat 64 x₀.1) x₀.2.w).isSome)
      = true :=
    List.any_eq_true.mpr ⟨O, hO, by simp [hw, Obj.get_isSome_of_mem hx₀]⟩
  simp only [hc, ↓reduceIte]

/-- The result of a store: the heap, and a writable object with a cell at the address. -/
theorem Heap.store_ok {h h' : Heap} {a : BitVec 64} {w : Width} {v : w.type}
    (hs : h.store a w v = .ok h') :
    h' = h.map (Obj.set a w v) ∧ ∃ O ∈ h, O.writable ∧ ∃ x ∈ offsets 0 O.cells,
      O.addr + BitVec.ofNat 64 x.1 = a ∧ x.2.w = w := by
  unfold Heap.store at hs
  split at hs
  · rename_i hc
    cases hs
    refine ⟨rfl, ?_⟩
    obtain ⟨O, hO, hc⟩ := List.any_eq_true.mp hc
    simp only [Bool.and_eq_true, Option.isSome_iff_exists] at hc
    obtain ⟨hw, v₀, hg⟩ := hc
    obtain ⟨x, hx, ha, hc₀⟩ := Obj.get_some hg
    exact ⟨O, hO, hw, x, hx, ha, by rw [hc₀]⟩
  · split at hs <;> cases hs

/-! ### The replacement of an object -/

/-- `h'` is `h` with the object `O` replaced by `O'` and each other object unchanged. -/
inductive Heap.Replaces (O O' : Obj) : Heap → Heap → Prop
  | nil : Heap.Replaces O O' [] []
  | here {t t' : Heap} : Heap.Replaces O O' t t' → Heap.Replaces O O' (O :: t) (O' :: t')
  | there {p : Obj} {t t' : Heap} : p ≠ O → Heap.Replaces O O' t t' →
    Heap.Replaces O O' (p :: t) (p :: t')

theorem Heap.Replaces.map {O : Obj} {f : Obj → Obj} {h : Heap}
    (hf : ∀ p ∈ h, p ≠ O → f p = p) : Heap.Replaces O (f O) h (h.map f) := by
  induction h with
  | nil => exact .nil
  | cons p t ih =>
    have ih' := ih fun q hq => hf q (List.mem_cons_of_mem _ hq)
    by_cases hp : p = O
    · subst hp; exact .here ih'
    · rw [List.map_cons, hf p (List.mem_cons_self ..) hp]
      exact .there hp ih'

/-- The new object is in the new heap. -/
theorem Heap.Replaces.mem_new {O O' : Obj} {h h' : Heap} (hr : Heap.Replaces O O' h h')
    (ho : O ∈ h) : O' ∈ h' := by
  induction hr with
  | nil => cases ho
  | here _ _ => exact List.mem_cons_self ..
  | there hne _ ih =>
    rcases List.mem_cons.mp ho with rfl | ho
    · exact absurd rfl hne
    · exact List.mem_cons_of_mem _ (ih ho)

/-- Each other object is in the new heap. -/
theorem Heap.Replaces.mem_of_ne {O O' p : Obj} {h h' : Heap} (hr : Heap.Replaces O O' h h')
    (hp : p ∈ h) (hne : p ≠ O) : p ∈ h' := by
  induction hr with
  | nil => cases hp
  | here _ ih =>
    rcases List.mem_cons.mp hp with rfl | hp
    · exact absurd rfl hne
    · exact List.mem_cons_of_mem _ (ih hp)
  | there _ _ ih =>
    rcases List.mem_cons.mp hp with rfl | hp
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (ih hp)

/-- A store to a cell leaves each other object unchanged. -/
theorem Heap.Holds.set_other {policy : CpuPolicy} {h : Heap} {m : DataMem}
    (hh : h.Holds policy m) {O p : Obj} {x₀ : Nat × Cell} (hO : O ∈ h) (hw : O.writable)
    (hx₀ : x₀ ∈ offsets 0 O.cells) (hp : p ∈ h) (hne : p ≠ O) (v : x₀.2.w.type) :
    p.set (O.addr + BitVec.ofNat 64 x₀.1) x₀.2.w v = p := by
  unfold Obj.set
  split
  · show ({ p with cells := _ } : Obj) = p
    rw [setCells_of_no_match]
    intro x hx ⟨e, _⟩
    have hd := hh.disjoint hO hw hx₀ hp hx (fun h => hne h.1)
    have := hd 0 (width_bytes_pos _) 0 (width_bytes_pos _)
    apply this
    simpa using e.symm
  · rfl

/-! ### A store to a field of a record -/

/-- A store to the cell of width `w` at index `i` of a writable object: the new heap has the
object with that cell changed; each other object is unchanged. -/
theorem Heap.store_field {policy : CpuPolicy} {h : Heap} {m : DataMem} {o : Obj}
    (hh : h.Holds policy m) (ho : o ∈ h) (hw : o.writable) (i : Nat) (hi : i < o.cells.length)
    (w : Width) (hc : o.cells[i].w = w) (v : w.type) :
    ∃ h', h.store (o.addr + BitVec.ofNat 64 (o.fieldOff i)) w v = .ok h' ∧
      Heap.Replaces o { o with cells := o.cells.set i ⟨w, v⟩ } h h' := by
  subst hc
  have hx₀ : (o.fieldOff i, o.cells[i]) ∈ offsets 0 o.cells := by
    have := mem_offsets_index o.cells 0 i hi
    rw [Nat.zero_add] at this
    exact this
  refine ⟨_, Heap.store_cell ho hw hx₀ v, ?_⟩
  rw [← Obj.set_field hw (hh.noWrap o ho) i hi _ rfl v]
  exact Heap.Replaces.map fun p hp hne => hh.set_other ho hw hx₀ hp hne v

/-! ### A store to an array element -/

theorem words_fieldOff (w : Width) (xs : List w.type) (k : Nat) (hk : k ≤ xs.length) :
    (((xs.map (Cell.mk w)).take k).map fun c => c.w.bytes).sum = w.bytes * k := by
  induction xs generalizing k with
  | nil => simp at hk; subst hk; rfl
  | cons x xs ih =>
    cases k with
    | zero => rfl
    | succ k =>
      have := ih k (by simpa using hk)
      simp only [List.map_cons, List.take_succ_cons, List.sum_cons]
      rw [this, Nat.mul_succ]
      omega

/-- A store to the element at index `k` of a writable array: the new heap has the array with the
element changed; each other object is unchanged. -/
theorem Heap.store_words {policy : CpuPolicy} {h : Heap} {m : DataMem} {base : BitVec 64}
    {w : Width} {xs : List w.type} {k : Nat} (hh : h.Holds policy m)
    (ho : Obj.words base true w xs ∈ h) (hk : k < xs.length) (v : w.type) :
    ∃ h', h.store (base + BitVec.ofNat 64 (w.bytes * k)) w v = .ok h' ∧
      Heap.Replaces (Obj.words base true w xs) (Obj.words base true w (xs.set k v)) h h' := by
  have hk' : k < (Obj.words base true w xs).cells.length := by simpa [Obj.words] using hk
  obtain ⟨h', hs, hr⟩ := Heap.store_field hh ho rfl k hk' w (by simp [Obj.words]) v
  have e : (Obj.words base true w xs).fieldOff k = w.bytes * k :=
    words_fieldOff w xs k (Nat.le_of_lt hk)
  rw [e] at hs
  refine ⟨h', hs, ?_⟩
  simpa [Obj.words, List.map_set] using hr

/-- A store to the byte at index `i` of a writable byte array. -/
theorem Heap.store_words8 {policy : CpuPolicy} {h : Heap} {m : DataMem} {base : BitVec 64}
    {xs : List (BitVec 8)} {i : BitVec 64} (hh : h.Holds policy m)
    (ho : Obj.words base true .W8 xs ∈ h) (hi : i.toNat < xs.length) (v : BitVec 8) :
    ∃ h', h.store (base + i) .W8 v = .ok h' ∧
      Heap.Replaces (Obj.words base true .W8 xs) (Obj.words base true .W8 (xs.set i.toNat v))
        h h' := by
  have e : BitVec.ofNat 64 (Width.W8.bytes * i.toNat) = i := by
    apply BitVec.eq_of_toNat_eq
    simp [Width.bytes]
  have := Heap.store_words (w := .W8) hh ho hi v
  rw [e] at this
  exact this

/-- A store to the word at index `i` of a writable array of words. -/
theorem Heap.store_words64 {policy : CpuPolicy} {h : Heap} {m : DataMem} {base : BitVec 64}
    {xs : List (BitVec 64)} {i : BitVec 64} (hh : h.Holds policy m)
    (ho : Obj.words base true .W64 xs ∈ h) (hi : i.toNat < xs.length) (v : BitVec 64) :
    ∃ h', h.store (base + 8 * i) .W64 v = .ok h' ∧
      Heap.Replaces (Obj.words base true .W64 xs) (Obj.words base true .W64 (xs.set i.toNat v))
        h h' := by
  have e : BitVec.ofNat 64 (Width.W64.bytes * i.toNat) = 8 * i := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_mul]
  have := Heap.store_words (w := .W64) hh ho hi v
  rw [e] at this
  exact this

/-! ### A store keeps the other loads -/

/-- A store to the cell of width `w` at `a` does not change a load at another address or of
another width. -/
theorem Obj.get_set_of_ne (a a' : BitVec 64) (w w' : Width) (v : w.type) (o : Obj)
    (hne : ¬ (a' = a ∧ w' = w)) : (o.set a w v).get a' w' = o.get a' w' := by
  unfold Obj.set
  split
  · unfold Obj.get
    dsimp only
    rw [offsets_setCells, List.findSome?_map]
    congr 1
    funext x
    simp only [Function.comp]
    by_cases hc : o.addr + BitVec.ofNat 64 x.1 = a ∧ x.2.w = w
    · by_cases e : o.addr + BitVec.ofNat 64 x.1 = a'
      · have hw' : w' ≠ w := fun h => hne ⟨hc.1 ▸ e.symm, h⟩
        simp only [hc, and_self, ↓reduceIte]
        unfold Cell.get
        simp [Ne.symm hw', hc.2.symm ▸ Ne.symm hw']
      · have e' : ¬ a = a' := fun h => e (hc.1.trans h)
        simp [hc, e']
    · simp [hc]
  · rfl

/-- A store does not change a load at another address or of another width. -/
theorem Heap.load_store_of_ne {h h' : Heap} {a : BitVec 64} {w : Width} {v : w.type}
    (hs : h.store a w v = .ok h') (a' : BitVec 64) (w' : Width) (hne : ¬ (a' = a ∧ w' = w)) :
    h'.load a' w' = h.load a' w' := by
  obtain ⟨rfl, -⟩ := Heap.store_ok hs
  unfold Heap.load
  rw [List.findSome?_map]
  have : (fun o : Obj => (Obj.set a w v o).get a' w') = fun o => o.get a' w' :=
    funext fun o => Obj.get_set_of_ne a a' w w' v o hne
  simp only [Function.comp_def, this]

/-- A load at the address and width of a store gives the value. -/
theorem Heap.load_store_self {policy : CpuPolicy} {h h' : Heap} {m : DataMem} {a : BitVec 64}
    {w : Width} {v : w.type} (hh : h.Holds policy m) (hs : h.store a w v = .ok h') :
    h'.load a w = .ok v := by
  obtain ⟨he, O, hO, hw, x₀, hx₀, ha, hxw⟩ := Heap.store_ok hs
  obtain ⟨m', -, hh', -⟩ := Heap.store_sound hh hs
  have hmem : Obj.set a w v O ∈ h' := by rw [he]; exact List.mem_map_of_mem hO
  have hcell : (x₀.1, (⟨w, v⟩ : Cell)) ∈ offsets 0 (Obj.set a w v O).cells := by
    unfold Obj.set
    simp only [hw, ↓reduceIte]
    show _ ∈ offsets 0 (setCells O.addr a w v 0 O.cells)
    rw [offsets_setCells]
    exact List.mem_map.mpr ⟨x₀, hx₀, by simp [ha, hxw]⟩
  have := Heap.load_of_mem hh' hmem hcell
  rw [Obj.set_addr, ha] at this
  exact this

/-- A store to a cell does not change the load of another cell. -/
theorem Heap.load_store_cell_ne {policy : CpuPolicy} {h h' : Heap} {m : DataMem}
    (hh : h.Holds policy m) {O o : Obj} {x₀ x : Nat × Cell} (hO : O ∈ h) (hw : O.writable)
    (hx₀ : x₀ ∈ offsets 0 O.cells) (ho : o ∈ h) (hx : x ∈ offsets 0 o.cells)
    (hne : ¬ (o = O ∧ x = x₀)) (v : x₀.2.w.type)
    (hs : h.store (O.addr + BitVec.ofNat 64 x₀.1) x₀.2.w v = .ok h') :
    h'.load (o.addr + BitVec.ofNat 64 x.1) x.2.w = .ok x.2.v := by
  rw [Heap.load_store_of_ne hs _ _ ?_]
  · exact Heap.load_cell hh ho hx
  · rintro ⟨e, -⟩
    have hd := hh.disjoint hO hw hx₀ ho hx hne
    have := hd 0 (width_bytes_pos _) 0 (width_bytes_pos _)
    apply this
    simpa using e.symm

/-! ### A frame that composes -/

/-- A writable object of the heap has the byte `b`. -/
def Heap.Owned (h : Heap) (b : BitVec 64) : Prop := ∃ o ∈ h, o.writable ∧ o.Covers b

/-- A store does not change the owned bytes. -/
theorem Heap.owned_store {h h' : Heap} {a : BitVec 64} {w : Width} {v : w.type}
    (hs : h.store a w v = .ok h') (b : BitVec 64) : h'.Owned b ↔ h.Owned b := by
  obtain ⟨rfl, -⟩ := Heap.store_ok hs
  constructor
  · rintro ⟨o', ho', hw, hc⟩
    obtain ⟨o, ho, rfl⟩ := List.mem_map.mp ho'
    rw [Obj.set_writable] at hw
    simp only [Obj.Covers, Obj.set_addr, Obj.set_size] at hc
    exact ⟨o, ho, hw, hc⟩
  · rintro ⟨o, ho, hw, hc⟩
    refine ⟨Obj.set a w v o, List.mem_map_of_mem ho, ?_, ?_⟩
    · rw [Obj.set_writable]; exact hw
    · simp only [Obj.Covers, Obj.set_addr, Obj.set_size]; exact hc

/-- A store writes the memory; the memory holds the new heap; each byte that is not owned is
the same. -/
theorem Heap.store_frame {policy : CpuPolicy} {h h' : Heap} {m : DataMem} {a : BitVec 64}
    {w : Width} {v : w.type} (hh : h.Holds policy m) (hs : h.store a w v = .ok h') :
    ∃ m', writeRam policy m a w v = .ok m' ∧ h'.Holds policy m' ∧
      ∀ b, ¬ h.Owned b → m'.get? b = m.get? b := by
  obtain ⟨m', hw, hh', O, hO, hOw, hb⟩ := Heap.store_sound hh hs
  exact ⟨m', hw, hh', fun b hn => hb b fun hc => hn ⟨O, hO, hOw, hc⟩⟩

/-- A sequence of stores. -/
inductive Heap.Stores : Heap → Heap → Prop
  | refl (h : Heap) : Heap.Stores h h
  | step {h h' h'' : Heap} (a : BitVec 64) (w : Width) (v : w.type) :
    h.store a w v = .ok h' → Heap.Stores h' h'' → Heap.Stores h h''

/-- A sequence of stores does not change the owned bytes. -/
theorem Heap.Stores.owned {h h' : Heap} (hs : Heap.Stores h h') (b : BitVec 64) :
    h'.Owned b ↔ h.Owned b := by
  induction hs with
  | refl => exact Iff.rfl
  | step a w v hst _ ih => exact ih.trans (Heap.owned_store hst b)

/-- After a sequence of stores, the memory holds the heap, and each byte that is not owned is
the same. -/
theorem Heap.Stores.frame {policy : CpuPolicy} {h h' : Heap} {m : DataMem}
    (hs : Heap.Stores h h') (hh : h.Holds policy m) :
    ∃ m', h'.Holds policy m' ∧ ∀ b, ¬ h.Owned b → m'.get? b = m.get? b := by
  induction hs generalizing m with
  | refl => exact ⟨m, hh, fun _ _ => rfl⟩
  | step a w v hst _ ih =>
    obtain ⟨m₁, -, hh₁, hb₁⟩ := Heap.store_frame hh hst
    obtain ⟨m₂, hh₂, hb₂⟩ := ih hh₁
    exact ⟨m₂, hh₂, fun b hn =>
      (hb₂ b fun ho => hn ((Heap.owned_store hst b).mp ho)).trans (hb₁ b hn)⟩

/-! ### Helpers on owned and covered bytes -/

/-- An object of the heap has the byte `b` (writable or not). -/
def Covered (h : Heap) (b : BitVec 64) : Prop := ∃ o ∈ h, o.Covers b

/-- An owned byte is a byte of an object. -/
theorem covered_of_owned {h : Heap} {b : BitVec 64} (ho : h.Owned b) : Covered h b :=
  let ⟨o, hm, _, hc⟩ := ho
  ⟨o, hm, hc⟩

/-- A store that succeeds writes bytes that are owned. -/
theorem owned_of_store {policy : CpuPolicy} {h h' : Heap} {m : DataMem} {a : BitVec 64}
    {w : Width} {v : w.type} (hh : h.Holds policy m) (hs : h.store a w v = .ok h') :
    ∀ i, i < w.bytes → h.Owned (a + BitVec.ofNat 64 i) := by
  intro i hi
  obtain ⟨-, O, hO, hw, x, hx, ha, hxw⟩ := Heap.store_ok hs
  have hn := hh.noWrap O hO
  obtain ⟨e, hb⟩ := Obj.toNat_cell hn hx
  rw [hxw] at hb
  refine ⟨O, hO, hw, ?_⟩
  unfold Obj.Covers
  rw [← ha, toNat_add_ofNat _ _ (by omega), e]
  omega

/-- A memory holds a heap if each byte of an object is the byte of a memory that holds it. -/
theorem holds_congr {policy : CpuPolicy} {h : Heap} {m m' : DataMem} (hh : h.Holds policy m)
    (e : ∀ b, Covered h b → m'.get? b = m.get? b) : h.Holds policy m' where
  read o ho x hx := readRam_congr (hh.read o ho x hx) (Mem.loadInt_congr fun i hi => by
    have hn := hh.noWrap o ho
    obtain ⟨e₀, b₀⟩ := Obj.toNat_cell hn hx
    refine e _ ⟨o, ho, ?_⟩
    unfold Obj.Covers
    rw [toNat_add_ofNat _ _ (by omega), e₀]
    omega)
  write := hh.write
  noWrap := hh.noWrap
  apart := hh.apart

/-- A replacement changes nothing in a heap that does not have the object. -/
theorem replaces_eq_of_not_mem {O O' : Obj} {t t' : Heap} (hr : Heap.Replaces O O' t t')
    (hn : O ∉ t) : t' = t := by
  induction hr with
  | nil => rfl
  | here _ _ => exact absurd (List.mem_cons_self ..) hn
  | there _ _ ih => rw [ih fun h => hn (List.mem_cons_of_mem _ h)]

/-- A writable object with a byte is not in the rest of a heap that a memory holds. -/
theorem not_mem_of_holds {policy : CpuPolicy} {O : Obj} {t : Heap} {m : DataMem}
    (hh : Heap.Holds policy (O :: t) m) (hw : O.writable) (hs : 0 < O.size) : O ∉ t :=
    fun ho => by
  have := (List.pairwise_cons.mp hh.apart).1 O ho (.inl hw)
  unfold Obj.Apart at this
  omega

/-- The byte `b` is in the area `[lo, hi)`, modulo `2^64`. -/
abbrev InArea (lo hi b : BitVec 64) : Prop := b - lo < hi - lo

/-- A byte outside the area `[r, r + 8)` is apart from the 8 bytes at `r`. -/
theorem disjoint_of_not_inArea {a r : BitVec 64} (h : ¬ InArea r (r + 8) a) :
    ByteDisjoint a 1 r 8 := by
  intro i hi j hj e
  apply h
  bv_omega

end Lift.Sem
