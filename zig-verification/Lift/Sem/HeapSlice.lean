module

public import Lift.Sem.HeapFields
public import Lift.Sem.HeapSpan

@[expose] public section

/-! Byte slices and stores relative to the input heap. These rules do not
reconstruct a list of objects from a program's final abstract state. -/

namespace Lift.Sem

open Lift.P2.Total Lift.Sem.ByteLemmas

/-- A stronger access policy keeps a held heap. This changes no memory byte. -/
theorem Heap.Holds.mono_policy {policy policy' : CpuPolicy} {h : Heap} {m : DataMem}
    (hh : h.Holds policy m)
    (hp : ∀ a, policy.permits a = true → policy'.permits a = true) :
    h.Holds policy' m := by
  refine ⟨?_, ?_, hh.noWrap, hh.apart⟩
  · intro o ho x hx
    have hr := hh.read o ho x hx
    have hperm := hp _ (readRam_ok hr).1
    unfold readRam at hr ⊢
    simp only [(readRam_ok (hh.read o ho x hx)).1, hperm, ↓reduceIte] at hr ⊢
    exact hr
  · intro o ho hw x hx
    exact hp _ (hh.write o ho hw x hx)

/-- A byte value in any object of a held heap is the result of `loadB`.
No byte-range permission is needed for this model-level equality. -/
theorem Heap.loadB_of_loadBytes {policy : CpuPolicy} {h : Heap} {m : DataMem}
    (hh : h.Holds policy m) {o : Obj} (ho : o ∈ h) {a : BitVec 64}
    {w : Width} {v : w.type} (hl : o.loadBytes a w = some v) :
    h.loadB a w = .ok v := by
  let allPolicy : CpuPolicy := ⟨fun _ => true⟩
  have hh' : h.Holds allPolicy m := hh.mono_policy (fun _ _ => rfl)
  have hp : h.Permits allPolicy := fun _ _ _ _ _ => ⟨rfl, fun _ => rfl⟩
  obtain ⟨k, ha, hk, hv⟩ := Obj.loadBytes_spec hl
  have hr : readRam allPolicy m a w = .ok v := by
    rw [readRam_slice hh' ho ha hk rfl, hv]
  unfold Heap.loadB
  split
  · rename_i v' hf
    have he := Heap.load_sound hh' hf
    rw [hr] at he
    cases he
    rfl
  · rename_i result hnot
    split
    · rename_i v' hf
      have he := Heap.loadB_sound hh' hp (show h.loadB a w = .ok v' by
        unfold Heap.loadB
        split
        · rename_i val hval
          exact (hnot val hval).elim
        · rw [hf])
      rw [hr] at he
      cases he
      rfl
    · rename_i hf
      have he := List.findSome?_eq_none_iff.mp hf o ho
      rw [hl] at he
      cases he

/-- An in-bounds offset gives the corresponding bytes of an object. -/
theorem Obj.loadBytes_offset {o : Obj} {k : Nat} (w : Width)
    (hk : k + w.bytes ≤ o.size) (hn : o.addr.toNat + o.size ≤ 2 ^ 64) :
    o.loadBytes (o.addr + BitVec.ofNat 64 k) w =
      some (BitVec.ofInt w.bits (Int.ofBytes ((o.bytes.drop k).take w.bytes))) := by
  obtain ⟨hs, hoff⟩ := Obj.spans_of_offset rfl hk hn
  simp only [Obj.loadBytes, hs, ↓reduceIte, hoff]

/-- A slice of an object in a held heap, with the address and bound exposed. -/
theorem Heap.loadB_slice {policy : CpuPolicy} {h : Heap} {m : DataMem}
    (hh : h.Holds policy m) {o : Obj} (ho : o ∈ h) {k : Nat} (w : Width)
    (hk : k + w.bytes ≤ o.size) :
    h.loadB (o.addr + BitVec.ofNat 64 k) w =
      .ok (BitVec.ofInt w.bits (Int.ofBytes ((o.bytes.drop k).take w.bytes))) :=
  Heap.loadB_of_loadBytes hh ho (Obj.loadBytes_offset w hk (hh.noWrap o ho))


/-- Read a byte range of one element of a fixed-size byte encoding. -/
theorem bytesSlice_flatMap {α : Type} {xs : List α} {encode : α → List UInt8}
    {size index offset count : Nat} (hs : ∀ x, (encode x).length = size)
    (hi : index < xs.length) (hr : offset + count ≤ size) :
    ((xs.flatMap encode).drop (index * size + offset)).take count =
      ((encode xs[index]).drop offset).take count := by
  induction xs generalizing index with
  | nil => cases hi
  | cons x xs ih =>
    rw [List.flatMap_cons]
    cases index with
    | zero =>
      simp only [Nat.zero_mul, Nat.zero_add, List.getElem_cons_zero]
      rw [List.drop_append_of_le_length (by rw [hs]; omega)]
      rw [List.take_append_of_le_length (by simp only [List.length_drop, hs]; omega)]
    | succ index =>
      rw [List.drop_append, List.drop_eq_nil_of_le (by rw [hs, Nat.succ_mul]; omega),
        List.nil_append, hs]
      rw [show (index + 1) * size + offset - size = index * size + offset by
        rw [Nat.succ_mul]; omega]
      exact ih (by simpa using hi)

/-- A byte slice inside a value is the corresponding bit-vector slice. -/
theorem Cell.bytes_slice (c : Cell) (w : Width) {offset : Nat}
    (hb : offset + w.bytes ≤ c.w.bytes) :
    BitVec.ofInt w.bits (Int.ofBytes ((c.bytes.drop offset).take w.bytes)) =
      c.v.extractLsb' (8 * offset) w.bits := by
  unfold Cell.bytes
  rw [toBytes_toInt, ofInt_ofBytes_slice _ _ _ _ _ (width_bits_eq w) hb,
    ofNat_div_eq_extractLsb']

/-- A narrow load inside a fixed-width array cell, including byte loads inside words. -/
theorem Heap.loadB_words_slice {policy : CpuPolicy} {h : Heap} {m : DataMem}
    (hh : h.Holds policy m) {base : BitVec 64} {writable : Bool} {wide : Width}
    {xs : List wide.type} (ho : Obj.words base writable wide xs ∈ h)
    {index offset : Nat} (w : Width) (hi : index < xs.length)
    (hr : offset + w.bytes ≤ wide.bytes) :
    h.loadB (base + BitVec.ofNat 64 (index * wide.bytes + offset)) w =
      .ok (xs[index].extractLsb' (8 * offset) w.bits) := by
  have hsize : (Obj.words base writable wide xs).size = xs.length * wide.bytes := by
    simp [Obj.words, Obj.size, List.map_map, Function.comp_def, sum_map_const]
  have hk : index * wide.bytes + offset + w.bytes ≤
      (Obj.words base writable wide xs).size := by
    rw [hsize]
    have := Nat.mul_le_mul_right wide.bytes (show index + 1 ≤ xs.length by omega)
    rw [Nat.succ_mul] at this
    omega
  have he := Heap.loadB_slice hh ho w hk
  have hbytes : (Obj.words base writable wide xs).bytes =
      xs.flatMap (fun v => (Cell.mk wide v).bytes) := by
    simp [Obj.bytes, Obj.words, List.flatMap_map, Cell.bytes]
  rw [hbytes, bytesSlice_flatMap (fun v => Cell.bytes_length (Cell.mk wide v)) hi hr,
    Cell.bytes_slice _ _ hr] at he
  exact he

/-- The same slice rule with the bit-vector address used by machine operations. -/
theorem Heap.loadB_words_slice_bv {policy : CpuPolicy} {h : Heap} {m : DataMem}
    (hh : h.Holds policy m) {base : BitVec 64} {writable : Bool} {wide : Width}
    {xs : List wide.type} (ho : Obj.words base writable wide xs ∈ h)
    {index : BitVec 64} {offset : Nat} (w : Width) (hi : index.toNat < xs.length)
    (hr : offset + w.bytes ≤ wide.bytes) :
    h.loadB (base + index * BitVec.ofNat 64 wide.bytes + BitVec.ofNat 64 offset) w =
      .ok (xs[index.toNat].extractLsb' (8 * offset) w.bits) := by
  have ha : base + index * BitVec.ofNat 64 wide.bytes + BitVec.ofNat 64 offset =
      base + BitVec.ofNat 64 (index.toNat * wide.bytes + offset) := by
    simp only [BitVec.ofNat_add, BitVec.ofNat_mul, BitVec.ofNat_toNat,
      BitVec.setWidth_eq, BitVec.add_assoc]
  rw [ha]
  exact Heap.loadB_words_slice hh ho w hi hr

/-- A cell store in an encoded array can use `List.set`, with every other record unchanged. -/
theorem cellSet_flatMap_set {α : Type} {xs : List α} {encode : α → List Cell}
    {size index offset : Nat} {w : Width} (v : w.type) (x : α)
    (hs : ∀ x, cellsSize (encode x) = size) (hi : index < xs.length)
    (hr : offset < size) (he : cellSet (encode xs[index]) offset w v = encode x) :
    cellSet (xs.flatMap encode) (index * size + offset) w v =
      (xs.set index x).flatMap encode := by
  rw [cellSet_flatMap w v hs hi hr, he, flatMap_set x hi]

/-- A selected object store leaves the pre and post of the heap unchanged. -/
theorem Heap.StoreAt.append_prefix {a : BitVec 64} {w : Width} {v : w.type}
    {h h' : Heap} (hs : Heap.StoreAt a w v h h') (pre : Heap) :
    Heap.StoreAt a w v (pre ++ h) (pre ++ h') := by
  induction pre with
  | nil => exact hs
  | cons o pre ih => exact .tail ih

/-- A whole-cell store updates an object at any list position and keeps its frame. -/
theorem Heap.storeB_at_append {policy : CpuPolicy} {m : DataMem} {pre post : Heap}
    {o o' : Obj} {a : BitVec 64} {w : Width} {v : w.type}
    (hh : (pre ++ o :: post).Holds policy m) (hw : o.writable = true)
    (hc : (cellGet o.cells (a - o.addr).toNat w).isSome)
    (he : o.set a w v = o') :
    (pre ++ o :: post).storeB a w v = .ok (pre ++ o' :: post) := by
  have ho : o ∈ pre ++ o :: post := List.mem_append_right _ (List.mem_cons_self ..)
  rw [Obj.set_eq_setAt v hw (hh.noWrap o ho) hc] at he
  subst o'
  exact Heap.storeB_of_storeAt hh ((Heap.StoreAt.head hw hc).append_prefix pre)

/-- The layout retained from an entry object: address, access mode, and cell widths. -/
def Obj.shape (o : Obj) : BitVec 64 × Bool × List Width :=
  (o.addr, o.writable, o.cells.map Cell.w)

/-- A heap has the entry objects in the same order and with the same layouts. -/
def Heap.SameShape (entry current : Heap) : Prop :=
  entry.map Obj.shape = current.map Obj.shape

/-- An exact-cell write retains the cell widths. -/
theorem setCells_widths (base a : BitVec 64) (w : Width) (v : w.type) :
    ∀ (offset : Nat) (cs : List Cell),
      (setCells base a w v offset cs).map Cell.w = cs.map Cell.w
  | _, [] => rfl
  | offset, c :: cs => by
    simp only [setCells, List.map_cons, setCells_widths base a w v]
    split
    · rename_i hc
      simp only [hc.2]
    · rfl

/-- An exact-cell store retains the object layout. -/
theorem Obj.set_shape (a : BitVec 64) (w : Width) (v : w.type) (o : Obj) :
    (o.set a w v).shape = o.shape := by
  unfold Obj.set Obj.shape
  split
  · simp only [setCells_widths]
  · rfl

/-- A byte store retains the object layout. -/
theorem Obj.setBytes_shape (a : BitVec 64) (w : Width) (v : w.type) (o : Obj) :
    (o.setBytes a w v).shape = o.shape := by
  simp only [Obj.shape, Obj.setBytes_addr, Obj.setBytes_writable, Obj.setBytes_widths]

/-- A successful exact-cell store retains the entry object layouts. -/
theorem Heap.store_sameShape {h h' : Heap} {a : BitVec 64} {w : Width} {v : w.type}
    (hs : h.store a w v = .ok h') : h.SameShape h' := by
  unfold Heap.store at hs
  split at hs
  · cases hs
    simp [Heap.SameShape, List.map_map, Function.comp_def, Obj.set_shape]
  · split at hs <;> cases hs

/-- A successful byte store retains the entry object layouts in both store paths. -/
theorem Heap.storeB_sameShape {h h' : Heap} {a : BitVec 64} {w : Width} {v : w.type}
    (hs : h.storeB a w v = .ok h') : h.SameShape h' := by
  unfold Heap.storeB at hs
  split at hs
  · exact Heap.store_sameShape hs
  · split at hs
    · cases hs
      simp [Heap.SameShape, List.map_map, Function.comp_def, Obj.setBytes_shape]
    · split at hs <;> cases hs

/-- Shape equality composes across a chain of stores and calls with that interface. -/
theorem Heap.SameShape.trans {h h' h'' : Heap}
    (h₁ : h.SameShape h') (h₂ : h'.SameShape h'') : h.SameShape h'' := Eq.trans h₁ h₂

/-- Shape equality rules out an accidental insertion or removal of an optional object. -/
theorem Heap.SameShape.length {h h' : Heap} (hs : h.SameShape h') : h.length = h'.length := by
  have := congrArg List.length hs
  simpa only [List.length_map] using this

end Lift.Sem
