module

public import Lift.Sem.HeapSlice
public import Lift.Sem.CallArmBytes

@[expose] public section

/-! Focus and reassembly for typed heaps. Read-only objects can overlap. A writable byte
cannot be in the other heap. A callee must provide both its footprint and its frame contents. -/

namespace Lift.Sem

open Lift.P2.Total

/-- A writable object in either heap is apart from each object of the other heap.
This also constrains empty objects, as required by `Heap.Holds.apart`. -/
def Heap.Separated (h F : Heap) : Prop :=
  ∀ o ∈ h, ∀ p ∈ F, (o.writable ∨ p.writable) → o.Apart p

theorem Heap.Separated.symm {h F : Heap} (hs : h.Separated F) : F.Separated h :=
  fun p hp o ho hw => Or.symm (hs o ho p hp (Or.symm hw))

/-- Equal object shapes retain the fields used by heap separation. -/
theorem Obj.fields_of_shape {o p : Obj} (hs : o.shape = p.shape) :
    o.addr = p.addr ∧ o.writable = p.writable ∧ o.size = p.size := by
  have ha := congrArg (fun q : BitVec 64 × Bool × List Width => q.1) hs
  have hw := congrArg (fun q : BitVec 64 × Bool × List Width => q.2.1) hs
  have hc := congrArg (fun q : BitVec 64 × Bool × List Width =>
    (q.2.2.map Width.bytes).sum) hs
  exact ⟨ha, hw, by simpa [Obj.shape, Obj.size, List.map_map, Function.comp_def] using hc⟩

/-- A callee with the same object layouts retains separation from its frame. -/
theorem Heap.Separated.of_shape {h h' F : Heap} (hs : h.Separated F)
    (shape : h.SameShape h') : h'.Separated F := by
  intro o' ho' p hp hw
  have hm : o'.shape ∈ h.map Obj.shape := by
    rw [shape]
    exact List.mem_map.mpr ⟨o', ho', rfl⟩
  obtain ⟨o, ho, he⟩ := List.mem_map.mp hm
  obtain ⟨ha, hw', hz⟩ := Obj.fields_of_shape he
  have hap := hs o ho p hp (by simpa only [hw'] using hw)
  simpa only [Obj.Apart, ha, hz] using hap

/-- A separated frame covers no byte owned by the selected heap. -/
theorem Heap.Separated.not_owned_of_covered {h F : Heap} (hs : h.Separated F)
    {b : BitVec 64} (hb : Covered F b) : ¬ h.Owned b := by
  rintro ⟨o, ho, hw, hoc⟩
  obtain ⟨p, hp, hpc⟩ := hb
  have ha := hs o ho p hp (.inl hw)
  unfold Obj.Apart at ha
  unfold Obj.Covers at hoc hpc
  omega

/-- A held heap separates every partition of its object list. -/
theorem Heap.Holds.separated {policy : CpuPolicy} {m : DataMem} {h F : Heap}
    (hh : (h ++ F).Holds policy m) : h.Separated F :=
  (List.pairwise_append.mp hh.apart).2.2

/-- Reassemble two held heaps after the separation condition is proved. -/
theorem Heap.Holds.append {policy : CpuPolicy} {m : DataMem} {h F : Heap}
    (hh : h.Holds policy m) (hf : F.Holds policy m) (hs : h.Separated F) :
    (h ++ F).Holds policy m where
  read o ho := (List.mem_append.mp ho).elim (hh.read o) (hf.read o)
  write o ho := (List.mem_append.mp ho).elim (hh.write o) (hf.write o)
  noWrap o ho := (List.mem_append.mp ho).elim (hh.noWrap o) (hf.noWrap o)
  apart := List.pairwise_append.mpr ⟨hh.apart, hf.apart, hs⟩

/-- Focus exposes both heaps and their separation condition. -/
theorem Heap.Holds.append_iff {policy : CpuPolicy} {m : DataMem} {h F : Heap} :
    (h ++ F).Holds policy m ↔ h.Holds policy m ∧ F.Holds policy m ∧ h.Separated F := by
  constructor
  · intro hh
    exact ⟨hh.sublist (List.sublist_append_left h F),
      hh.sublist (List.sublist_append_right h F), hh.separated⟩
  · rintro ⟨hh, hf, hs⟩
    exact hh.append hf hs

/-- The selected objects can occur at any positions in the original heap. -/
theorem Heap.Holds.focus {policy : CpuPolicy} {m : DataMem} {H h F : Heap}
    (hh : H.Holds policy m) (hp : H.Perm (h ++ F)) :
    h.Holds policy m ∧ F.Holds policy m ∧ h.Separated F :=
  Heap.Holds.append_iff.mp ((Heap.Holds_perm hp).mp hh)

/-- Reassemble a callee's output with a frame whose contents have been proved. -/
theorem Heap.Holds.reassemble_of_frame {policy : CpuPolicy} {m m' : DataMem} {h h' F : Heap}
    (hh : (h ++ F).Holds policy m) (hout : h'.Holds policy m')
    (shape : h.SameShape h') (frame : F.Holds policy m') :
    (h' ++ F).Holds policy m' :=
  hout.append frame (hh.separated.of_shape shape)

/-- A callee's byte frame clause preserves the contents of the selected frame. -/
theorem Heap.Holds.reassemble {policy : CpuPolicy} {m m' : DataMem} {h h' F : Heap}
    (hh : (h ++ F).Holds policy m) (hout : h'.Holds policy m')
    (shape : h.SameShape h')
    (frame : ∀ b, ¬ h.Owned b → m'.get? b = m.get? b) :
    (h' ++ F).Holds policy m' := by
  obtain ⟨_, hf, hs⟩ := Heap.Holds.append_iff.mp hh
  exact hh.reassemble_of_frame hout shape (holds_congr hf fun b hb =>
    frame b (hs.not_owned_of_covered hb))

/-- Select an exact cell from any visible object, including an object after an unknown prefix. -/
theorem Heap.Found.of_mem {h : Heap} {o : Obj} {a : BitVec 64} {w : Width} {v : w.type}
    (ho : o ∈ h) (hc : cellGet o.cells (a - o.addr).toNat w = some v) : Heap.Found a w v h := by
  induction h with
  | nil => cases ho
  | cons p h ih =>
    rcases List.mem_cons.mp ho with rfl | ho
    · exact .head hc
    · exact .tail (ih ho)

/-- A selected byte store leaves every object of an unknown prefix in place. -/
theorem Heap.StoreSpanAt.append_prefix {a : BitVec 64} {w : Width} {v : w.type}
    {h h' : Heap} (hs : Heap.StoreSpanAt a w v h h') (pre : Heap) :
    Heap.StoreSpanAt a w v (pre ++ h) (pre ++ h') := by
  induction pre with
  | nil => exact hs
  | cons o pre ih => exact .tail ih

/-- A cross-cell byte store updates one object at any position. -/
theorem Heap.storeB_span_at_append {policy : CpuPolicy} {m : DataMem} {pre post : Heap}
    {o : Obj} {cs : List Cell} {a : BitVec 64} {w : Width} {v : w.type}
    (hh : (pre ++ o :: post).Holds policy m) (hw : o.writable = true)
    (hc : cellGet o.cells (a - o.addr).toNat w = none)
    (hs : spanSet v o.cells (a - o.addr).toNat w.bytes 0 = some cs) :
    (pre ++ o :: post).storeB a w v = .ok (pre ++ { o with cells := cs } :: post) :=
  Heap.storeB_of_storeSpanAt hh ((Heap.StoreSpanAt.head hw hc hs).append_prefix pre)

/-- A byte range inside one writable object updates no object of its frame.
The byte-range permissions of a concrete machine write remain a separate condition. -/
theorem Heap.storeB_bytes_at_append {policy : CpuPolicy} {m : DataMem} {pre post : Heap}
    {o : Obj} {a : BitVec 64} {w : Width} {v : w.type}
    (hh : (pre ++ o :: post).Holds policy m) (hw : o.writable = true)
    (hc : cellGet o.cells (a - o.addr).toNat w = none) (spans : o.Spans a w) :
    (pre ++ o :: post).storeB a w v = .ok (pre ++ o.setBytes a w v :: post) := by
  have ho : o ∈ pre ++ o :: post := List.mem_append_right _ (List.mem_cons_self ..)
  have hng := hh.no_get ho hw spans hc
  have h1 : ((pre ++ o :: post).any fun p => (p.get a w).isSome) = false := by
    rw [List.any_eq_false]
    intro p hp
    simp [hng p hp]
  have h2 : ((pre ++ o :: post).any fun p => p.writable && decide (p.Spans a w)) = true :=
    List.any_eq_true.mpr ⟨o, ho, by simp [hw, spans]⟩
  have noPre : o ∉ pre := by
    intro hp
    have ha := (List.pairwise_append.mp hh.apart).2.2 o hp o (List.mem_cons_self ..) (.inl hw)
    exact Obj.not_apart_of_spans spans spans ha
  have hhpost : Heap.Holds policy (o :: post) m := hh.sublist (List.sublist_append_right pre _)
  have noPost : o ∉ post := not_mem_of_holds hhpost hw (by
    have := width_bytes_pos w
    unfold Obj.Spans at spans
    omega)
  have preUnchanged : pre.map (Obj.setBytes a w v) = pre := by
    conv => rhs; rw [← List.map_id pre]
    exact List.map_congr_left fun p hp => hh.setBytes_other ho
      (List.mem_append_left _ hp) (fun e => noPre (e ▸ hp)) hw spans
  have postUnchanged : post.map (Obj.setBytes a w v) = post := by
    conv => rhs; rw [← List.map_id post]
    exact List.map_congr_left fun p hp => hh.setBytes_other ho
      (List.mem_append_right _ (List.mem_cons_of_mem _ hp)) (fun e => noPost (e ▸ hp)) hw spans
  simp only [Heap.storeB, h1, h2, Bool.false_eq_true, ↓reduceIte,
    List.map_append, List.map_cons, preUnchanged, postUnchanged]

/-- Read a byte range from one record in a fixed-size typed encoding. -/
theorem Heap.loadB_records_slice {policy : CpuPolicy} {h : Heap} {m : DataMem}
    (hh : h.Holds policy m) {α : Type} {base : BitVec 64} {writable : Bool}
    {xs : List α} {encode : α → List Cell} {size index offset : Nat}
    (ho : Obj.mk base writable (xs.flatMap encode) ∈ h)
    (hs : ∀ x, cellsSize (encode x) = size) (w : Width) (hi : index < xs.length)
    (hr : offset + w.bytes ≤ size) :
    h.loadB (base + BitVec.ofNat 64 (index * size + offset)) w =
      .ok (BitVec.ofInt w.bits
        (Int.ofBytes ((((encode xs[index]).flatMap Cell.bytes).drop offset).take w.bytes))) := by
  have hsize : (Obj.mk base writable (xs.flatMap encode)).size = xs.length * size := by
    change cellsSize (xs.flatMap encode) = _
    rw [cellsSize_flatMap]
    simp only [hs, sum_map_const]
  have hk : index * size + offset + w.bytes ≤
      (Obj.mk base writable (xs.flatMap encode)).size := by
    rw [hsize]
    have := Nat.mul_le_mul_right size (show index + 1 ≤ xs.length by omega)
    rw [Nat.succ_mul] at this
    omega
  have he := Heap.loadB_slice hh ho w hk
  have bytes : (Obj.mk base writable (xs.flatMap encode)).bytes =
      xs.flatMap (fun x => (encode x).flatMap Cell.bytes) := by
    change (xs.flatMap encode).flatMap Cell.bytes = _
    rw [List.flatMap_assoc]
  have lengths (x : α) : ((encode x).flatMap Cell.bytes).length = size := by
    simpa only [List.length_flatMap, Cell.bytes_length, cellsSize] using hs x
  rw [bytes, bytesSlice_flatMap lengths hi hr] at he
  exact he

/-- The record slice rule at the bit-vector address of a machine operation. -/
theorem Heap.loadB_records_slice_bv {policy : CpuPolicy} {h : Heap} {m : DataMem}
    (hh : h.Holds policy m) {α : Type} {base : BitVec 64} {writable : Bool}
    {xs : List α} {encode : α → List Cell} {size offset : Nat} {index : BitVec 64}
    (ho : Obj.mk base writable (xs.flatMap encode) ∈ h)
    (hs : ∀ x, cellsSize (encode x) = size) (w : Width) (hi : index.toNat < xs.length)
    (hr : offset + w.bytes ≤ size) :
    h.loadB (base + index * BitVec.ofNat 64 size + BitVec.ofNat 64 offset) w =
      .ok (BitVec.ofInt w.bits
        (Int.ofBytes ((((encode xs[index.toNat]).flatMap Cell.bytes).drop offset).take w.bytes))) := by
  have ha : base + index * BitVec.ofNat 64 size + BitVec.ofNat 64 offset =
      base + BitVec.ofNat 64 (index.toNat * size + offset) := by
    simp only [BitVec.ofNat_add, BitVec.ofNat_mul, BitVec.ofNat_toNat,
      BitVec.setWidth_eq, BitVec.add_assoc]
  rw [ha]
  exact Heap.loadB_records_slice hh ho hs w hi hr

end Lift.Sem
