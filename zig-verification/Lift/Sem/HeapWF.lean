module

public import Lift.Sem.Heap

@[expose] public section

namespace Lift.Sem

open Lift.P2.Total

instance : DecidableRel Obj.Apart := fun o o' =>
  inferInstanceAs (Decidable (o.addr.toNat + o.size ≤ o'.addr.toNat ∨ o'.addr.toNat + o'.size ≤ o.addr.toNat))

/-- The heap is well formed: no object wraps around the end of the address space, and each two objects have no byte in
common (`Obj.Apart`, also for two read-only objects). Then a memory holds the heap (`Heap.WF.holds`). -/
def Heap.WF (h : Heap) : Bool :=
  (h.all fun o => decide (o.addr.toNat + o.size ≤ 2 ^ 64)) && decide (h.Pairwise Obj.Apart)

/-- The cells of the heap, each with its address. -/
def Heap.cellList (h : Heap) : List (BitVec 64 × Cell) :=
  h.flatMap fun o => (offsets 0 o.cells).map fun x => (o.addr + BitVec.ofNat 64 x.1, x.2)

/-- The memory with the value of each cell stored. -/
def Heap.memOf (h : Heap) : DataMem :=
  h.cellList.foldl (fun m p => Mem.storeInt m p.1 p.2.w.bytes p.2.v.toInt) ∅

/-- A store of a cell does not change the bytes of the cells that have no byte in common with it. -/
theorem loadInt_foldl_disjoint (L : List (BitVec 64 × Cell)) (p : BitVec 64 × Cell) (m : DataMem)
    (hd : ∀ q ∈ L, ByteDisjoint q.1 q.2.w.bytes p.1 p.2.w.bytes) :
    Mem.loadInt (L.foldl (fun m q => Mem.storeInt m q.1 q.2.w.bytes q.2.v.toInt) m) p.1 p.2.w.bytes =
      Mem.loadInt m p.1 p.2.w.bytes := by
  induction L generalizing m with
  | nil => rfl
  | cons q L ih =>
    simp only [List.foldl_cons]
    rw [ih _ fun r hr => hd r (List.mem_cons_of_mem _ hr)]
    exact loadInt_storeInt_separate _ _ _ _ _ _ (hd q (List.mem_cons_self ..))

/-- When the cells have no byte in common, the memory of the fold holds each cell. -/
theorem loadInt_foldl_mem (L : List (BitVec 64 × Cell))
    (hp : L.Pairwise fun p q => ByteDisjoint p.1 p.2.w.bytes q.1 q.2.w.bytes) (m : DataMem)
    (p : BitVec 64 × Cell) (hm : p ∈ L) :
    Mem.loadInt (L.foldl (fun m q => Mem.storeInt m q.1 q.2.w.bytes q.2.v.toInt) m) p.1 p.2.w.bytes =
      some (Int.ofBytes (Int.toBytes p.2.w.bytes p.2.v.toInt)) := by
  induction L generalizing m with
  | nil => cases hm
  | cons q L ih =>
    obtain ⟨hq, hL⟩ := List.pairwise_cons.mp hp
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hm with rfl | hm
    · rw [loadInt_foldl_disjoint L _ _ fun r hr => (hq r hr).symm]
      exact Mem.loadInt_storeInt _ _ _ _ (by cases p.2.w <;> decide)
    · exact ih hL _ hm

/-- The cells of a well formed heap have no byte in common. -/
theorem Heap.WF.pairwise {h : Heap} (hw : h.WF = true) :
    h.cellList.Pairwise fun p q => ByteDisjoint p.1 p.2.w.bytes q.1 q.2.w.bytes := by
  simp only [Heap.WF, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hw
  obtain ⟨hn, ha⟩ := hw
  unfold Heap.cellList
  rw [List.pairwise_flatMap]
  refine ⟨fun o ho => ?_, ?_⟩
  · rw [List.pairwise_map]
    refine (offsets_pairwise 0 o.cells).imp_of_mem fun {x y} hx hy hxy => ?_
    have hno := hn o ho
    obtain ⟨ex, bx⟩ := Obj.toNat_cell hno hx
    obtain ⟨ey, by'⟩ := Obj.toNat_cell hno hy
    show ByteDisjoint (o.addr + BitVec.ofNat 64 x.1) x.2.w.bytes (o.addr + BitVec.ofNat 64 y.1) y.2.w.bytes
    refine byteDisjoint_of_nat (by rw [ex]; omega) (by rw [ey]; omega) (Or.inl ?_)
    rw [ex, ey]
    omega
  · refine ha.imp_of_mem fun {o o'} ho ho' hap p hp q hq => ?_
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hq
    have hno := hn o ho
    have hno' := hn o' ho'
    obtain ⟨ex, bx⟩ := Obj.toNat_cell hno hx
    obtain ⟨ey, by'⟩ := Obj.toNat_cell hno' hy
    show ByteDisjoint (o.addr + BitVec.ofNat 64 x.1) x.2.w.bytes (o'.addr + BitVec.ofNat 64 y.1) y.2.w.bytes
    refine byteDisjoint_of_nat (by rw [ex]; omega) (by rw [ey]; omega) ?_
    rw [ex, ey]
    unfold Obj.Apart at hap
    omega

/-- A well formed heap is held by a policy that permits each access and a memory of its cells. -/
theorem Heap.WF.holds {h : Heap} (hw : h.WF = true) : ∃ policy m, h.Holds policy m := by
  have hp := Heap.WF.pairwise hw
  simp only [Heap.WF, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hw
  obtain ⟨hn, ha⟩ := hw
  refine ⟨⟨fun _ => true⟩, h.memOf, ?_, ?_, hn, ?_⟩
  · intro o ho x hx
    have hl := loadInt_foldl_mem h.cellList hp ∅
      (o.addr + BitVec.ofNat 64 x.1, x.2) (List.mem_flatMap.mpr ⟨o, ho, List.mem_map.mpr ⟨x, hx, rfl⟩⟩)
    unfold readRam
    simp only [Heap.memOf, hl, ↓reduceIte]
    show Except.ok (BitVec.ofInt x.2.w.bits _) = _
    rw [BitVec.ofInt_ofBytes_toBytes _ _ (width_bits_eq x.2.w), BitVec.ofInt_toInt]
  · intro _ _ _ _ _
    rfl
  · refine ha.imp ?_
    intro a b hab _
    exact hab

end Lift.Sem
