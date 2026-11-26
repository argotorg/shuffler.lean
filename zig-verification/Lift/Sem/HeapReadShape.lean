module
public import Lift.Sem.HeapFrame
public import Lift.Sem.Bridge

@[expose] public section

open Lift.P2.Total
namespace Lift.Sem

theorem cells_eq_of_widths_reads {policy : CpuPolicy} {m : DataMem} (base : BitVec 64)
    (cs : List Cell) : ∀ (ds : List Cell) (off : Nat),
    cs.map Cell.w = ds.map Cell.w →
    (∀ x ∈ offsets off cs, readRam policy m (base + BitVec.ofNat 64 x.1) x.2.w = .ok x.2.v) →
    (∀ x ∈ offsets off ds, readRam policy m (base + BitVec.ofNat 64 x.1) x.2.w = .ok x.2.v) →
    cs = ds := by
  induction cs with
  | nil =>
    intro ds off hw hr hs
    cases ds with
    | nil => rfl
    | cons d ds => cases hw
  | cons c cs ih =>
    intro ds off hw hr hs
    cases ds with
    | nil => cases hw
    | cons d ds =>
      obtain ⟨w, v⟩ := c
      obtain ⟨w', v'⟩ := d
      simp only [List.map_cons, List.cons.injEq] at hw
      obtain ⟨he, ht⟩ := hw
      cases he
      have hcv := hr (off, ⟨w, v⟩) (List.mem_cons_self ..)
      have hdv := hs (off, ⟨w, v'⟩) (List.mem_cons_self ..)
      have hv : v = v' := Except.ok.inj (hcv.symm.trans hdv)
      cases hv
      congr 1
      exact ih ds (off + w.bytes) ht
        (fun x hx => hr x (List.mem_cons_of_mem _ hx))
        (fun x hx => hs x (List.mem_cons_of_mem _ hx))

theorem Obj.eq_of_shape_reads {policy : CpuPolicy} {m : DataMem} {o p : Obj}
    (hshape : o.shape = p.shape)
    (ho : ∀ x ∈ offsets 0 o.cells,
      readRam policy m (o.addr + BitVec.ofNat 64 x.1) x.2.w = .ok x.2.v)
    (hp : ∀ x ∈ offsets 0 p.cells,
      readRam policy m (p.addr + BitVec.ofNat 64 x.1) x.2.w = .ok x.2.v) : o = p := by
  obtain ⟨a, wr, cs⟩ := o
  obtain ⟨b, ws, ds⟩ := p
  simp only [Obj.shape, Prod.mk.injEq] at hshape
  obtain ⟨rfl, rfl, hw⟩ := hshape
  have he := cells_eq_of_widths_reads a cs ds 0 hw ho hp
  cases he
  rfl

theorem Heap.eq_of_sameShape_reads {policy : CpuPolicy} {m : DataMem} {h k : Heap}
    (hshape : h.SameShape k)
    (hh : ∀ o ∈ h, ∀ x ∈ offsets 0 o.cells,
      readRam policy m (o.addr + BitVec.ofNat 64 x.1) x.2.w = .ok x.2.v)
    (hk : ∀ o ∈ k, ∀ x ∈ offsets 0 o.cells,
      readRam policy m (o.addr + BitVec.ofNat 64 x.1) x.2.w = .ok x.2.v) : h = k := by
  induction h generalizing k with
  | nil =>
    cases k with
    | nil => rfl
    | cons p k => cases hshape
  | cons o h ih =>
    cases k with
    | nil => cases hshape
    | cons p k =>
      simp only [Heap.SameShape, List.map_cons, List.cons.injEq] at hshape
      obtain ⟨hs, ht⟩ := hshape
      have he := Obj.eq_of_shape_reads hs (hh o (List.mem_cons_self ..))
        (hk p (List.mem_cons_self ..))
      cases he
      congr 1
      exact ih ht (fun q hq => hh q (List.mem_cons_of_mem _ hq))
        (fun q hq => hk q (List.mem_cons_of_mem _ hq))

theorem Heap.Holds.eq_of_sameShape {policy : CpuPolicy} {m : DataMem} {h k : Heap}
    (hh : h.Holds policy m) (hk : k.Holds policy m) (hs : h.SameShape k) : h = k :=
  Heap.eq_of_sameShape_reads hs hh.read hk.read

theorem Heap.store_readonly_mem {h k : Heap} {a : BitVec 64} {w : Width} {v : w.type}
    (hs : h.store a w v = .ok k) {o : Obj} (ho : o ∈ h) (hw : o.writable = false) : o ∈ k := by
  unfold Heap.store at hs
  split at hs
  · cases hs
    have he : Obj.set a w v o = o := by simp only [Obj.set, hw, Bool.false_eq_true, ↓reduceIte]
    rw [← he]
    exact List.mem_map_of_mem ho
  · split at hs <;> cases hs

end Lift.Sem
