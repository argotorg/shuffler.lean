module

public import Lift.Sem.Sim
public import Lift.Sem.HeapSplit

@[expose] public section

/-! The call rule at L2⁺ with a frame and a permutation (L3-U6a; design
`docs/research/pilot-heap-design-20261118.md`, section 5.5).

A callee's objects are a sub-list of the caller's objects; the other objects are the frame. The
frame form of a callee result (`Framed`) quantifies over the frame `F`: on `objs ++ F` the callee
returns `objs' ++ F`. The caller's heap `H` is a permutation of `objs ++ F`, and the caller's
heap after the call `H'` is a permutation of `objs' ++ F` with the same permutation
(`SamePerm`: the pairs of objects before and after are a permutation of each other). The
caller's L2⁺ model uses the callee relation up to such a permutation (`PermLift`).

* `Framed` does not follow from the result on `objs` alone (the empty frame) for each relation:
  `Local` is the extra hypothesis (`Framed.of_local`). A load and a store keep a frame
  (`Heap.load_append_frame`, `Heap.store_append_frame`) when a memory holds `h ++ F`; without
  that hypothesis a store writes a frame object that aliases the stored object (test
  `alias_not_local`).
* `Framed.call` is the rule; `Framed.call_holds` and `Framed.call_wf` take the hypothesis on the
  caller's heap (`Holds` or `Heap.WF`) and move it to `objs ++ F` by the permutation.
* `Refines.permLift` gives the callee fact of the L2 side (`Blocks.Returns.sim`) for `PermLift`
  from the callee's `refines_l2p`, when the relations do not depend on the order of the heap. -/

namespace Lift.Sem

open Lift.P2.Total

/-! ### A frame after the heap -/

/-- A load in `h` gives the same value in `h ++ F`. -/
theorem Heap.load_append_frame {h : Heap} {a : BitVec 64} {w : Width} {v : w.type} (F : Heap)
    (hl : h.load a w = .ok v) : (h ++ F).load a w = .ok v := by
  unfold Heap.load at hl ⊢
  rw [List.findSome?_append]
  split at hl
  · rename_i v' hf
    rw [hf]
    exact hl
  · cases hl

/-- A cell of a writable object and a cell of another object of a heap that a memory holds are at
other addresses. -/
theorem Heap.Holds.cell_ne {policy : CpuPolicy} {m : DataMem} {pre post : Heap}
    (hh : (pre ++ post).Holds policy m) {O p : Obj} (hO : O ∈ pre) (hp : p ∈ post)
    (hw : O.writable) {x y : Nat × Cell} (hx : x ∈ offsets 0 O.cells)
    (hy : y ∈ offsets 0 p.cells) : O.addr + BitVec.ofNat 64 x.1 ≠ p.addr + BitVec.ofNat 64 y.1 := by
  intro e
  have hap := (List.pairwise_append.mp hh.apart).2.2 O hO p hp (.inl hw)
  obtain ⟨ex, bx⟩ := Obj.toNat_cell (hh.noWrap O (List.mem_append_left _ hO)) hx
  obtain ⟨ey, by'⟩ := Obj.toNat_cell (hh.noWrap p (List.mem_append_right _ hp)) hy
  have := congrArg BitVec.toNat e
  have := width_bytes_pos x.2.w
  have := width_bytes_pos y.2.w
  unfold Obj.Apart at hap
  omega

/-- A store in `h` gives the same store in `h ++ F`, with `F` unchanged, when a memory holds
`h ++ F`. -/
theorem Heap.store_append_frame {policy : CpuPolicy} {m : DataMem} {h h' F : Heap}
    {a : BitVec 64} {w : Width} {v : w.type} (hh : (h ++ F).Holds policy m)
    (hs : h.store a w v = .ok h') : (h ++ F).store a w v = .ok (h' ++ F) := by
  obtain ⟨hc, rfl⟩ := Heap.store_eq_ok_iff.mp hs
  obtain ⟨-, O, hO, hw, x, hx, ha, -⟩ := Heap.store_ok hs
  refine Heap.store_eq_ok_iff.mpr ⟨?_, ?_⟩
  · rw [List.any_append, hc, Bool.true_or]
  · rw [List.map_append]
    congr 1
    refine ((List.map_congr_left fun p hp => ?_).trans (List.map_id F)).symm
    unfold Obj.set
    split
    · rename_i hpw
      rw [setCells_of_no_match _ _ _ _ _ _ fun y hy hya =>
        hh.cell_ne hO hp hw hx hy (ha.trans hya.1.symm)]
      rfl
    · rfl

/-! ### The order of the heap -/

theorem Heap.owned_perm {h h' : Heap} (hp : h.Perm h') (b : BitVec 64) :
    h.Owned b ↔ h'.Owned b :=
  ⟨fun ⟨o, ho, hw, hc⟩ => ⟨o, hp.subset ho, hw, hc⟩,
    fun ⟨o, ho, hw, hc⟩ => ⟨o, hp.symm.subset ho, hw, hc⟩⟩

theorem covered_perm {h h' : Heap} (hp : h.Perm h') (b : BitVec 64) :
    Covered h b ↔ Covered h' b :=
  ⟨fun ⟨o, ho, hc⟩ => ⟨o, hp.subset ho, hc⟩, fun ⟨o, ho, hc⟩ => ⟨o, hp.symm.subset ho, hc⟩⟩

namespace CallFrame

/-! ### The frame form -/

/-- Some memory holds the heap with the policy: the hypothesis on the heap of the generated
`SimArr` (`∃ m, a.heap.Holds a.policy m`). -/
def HoldsAt (policy : CpuPolicy) (h : Heap) : Prop := ∃ m, h.Holds policy m

/-- The frame form of a callee's L2⁺ result (design 5.5): for each frame `F` with `pre (objs ++
F)`, the callee relation `R` (from input heap to result heap; the other inputs are fixed) returns
`objs' ++ F` on `objs ++ F`. -/
def Framed (pre : Heap → Prop) (R : Heap → Heap → Prop) (objs objs' : Heap) : Prop :=
  ∀ F, pre (objs ++ F) → R (objs ++ F) (objs' ++ F)

/-- `R` keeps each frame `F` with `pre (h ++ F)`: a result `h'` on `h` gives the result `h' ++ F`
on `h ++ F`. -/
def Local (pre : Heap → Prop) (R : Heap → Heap → Prop) : Prop :=
  ∀ h h' F, pre (h ++ F) → R h h' → R (h ++ F) (h' ++ F)

/-- The frame form from the result with no frame, for a relation that keeps each frame. Without
`Local` this is false (`Test/CallFrame.lean`: `alias_not_local`, `frame_write_not_framed`). -/
theorem Framed.of_local {pre : Heap → Prop} {R : Heap → Heap → Prop} {objs objs' : Heap}
    (hl : Local pre R) (h : R objs objs') : Framed pre R objs objs' :=
  fun F hp => hl objs objs' F hp h

/-- The frame form at the empty frame is the result on `objs`. -/
theorem Framed.nil {pre : Heap → Prop} {R : Heap → Heap → Prop} {objs objs' : Heap}
    (h : Framed pre R objs objs') (hp : pre objs) : R objs objs' := by
  have := h [] (by rwa [List.append_nil])
  rwa [List.append_nil, List.append_nil] at this

/-! ### One permutation of two heaps -/

/-- `H'` is `H` changed as `h` changes to `h'`, up to one permutation: the pairs (object before,
object after) of `H` and `H'` are a permutation of the pairs of `h` and `h'`. -/
def SamePerm (H H' h h' : Heap) : Prop :=
  H.length = H'.length ∧ h.length = h'.length ∧ (H.zip H').Perm (h.zip h')

theorem SamePerm.perm_in {H H' h h' : Heap} (hs : SamePerm H H' h h') : H.Perm h := by
  obtain ⟨e₁, e₂, hp⟩ := hs
  have := hp.map Prod.fst
  rwa [List.map_fst_zip (by omega), List.map_fst_zip (by omega)] at this

theorem SamePerm.perm_out {H H' h h' : Heap} (hs : SamePerm H H' h h') : H'.Perm h' := by
  obtain ⟨e₁, e₂, hp⟩ := hs
  have := hp.map Prod.snd
  rwa [List.map_snd_zip (by omega), List.map_snd_zip (by omega)] at this

/-- The callee relation `R` up to one permutation of the heap: `H` and `H'` are a permutation of
an input `h` and a result `h'` of `R`, with the same permutation. -/
def PermLift (R : Heap → Heap → Prop) (H H' : Heap) : Prop :=
  ∃ h h', R h h' ∧ SamePerm H H' h h'

/-! ### The call rule -/

/-- The call rule. The callee has the frame form for `objs → objs'`; the caller's heap `H` and its
heap after the call `H'` are `objs ++ F` and `objs' ++ F` with one permutation, and
`pre (objs ++ F)`. Then the caller's call returns `H'` (`PermLift`), and `Holds` and `Heap.WF` of
`H'` are those of `objs' ++ F`. -/
theorem Framed.call {pre : Heap → Prop} {R : Heap → Heap → Prop} {objs objs' F H H' : Heap}
    (hR : Framed pre R objs objs') (hpre : pre (objs ++ F))
    (hs : SamePerm H H' (objs ++ F) (objs' ++ F)) :
    PermLift R H H' ∧ (∀ policy m, H'.Holds policy m ↔ (objs' ++ F).Holds policy m) ∧
      (H'.WF = true ↔ (objs' ++ F).WF = true) :=
  ⟨⟨_, _, hR F hpre, hs⟩, fun _ _ => Heap.Holds_perm hs.perm_out, Heap.WF_perm hs.perm_out⟩

/-- The call rule with the hypothesis of `SimArr` on the caller's heap: a memory holds `H`. -/
theorem Framed.call_holds {policy : CpuPolicy} {m : DataMem} {R : Heap → Heap → Prop}
    {objs objs' F H H' : Heap} (hR : Framed (HoldsAt policy) R objs objs') (hh : H.Holds policy m)
    (hs : SamePerm H H' (objs ++ F) (objs' ++ F)) :
    PermLift R H H' ∧ (∀ policy m, H'.Holds policy m ↔ (objs' ++ F).Holds policy m) ∧
      (H'.WF = true ↔ (objs' ++ F).WF = true) :=
  Framed.call hR ⟨m, (Heap.Holds_perm hs.perm_in).mp hh⟩ hs

/-- The call rule with the hypothesis of the design on the caller's heap: `Heap.WF H`. -/
theorem Framed.call_wf {R : Heap → Heap → Prop} {objs objs' F H H' : Heap}
    (hR : Framed (fun h => h.WF = true) R objs objs') (hw : H.WF = true)
    (hs : SamePerm H H' (objs ++ F) (objs' ++ F)) :
    PermLift R H H' ∧ (∀ policy m, H'.Holds policy m ↔ (objs' ++ F).Holds policy m) ∧
      (H'.WF = true ↔ (objs' ++ F).WF = true) :=
  Framed.call hR ((Heap.WF_perm hs.perm_in).mp hw) hs

/-! ### The L2 side -/

/-- The callee fact of `Blocks.Returns.sim` for `PermLift`. The callee refines L2 with `simX` and
`simY` (its `refines_l2p`); the input and the result have a heap (`inH`, `outH`), which `setIn`
and `setOut` replace. If `simX` and `simY` do not depend on the order of the heaps (for the
generated relations: `Heap.Holds_perm`, `Heap.owned_perm`, `covered_perm`), then the callee up to
one permutation of the heap refines L2 with the same relations. -/
theorem Refines.permLift {Xh Xl Yh Yl : Type} {simX : Xh → Xl → Prop}
    {simY : Xh → Xl → Yh → Yl → Prop} {R : Xh → Yh → Prop} {lo : Xl → Yl → Prop}
    (inH : Xh → Heap) (setIn : Xh → Heap → Xh) (outH : Yh → Heap) (setOut : Yh → Heap → Yh)
    (h : Refines simX simY R lo)
    (hX : ∀ x xl k, (inH x).Perm k → simX x xl → simX (setIn x k) xl)
    (hY : ∀ x xl y yl k k', (inH x).Perm k → (outH y).Perm k' →
      simY (setIn x k) xl (setOut y k') yl → simY x xl y yl) :
    Refines simX simY
      (fun x y => PermLift (fun k k' => R (setIn x k) (setOut y k')) (inH x) (outH y)) lo := by
  rintro x xl y hx ⟨k, k', hr, hs⟩
  obtain ⟨yl, hlo, hy⟩ := h _ xl _ (hX x xl k hs.perm_in hx) hr
  exact ⟨yl, hlo, hY x xl y yl k k' hs.perm_in hs.perm_out hy⟩

end CallFrame

end Lift.Sem
