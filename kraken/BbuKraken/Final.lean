import BbuKraken.Unit.IsSpilled
import BbuKraken.Unit.ShallowestCopy
import BbuKraken.Unit.Push
import BbuKraken.Unit.Dup
import BbuKraken.Unit.SwapWith
import BbuKraken.Unit.Produce
import BbuKraken.Unit.Generate
import BbuKraken.Unit.Permute
import BbuKraken.Unit.Loop
import BbuKraken.Unit.Top
import BbuKraken.FlatBridge
import BbuKraken.Link

/-!
`build_bottom_up` in a host program that contains `c/bbu/build_bottom_up.S` returns the result of
the list model `buildBottomUp`.

The chain: the spec of each callee comes from its unit theorem (`Unit/*.lean`), from the leaves
up (`Sep.spec_of_body`). The unit `Unit.buildBottomUp_unit` gives the result of the flat model
`Flat.build_bottom_up` (`TopFlatPost`). The bridge `Flat.build_bottom_up_rel` (`FlatBridge.lean`)
gives the result of the list model from it (`topPost_of_flat`). `BbuBridge` (root project) gives
the PR31 model from the list model.
-/

open Std.WP Lean.Order
open scoped Program.WP

namespace Bbu

section
variable {s t : MachineData}

-- The memory that holds a flat state holds the list state that `Holds` relates to it.
theorem outMem_of_flat {fs : Flat.St} {st : St} {pos excess : Nat} (hf : FlatMem s t fs)
    (hh : Flat.Holds fs st pos excess) : OutMem s t st pos excess := by
  have hlen : fs.size.toNat = st.len := by
    simpa [Flat.slotsOf, St.len] using congrArg List.length hh.data
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hh.trace]; exact hf.ops
  · rw [← hlen, ← hh.data]; exact hf.data
  · rw [hf.blk0, hh.blk0]
  · rw [hf.blk1, hh.blk1]

-- The result of the flat model in `t` is the result of the list model, if `Rel` holds.
theorem topOut_of_rel {r : Word × Option Flat.St} {res : M St} (ho : FlatOut s t r)
    (hr : Flat.Rel r res) : TopOut s t res := by
  obtain ⟨hax, hmem⟩ := ho
  match res, hr with
  | .ok st, ⟨fs, hr, hh⟩ =>
    subst hr
    exact ⟨hax, outMem_of_flat (hmem fs rfl (by simp only [hh.trace])) hh⟩
  | .error (.blocked pos excess st), ⟨fs, hr, hh⟩ =>
    subst hr
    exact ⟨hax, outMem_of_flat (hmem fs rfl (by simp only [hh.trace])) hh⟩
  | .error .assertion, hr => exact hax.trans hr

-- `TopPost` from `TopFlatPost`: the bridge if the guard holds, else the guard of the flat model.
theorem topPost_of_flat (hp : TopPre s) (h : TopFlatPost s t) : TopPost s t := by
  obtain ⟨hmap, u, ho⟩ := h
  refine ⟨hmap, ?_⟩
  split
  · rename_i hg
    exact topOut_of_rel ho
      (Flat.build_bottom_up_rel u (BitVec.le_def.mpr hg.1) hg.2 (hp.mem hg).dests)
  · rename_i hg
    have he : Flat.build_bottom_up (rdi s) (rsi s) (flatData s) (flatTgt s) (flatDest s)
        (topSpill s) u = (-2, none) := by
      unfold Flat.build_bottom_up
      split
      · rfl
      · rename_i hc
        exfalso
        simp only [TopGuard, mArg, nArg, MAX_N] at hg
        simp only [gt_iff_lt, BitVec.lt_def, BitVec.toNat_ofNat, MAX_N, not_or, Nat.not_lt] at hc
        omega
    have hax := ho.1
    rw [he] at hax
    exact hax

end

theorem buildBottomUp_correct [Host] (L : Linked) :
    letI := L.decls
    ∀ s ra, ⦃ fun t => t = s.pushRa ra ∧ TopPre s ⦄ buildBottomUpAsm
      ⦃ (fun _ _ => False); fun a t => a = ra ∧ TopPost s t ∧ (topMod s).Agree s t ⦄ := by
  letI := L.decls
  have hspill := Sep.spec_of_body L.isSpilled_decl Unit.isSpilled_unit
  have hcopy := Sep.spec_of_body L.shallowestCopy_decl Unit.shallowestCopy_unit
  have hpush := Sep.spec_of_body L.push_decl Unit.push_unit
  have hdup := Sep.spec_of_body L.dup_decl Unit.dup_unit
  have hswap := Sep.spec_of_body L.swapWith_decl Unit.swapWith_unit
  have hprod := Sep.spec_of_body L.produce_decl (Unit.produce_unit hcopy hspill hpush hdup)
  have hgen := Sep.spec_of_body L.generate_decl (Unit.generate_unit hprod hswap)
  have hperm := fun p => Sep.spec_of_bodyW L.finish_decl (Unit.permute_unit hcopy p)
  have hloop := Sep.spec_of_body L.loop_decl (Unit.loop_unit hperm hspill hcopy hgen hswap)
  intro s ra
  refine ⟨fun t ht => ?_⟩
  exact Program.wp_mono (fun _ h => h)
    (fun _ ⟨ha, hf, hag⟩ => ⟨ha, topPost_of_flat ht.2 hf, hag⟩)
    ((Unit.buildBottomUp_unit hloop s ra).1 t ht)

end Bbu
