module

public import BbuKraken.Unit.IsSpilled
import all BbuKraken.Unit.IsSpilled
public import BbuKraken.Unit.ShallowestCopy
import all BbuKraken.Unit.ShallowestCopy
public import BbuKraken.Unit.Push
import all BbuKraken.Unit.Push
public import BbuKraken.Unit.Dup
import all BbuKraken.Unit.Dup
public import BbuKraken.Unit.SwapWith
import all BbuKraken.Unit.SwapWith
public import BbuKraken.Unit.Produce
import all BbuKraken.Unit.Produce
public import BbuKraken.Unit.Generate
import all BbuKraken.Unit.Generate
public import BbuKraken.Unit.Permute
import all BbuKraken.Unit.Permute
public import BbuKraken.Unit.Loop
import all BbuKraken.Unit.Loop
public import BbuKraken.Unit.Top
import all BbuKraken.Unit.Top
public import BbuKraken.FlatBridge
import all BbuKraken.FlatBridge
public import BbuKraken.Link
import all BbuKraken.Link

@[expose] public section

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

theorem topModelExit_of_flat (hp : TopPre s) (hx : TopFlatExit s t) : TopModelExit s t := by
  refine ⟨hx, ?_⟩
  obtain ⟨hg, _, _, u, fs, hr, hlen, _, _⟩ := hx
  have hrel := Flat.build_bottom_up_rel
    (data := flatData s) (target := flatTgt s) (spilled := topSpill s)
    u (BitVec.le_def.mpr hg.1) hg.2 (hp.mem hg).dests
  rw [hr] at hrel
  have hn : ∀ (st : St) (pos exc : Nat), ¬ (∃ f, (-2#64, some fs) =
      (BitVec.ofNat 64 st.trace.length, some f) ∧ Flat.Holds f st pos exc) := by
    intro st pos exc ⟨f, he, hh⟩
    have hf : fs = f := Option.some.inj (congrArg Prod.snd he)
    have hl : st.trace.length ≤ 6 * nArg s := by rw [← hh.trace, ← hf]; exact hlen
    have hN : nArg s ≤ 1024 := hg.2
    have heq := congrArg (fun p : Word × Option Flat.St => p.1.toNat) he
    change 18446744073709551614 = st.trace.length % 18446744073709551616 at heq
    rw [Nat.mod_eq_of_lt (by omega)] at heq
    omega
  change Flat.Rel (-2#64, some fs)
    (buildBottomUp (topEnv s) (topSource s) (topDests s)) at hrel
  cases he : buildBottomUp (topEnv s) (topSource s) (topDests s) with
  | ok st =>
    rw [he] at hrel
    exact False.elim (hn st 0 0 hrel)
  | error err =>
    cases err with
    | assertion => rfl
    | blocked pos exc st =>
      rw [he] at hrel
      exact False.elim (hn st pos exc hrel)

end

theorem buildBottomUp_correct [Host] (L : Linked) (X : ExitBoundary) :
    letI := L.decls
    ∀ s ra, ⦃ fun t => t = s.pushRa ra ∧ TopPre s ⦄ buildBottomUpAsm
      ⦃ (fun _ _ => False); fun a t =>
        (a = ra ∧ TopPost s t ∧ (topMod s).Agree s t) ∨
        (a = label "exit" ∧ t.regs.get64 .rdi = 1#64 ∧ TopModelExit s t) ⦄ := by
  letI := L.decls
  have hexit := L.exit_decl X
  have hspill := Sep.spec_of_body L.isSpilled_decl Unit.isSpilled_unit
  have hcopy := Sep.spec_of_body L.shallowestCopy_decl Unit.shallowestCopy_unit
  have hpush := Sep.specWithExit_of_body L.push_decl (X.returnDistinct _)
    (Unit.push_unit hexit (X.outside push_at))
  have hdup := Sep.specWithExit_of_body L.dup_decl (X.returnDistinct _)
    (Unit.dup_unit hexit (X.outside dup_at))
  have hswap := Sep.specWithExit_of_body L.swapWith_decl (X.returnDistinct _)
    (Unit.swapWith_unit hexit (X.outside swapWith_at))
  have hprod := Sep.specWithExit_of_body L.produce_decl (X.returnDistinct _)
    (Unit.produce_unit hexit (X.outside produce_at) hcopy hspill hpush hdup)
  have hgen := Sep.specWithExit_of_body L.generate_decl (X.returnDistinct _)
    (Unit.generate_unit hexit (X.outside generate_at) hprod hswap)
  have hperm := fun p => Sep.specWithExit_of_bodyW L.finish_decl (X.returnDistinct _)
    (Unit.permute_unit hexit (X.outside finish_at) hcopy p)
  have hloop := Sep.specWithExit_of_body L.loop_decl (X.returnDistinct _)
    (Unit.loop_unit hexit (X.outside loop_at) hperm hspill hcopy hgen hswap)
  intro s ra
  refine ⟨fun t ht => ?_⟩
  exact Program.wp_mono (fun _ h => h)
    (fun _ h => h.elim
      (fun ⟨ha, hf, hag⟩ => Or.inl ⟨ha, topPost_of_flat ht.2 hf, hag⟩)
      (fun ⟨ha, harg, hx⟩ => Or.inr ⟨ha, harg, topModelExit_of_flat ht.2 hx⟩))
    ((Unit.buildBottomUp_unit (X.outside buildBottomUp_at) hloop s ra).1 t ht)

end Bbu
