import BbuKraken.Unit.ShallowestCopy
import BbuKraken.Unit.Permute
import BbuKraken.Unit.Lowest
import BbuKraken.FlatLowestRel
import BbuKraken.Link

/-!
`Emission::permuteAtLowestHeight` in a host program that contains `c/bbu/build_bottom_up.S`
returns the result of the list model `Bbu.lowest`.

The chain: the spec of `permute` comes from its unit theorem, and that one from the unit theorem
of `shallowestCopyPosition` (`Sep.spec_of_bodyW`, `Sep.spec_of_body`), as in `Final.lean`.
The unit `Unit.permuteAtLowestHeight_unit` gives the result of the flat model
`Flat.permuteAtLowestHeight` (`Unit.lowestQ`). `Flat.sim_lowest` (`FlatLowestRel.lean`) gives the
result of the list model from it, for each list state that the flat state holds.
`BbuBridge.lowest_corr` (root project, `BbuBridge/Lowest.lean`) gives the PR31 model
`Shuffler.PermuteAtLowestHeight.permuteAtLowestHeight` from the list model.
-/

open Std.WP Lean.Order
open scoped Program.WP

namespace Bbu

-- The result of `permuteAtLowestHeight` for the planned array `planned`: the members that no
-- function writes do not change, and the status in `al` and the state of `g'` are a flat result `r`
-- that holds the list result `Bbu.lowest` of each list state that the flat state of `g` holds.
def LowestOut (planned : Vector Word MAX_N) (g g' : Sep.G) (t : MachineData) : Prop :=
  Unit.Keep g g' ∧ ∃ r : Flat.Status × Flat.St, al t = Unit.code r.1 ∧ Unit.flat g' = r.2
    ∧ ∀ (e : Env) (st : St) (pl : List (Option Nat)), Flat.Sim e (Unit.flat g) st →
      Flat.PlanR (Unit.flat g).targetSize.toNat planned pl → Flat.SimR e r (lowest e.n pl st)

theorem permuteAtLowestHeight_correct [Host] (L : Linked) :
    letI := L.decls
    ∀ S PM planned g F, Sep.Body permuteAtLowestHeightAsm
      (Sep.Pre S g (Unit.Planned S PM planned ∗ F) (Unit.lowestA planned) Unit.lowestD)
      (fun s t => Sep.Post S (Unit.Planned S PM planned ∗ F) Unit.lowestD
        (fun g' t => LowestOut planned g g' t) s t) := by
  letI := L.decls
  have hcopy := Sep.spec_of_body L.shallowestCopy_decl Unit.shallowestCopy_unit
  have hperm := fun p => Sep.spec_of_bodyW L.finish_decl (Unit.permute_unit hcopy p)
  intro S PM planned g F s ra
  refine ⟨fun t ht => ?_⟩
  have hb := ht.2.args.2.2
  exact Program.wp_mono (fun _ h => h)
    (fun _ ⟨ha, ⟨g', fr, v, ⟨l, hk, hf, hal⟩, hok, hl, hm⟩, hag⟩ =>
      ⟨ha, ⟨g', fr, v, ⟨hk, _, hal, hf, fun _ _ _ hs hpl => Flat.sim_lowest hs hpl hb l⟩,
        hok, hl, hm⟩, hag⟩)
    ((Unit.permuteAtLowestHeight_unit hperm S PM planned g F s ra).1 t ht)

end Bbu
