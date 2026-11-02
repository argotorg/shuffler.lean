module

public import FlatShuffler.Unit.ShallowestCopy
import all FlatShuffler.Unit.ShallowestCopy
public import FlatShuffler.Unit.Permute
import all FlatShuffler.Unit.Permute
public import FlatShuffler.Unit.Lowest
import all FlatShuffler.Unit.Lowest
public import FlatShuffler.FlatLowestRel
import all FlatShuffler.FlatLowestRel
public import FlatShuffler.Link
import all FlatShuffler.Link

@[expose] public section

/-!
`Emission::permuteAtLowestHeight` in a host program that contains `build/kraken/c/build_bottom_up.S`
returns the result of the list model `FlatShuffler.lowest`.

The chain: the spec of `permute` comes from its unit theorem, and that one from the unit theorem
of `shallowestCopyPosition` (`Sep.spec_of_bodyW`, `Sep.spec_of_body`), as in `Final.lean`.
The unit `Unit.permuteAtLowestHeight_unit` gives the result of the flat model
`Flat.permuteAtLowestHeight` (`Unit.lowestQ`). `Flat.sim_lowest` (`FlatLowestRel.lean`) gives the
result of the list model from it, for each list state that the flat state holds.
`ShufflerBridge.Emission.lowest_corr` (root project, `ShufflerBridge/Emission/Lowest.lean`) gives the PR31 model
`Shuffler.PermuteAtLowestHeight.permuteAtLowestHeight` from the list model.
-/

open Std.WP Lean.Order
open scoped Program.WP

namespace FlatShuffler

-- The result of `permuteAtLowestHeight` for the planned array `planned`: the members that no
-- function writes do not change, and the status in `al` and the state of `g'` are a flat result `r`
-- that holds the list result `FlatShuffler.lowest` of each list state that the flat state of `g` holds.
def LowestOut (planned : Vector Word maxStackSize) (g g' : Sep.G) (t : MachineData) : Prop :=
  Unit.Keep g g' ∧ al t ≠ ASSERTION_FAILED ∧
    ∃ r : Flat.Status × Flat.St, al t = Unit.code r.1 ∧ Unit.flat g' = r.2
    ∧ ∀ (e : Env) (st : St) (pl : List (Option Nat)), Flat.Sim e (Unit.flat g) st →
      Flat.PlanR (Unit.flat g).targetSize.toNat planned pl → Flat.SimR e r (lowest e.n pl st)

def LowestExit (planned : Vector Word maxStackSize) (g g' : Sep.G) : Prop :=
  Unit.Keep g g' ∧ ∃ r : Flat.Status × Flat.St,
    r.1 = .assertionFailed ∧ Unit.flat g' = r.2 ∧
    ∀ (e : Env) (st : St) (pl : List (Option Nat)), Flat.Sim e (Unit.flat g) st →
      Flat.PlanR (Unit.flat g).targetSize.toNat planned pl → Flat.SimR e r (lowest e.n pl st)

theorem permuteAtLowestHeight_correct [Host] (L : Linked) (X : ExitBoundary) :
    letI := L.decls
    ∀ S PM planned g F, Sep.BodyWithExit permuteAtLowestHeightAsm
      (Sep.Pre S g (Unit.Planned S PM planned ∗ F) (Unit.lowestA planned) Unit.lowestD)
      (fun s t => Sep.Post S (Unit.Planned S PM planned ∗ F) Unit.lowestD
        (fun g' t => LowestOut planned g g' t) s t)
      (fun s t => Sep.Post S (Unit.Planned S PM planned ∗ F) Unit.lowestD
        (fun g' _ => LowestExit planned g g') s t) := by
  letI := L.decls
  have hexit := L.exit_decl X
  have hcopy := Sep.spec_of_body L.shallowestCopy_decl Unit.shallowestCopy_unit
  have hperm := fun p => Sep.specWithExit_of_bodyW L.finish_decl (X.returnDistinct _)
    (Unit.permute_unit hexit (X.outside finish_at) hcopy p)
  intro S PM planned g F s ra
  refine ⟨fun t ht => ?_⟩
  have hb := ht.2.args.2.2
  exact Program.wp_mono (fun _ h => h)
    (fun _ h => h.elim
      (fun ⟨ha, ⟨g', fr, v, ⟨l, ⟨hk, hf, hal⟩, normalByte⟩, hok, hl, hm⟩, hag⟩ =>
        Or.inl ⟨ha, ⟨g', fr, v, ⟨hk, normalByte, _, hal, hf,
          fun _ _ _ hs hpl => Flat.sim_lowest hs hpl hb l⟩, hok, hl, hm⟩, hag⟩)
      (fun ⟨ha, harg, ⟨g', fr, v, ⟨l, hk, hf, hstatus⟩, hok, hl, hm⟩⟩ =>
        Or.inr ⟨ha, harg, ⟨g', fr, v, ⟨hk, _, hstatus, hf,
          fun _ _ _ hs hpl => Flat.sim_lowest hs hpl hb l⟩, hok, hl, hm⟩⟩))
    ((Unit.permuteAtLowestHeight_unit hexit (X.outside permuteAtLowestHeight_at)
      hperm S PM planned g F s ra).1 t ht)

end FlatShuffler
