module

public import FlatShuffler.Unit.Plan.PlannerRunScanDefs
import all FlatShuffler.Unit.Plan.PlannerRunScanDefs

@[expose] public section

namespace FlatShuffler.Unit.PlannerRunU

theorem variable_of_not_generated {x : StackSlot}
    (hf : (isJunk x || canBeFreelyGenerated x) = false) (hk : x.kind = 0#8) :
    Flat.isVariable x = true := by
  simp only [isJunk, canBeFreelyGenerated, isLiteralValue, Bool.or_eq_false_iff,
    beq_eq_false_iff_ne] at hf
  have ho : x.valueOpcode ≠ Const := hf.2.1.1
  simp [Flat.isVariable, isLiteralValue, hk, Value, Const] at ho ⊢
  exact ho

theorem spill_false_of_kind {x : StackSlot} {sp : BitVec 32 → BitVec 8}
    (hk : x.kind ≠ 0#8) : Flat.spillIsSpilled sp x = false := by
  simp [Flat.spillIsSpilled, Flat.isVariable, Value, hk]

theorem target_missing_bad {pl : Flat.Planner} {sp : BitVec 32 → BitVec 8} {i : Word}
    (hi : i < pl.n)
    (hf : (isJunk (Flat.get pl.target i) || canBeFreelyGenerated (Flat.get pl.target i)) = false)
    (hc : Flat.containsFrom pl.source pl.m (Flat.get pl.target i) 0 = false)
    (hs : Flat.spillIsSpilled sp (Flat.get pl.target i) = false) :
    Flat.targetsFrom pl sp i = false := by
  apply targets_fail hi
  simp only [hf, hc, hs, Bool.false_or]

def CheckBad (P : Addr) (g : PlannerCallMemory) (F : MProp 64) (s : MachineData) (ra : Int64)
    (t : MachineData) : Prop :=
  ∃ lo locals, EarlyLI P g F s ra lo locals t ∧ Flat.targetsFrom g.p.fl g.spills 0 = false

end FlatShuffler.Unit.PlannerRunU
