module

public import BbuKraken.Unit.SwapWith
import all BbuKraken.Unit.SwapWith
public import BbuKraken.Unit.Pop
import all BbuKraken.Unit.Pop
public import BbuKraken.Unit.RemoveSurplus
import all BbuKraken.Unit.RemoveSurplus
public import BbuKraken.FlatSurplusRel
import all BbuKraken.FlatSurplusRel
public import BbuKraken.Link
import all BbuKraken.Link

@[expose] public section

/-!
`Emission::removeSurplus` in a host program that contains `build/kraken/c/build_bottom_up.S` returns the
result of the list model `Map.State.removeSurplus`. If the model reports an assertion failure,
the assembly calls `exit(1)`.

The chain: the specs of the callees `swapWith` and `pop` come from their unit theorems
(`Sep.specWithExit_of_body`). The unit `Unit.removeSurplus_unit` gives the result of the flat model
`Flat.removeSurplus` (`Unit.surplusQ`). `Flat.removeSurplus_abs` (`FlatSurplusRel.lean`) gives the
result of the list model from it. `BbuBridge.removeSurplus_corr` (root project,
`BbuBridge/RemoveSurplus.lean`) gives the PR31 model `Shuffler.Emission.removeSurplus` from the
list model.

The flat state does not hold the planned mapping, and `removeSurplus` does not read it, so the
theorem holds for each planned mapping.
-/

open Std.WP Lean.Order
open scoped Program.WP

namespace Bbu

namespace Linked
variable [Host] (L : Linked)

-- The functions that `removeSurplus` calls.
@[instance_reducible]
def surplusDecls : FunDecls := ⟨[L.frag swapWithAsm swapWith_at, L.frag popAsm pop_at]⟩

theorem surplusHeads :
    Head (L.frag swapWithAsm swapWith_at) Names.swapWith ∧ Head (L.frag popAsm pop_at) Names.pop :=
  ⟨by head_tac, by head_tac⟩

theorem surplus_swapWith_decl :
    L.surplusDecls.at (label Names.swapWith) = some (L.frag swapWithAsm swapWith_at) :=
  find_hit L.surplusHeads.1

theorem surplus_pop_decl : L.surplusDecls.at (label Names.pop) = some (L.frag popAsm pop_at) := by
  show List.find? _ [_, _] = _
  rw [find_skip L.surplusHeads.1 L.surplusHeads.2 (by decide)]
  exact find_hit L.surplusHeads.2

theorem surplus_exit_decl (X : ExitBoundary) : L.surplusDecls.at (label "exit") = none := by
  show ([L.frag swapWithAsm swapWith_at, L.frag popAsm pop_at] : List Fragment).find? _ = none
  apply List.find?_eq_none.mpr
  intro f hf he
  have ha : f.startAddr = label "exit" := beq_iff_eq.mp he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · exact X.head swapWith_at rfl (L.surplusHeads.1.1.symm.trans ha)
  · exact X.head pop_at rfl (L.surplusHeads.2.1.symm.trans ha)

end Linked

-- The result of `removeSurplus` for the planned mapping `planned`: the members that no function
-- writes do not change, and the status in `al` and the state of `g'` are a flat result `r` whose
-- list result (`Flat.absOut`) is `Map.State.removeSurplus` of the list state of `g`.
def SurplusOut (planned : Map.Mapping) (g g' : Sep.G) (t : MachineData) : Prop :=
  Unit.Keep g g' ∧ ∃ r : Flat.Status × Flat.St, al t = Unit.code r.1 ∧ Unit.flat g' = r.2
    ∧ (Flat.absSt planned (Unit.flat g)).removeSurplus = Flat.absOut planned r

def SurplusExit (planned : Map.Mapping) (g g' : Sep.G) : Prop :=
  Unit.Keep g g' ∧ ∃ r : Flat.Status × Flat.St, r.1 = .assertionFailed ∧ Unit.flat g' = r.2
    ∧ (Flat.absSt planned (Unit.flat g)).removeSurplus = Flat.absOut planned r

theorem removeSurplus_correct [Host] (L : Linked) (X : ExitBoundary) (planned : Map.Mapping) :
    letI := L.surplusDecls
    Unit.UnitThmWithExit removeSurplusAsm Unit.surplusA 4
      (fun g g' _ t => SurplusOut planned g g' t)
      (fun g g' _ _ => SurplusExit planned g g') := by
  letI := L.surplusDecls
  have hexit := L.surplus_exit_decl X
  have hswap := Sep.specWithExit_of_body L.surplus_swapWith_decl (X.returnDistinct _)
    (Unit.swapWith_unit hexit (X.outside swapWith_at))
  have hpop := Sep.specWithExit_of_body L.surplus_pop_decl (X.returnDistinct _)
    (Unit.pop_unit hexit (X.outside pop_at))
  intro S g F s ra
  refine ⟨fun t ht => ?_⟩
  have hsz : (Unit.flat g).size.toNat ≤ MAX_N := Nat.le_trans ht.2.ok.len ht.2.ok.xs
  exact Program.wp_mono (fun _ h => h)
    (fun _ h => h.elim
      (fun ⟨ha, ⟨g', fr, v, ⟨hk, hf, hal⟩, hok, hl, hm⟩, hag⟩ =>
        Or.inl ⟨ha, ⟨g', fr, v,
          ⟨hk, _, hal, hf, Flat.removeSurplus_abs planned _ hsz⟩, hok, hl, hm⟩, hag⟩)
      (fun ⟨ha, harg, ⟨g', fr, v, ⟨hk, hf, hstatus⟩, hok, hl, hm⟩⟩ =>
        Or.inr ⟨ha, harg, ⟨g', fr, v,
          ⟨hk, _, hstatus, hf, Flat.removeSurplus_abs planned _ hsz⟩, hok, hl, hm⟩⟩))
    ((Unit.removeSurplus_unit hexit (X.outside removeSurplus_at) hswap hpop S g F s ra).1 t ht)

end Bbu
