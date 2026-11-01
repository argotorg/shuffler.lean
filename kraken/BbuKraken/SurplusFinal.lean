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
`Emission::removeSurplus` in a host program that contains `c/bbu/build_bottom_up.S` returns the
result of the list model `Map.State.removeSurplus`.

The chain: the specs of the callees `swapWith` and `pop` come from their unit theorems
(`Sep.spec_of_body`). The unit `Unit.removeSurplus_unit` gives the result of the flat model
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

end Linked

-- The result of `removeSurplus` for the planned mapping `planned`: the members that no function
-- writes do not change, and the status in `al` and the state of `g'` are a flat result `r` whose
-- list result (`Flat.absOut`) is `Map.State.removeSurplus` of the list state of `g`.
def SurplusOut (planned : Map.Mapping) (g g' : Sep.G) (t : MachineData) : Prop :=
  Unit.Keep g g' ∧ ∃ r : Flat.Status × Flat.St, al t = Unit.code r.1 ∧ Unit.flat g' = r.2
    ∧ (Flat.absSt planned (Unit.flat g)).removeSurplus = Flat.absOut planned r

theorem removeSurplus_correct [Host] (L : Linked) (planned : Map.Mapping) :
    letI := L.surplusDecls
    Unit.UnitThm removeSurplusAsm Unit.surplusA 2 (fun g g' _ t => SurplusOut planned g g' t) := by
  letI := L.surplusDecls
  have hswap := Sep.spec_of_body L.surplus_swapWith_decl Unit.swapWith_unit
  have hpop := Sep.spec_of_body L.surplus_pop_decl Unit.pop_unit
  intro S g F s ra
  refine ⟨fun t ht => ?_⟩
  have hsz : (Unit.flat g).size.toNat ≤ MAX_N := Nat.le_trans ht.2.ok.len ht.2.ok.xs
  exact Program.wp_mono (fun _ h => h)
    (fun _ ⟨ha, ⟨g', fr, v, ⟨hk, hf, hal⟩, hok, hl, hm⟩, hag⟩ =>
      ⟨ha, ⟨g', fr, v, ⟨hk, _, hal, hf, Flat.removeSurplus_abs planned _ hsz⟩, hok, hl, hm⟩, hag⟩)
    ((Unit.removeSurplus_unit hswap hpop S g F s ra).1 t ht)

end Bbu
