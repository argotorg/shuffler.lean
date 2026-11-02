module

public import BbuKraken.Unit.SpillSet
import all BbuKraken.Unit.SpillSet
public import BbuKraken.Link
import all BbuKraken.Link

@[expose] public section

/-!
`spill_set` in a host program that contains `build/kraken/c/build_bottom_up.S` returns the result of the
flat model `Flat.spill_set` (`Unit.SetPost`). The spec of `SpillSet::add` comes from its unit
theorem (`Unit.addSpec_of_body`). The root lib `SpillBridge` relates `Flat.spill_set`,
`Flat.spillAdd` and `Flat.spillIsSpilled` to `SpillSet.add` and `SpillSet.is_spilled` of PR31.

`spill_set` calls only `SpillSet::add`, so its function declarations (`Linked.spillDecls`) hold
only that fragment.
-/

open Std.WP Lean.Order
open scoped Program.WP

namespace Bbu

section
set_option maxRecDepth 100000

theorem spillSetAdd_at : spillSetAddAsm.IsInfixAt bbuAsm 846 := by
  rw [bbuAsm_eq]; exact ⟨_, rfl⟩
theorem spillSet_at : spillSetAsm.IsInfixAt bbuAsm 2489 := by rw [bbuAsm_eq]; exact ⟨_, rfl⟩
end

namespace Linked
variable [Host] (L : Linked)

-- The function that `spill_set` calls.
@[instance_reducible]
def spillDecls : FunDecls := ⟨[L.frag spillSetAddAsm spillSetAdd_at]⟩

theorem spillSetAdd_decl :
    L.spillDecls.at (label Names.spillSetAdd) = some (L.frag spillSetAddAsm spillSetAdd_at) :=
  FunDecls.at_of_unique (List.mem_singleton_self _)
    (head_of_isInfixAt _ rfl (by rintro ⟨⟩) : Head (L.frag spillSetAddAsm spillSetAdd_at) _).1
    fun _ hg _ => List.mem_singleton.mp hg

theorem spill_exit_decl (X : ExitBoundary) : L.spillDecls.at (label "exit") = none := by
  show ([L.frag spillSetAddAsm spillSetAdd_at] : List Fragment).find? _ = none
  apply List.find?_eq_none.mpr
  intro f hf he
  obtain rfl := List.mem_singleton.mp hf
  have hh : Head (L.frag spillSetAddAsm spillSetAdd_at) Names.spillSetAdd :=
    head_of_isInfixAt _ rfl (by rintro ⟨⟩)
  exact X.head spillSetAdd_at rfl (hh.1.symm.trans (beq_iff_eq.mp he))

end Linked

theorem spill_set_correct [Host] (L : Linked) (X : ExitBoundary) :
    letI := L.spillDecls
    ∀ f adds queries r res F, Sep.BodyWithExit spillSetAsm (Unit.SetPre f adds queries r res F)
      (Unit.SetPost f adds queries r res F) (Unit.SetExit f adds queries r res F) := by
  letI := L.spillDecls
  exact Unit.spill_set_unit (Unit.addSpec_of_body L.spillSetAdd_decl
    (X.returnDistinct Names.spillSetAdd)
    (Unit.spillSetAdd_unit (L.spill_exit_decl X) (X.outside spillSetAdd_at)))
    (X.outside spillSet_at)

end Bbu
