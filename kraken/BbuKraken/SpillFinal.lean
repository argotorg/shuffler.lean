import BbuKraken.Unit.SpillSet
import BbuKraken.Link

/-!
`spill_set` in a host program that contains `c/build_bottom_up.S` returns the result of the
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

theorem spillSetAdd_at : spillSetAddAsm.IsInfixAt bbuAsm 1147 := by
  rw [bbuAsm_eq]; exact ⟨_, rfl⟩
theorem spillSet_at : spillSetAsm.IsInfixAt bbuAsm 1168 := by rw [bbuAsm_eq]; exact ⟨_, rfl⟩
end

namespace Linked
variable [Host] (L : Linked)

-- The function that `spill_set` calls.
def spillDecls : FunDecls := ⟨[L.frag spillSetAddAsm spillSetAdd_at]⟩

theorem spillSetAdd_decl :
    L.spillDecls.at (label Names.spillSetAdd) = some (L.frag spillSetAddAsm spillSetAdd_at) :=
  FunDecls.at_of_unique (List.mem_singleton_self _)
    (head_of_isInfixAt _ rfl (by rintro ⟨⟩) : Head (L.frag spillSetAddAsm spillSetAdd_at) _).1
    fun _ hg _ => List.mem_singleton.mp hg

end Linked

theorem spill_set_correct [Host] (L : Linked) :
    letI := L.spillDecls
    ∀ f adds queries r res F, Sep.Body spillSetAsm (Unit.SetPre f adds queries r res F)
      (Unit.SetPost f adds queries r res F) := by
  letI := L.spillDecls
  exact Unit.spill_set_unit (Unit.addSpec_of_body L.spillSetAdd_decl Unit.spillSetAdd_unit)

end Bbu
