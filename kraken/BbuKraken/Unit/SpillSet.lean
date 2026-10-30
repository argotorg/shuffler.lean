import BbuKraken.Unit.SpillAdd

/-!
# `spill_set`

`c/bbu/spill_set.S`: 6 pushes and 24 bytes of locals. `(%rsp)` holds `spilled`, and `16(%rsp)`
is the `SpillSet` object that `SpillSet::add` gets in `rdi`. The four loops are:

- `.LB248`: the check of the adds (an id of a variable is below `idCount`);
- `.LB251`: the check of the queries;
- `.LB253`: the adds, with a call of `SpillSet::add` for each;
- `.LB255`: the queries, with a store of the result byte for each.
-/

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

set_option experimental.vcgen true

namespace Bbu.Unit

open Bbu.Sep

theorem spill_set_unit [Host] [FunDecls] (hadd : AddSpec) :
    ∀ f adds queries r res F,
      Body spillSetAsm (SetPre f adds queries r res F) (SetPost f adds queries r res F) := by
  sorry

end Bbu.Unit
