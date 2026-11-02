module

public import BbuKraken.Unit.Lowest.Assemble
import all BbuKraken.Unit.Lowest.Assemble

@[expose] public section

/-!
# `permuteAtLowestHeight`

`c/bbu/<Names.permuteAtLowestHeight>.S`. The contract is in `Lowest/Defs.lean`, and the proof
from the block lemmas in `Lowest/Assemble.lean`.
-/

namespace Bbu.Unit

theorem permuteAtLowestHeight_unit [Host] [FunDecls]
    (hexit : FunDecls.at (label "exit") = none)
    (hout : ∀ l ∈ Program.labels permuteAtLowestHeightAsm, label l ≠ label "exit")
    (hperm : ∀ p, Sep.SpecWWithExit Names.permute permW (permuteA p) 1034
      (permuteQ p) (permuteX p)) :
    LowestThm permuteAtLowestHeightAsm :=
  Lowest.lowest_of_blocks hexit hout hperm

end Bbu.Unit
