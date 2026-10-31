import BbuKraken.Unit.Lowest.Assemble

/-!
# `permuteAtLowestHeight`

`c/bbu/<Names.permuteAtLowestHeight>.S`. The contract is in `Lowest/Defs.lean`, and the proof
from the block lemmas in `Lowest/Assemble.lean`.
-/

namespace Bbu.Unit

theorem permuteAtLowestHeight_unit [Host] [FunDecls]
    (hperm : ∀ p, Sep.SpecW Names.permute permW (permuteA p) 1034 (permuteQ p)) :
    LowestThm permuteAtLowestHeightAsm :=
  Lowest.lowest_of_blocks hperm

end Bbu.Unit
