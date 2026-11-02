module

public import Kraken.SeparationMem
import all Kraken.SeparationMem

@[expose] public section

namespace Mem

theorem UnchangedOutside.storeInt {m m' : Mem 64} {addr : BitVec 64}
    {l : List (BitVec 64 × Nat)} {n : Nat}
    (h : UnchangedOutside l m m') (hin : Blocks.Inside addr n l) (v : Int) :
    UnchangedOutside l m (m'.storeInt addr n v) := fun b hb => by
  rw [hin.get?_storeInt hb v]
  exact h b hb

end Mem
