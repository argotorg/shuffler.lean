module

public import BbuKraken.Sep.Carve
import all BbuKraken.Sep.Carve
public import BbuKraken.StructLayout
import all BbuKraken.StructLayout

@[expose] public section

/-!
Tests of `EmSize`: `Em` holds the bytes of the struct before `m_plannedMapping`, and not that
word. The values come from the g++ layout (`StructLayout.offsets`).
-/

namespace Bbu.Sep.CarveTest

open Bbu.Sep

-- `EmSize` is the g++ offset of `m_plannedMapping`, the last member.
example : StructLayout.offsets.lookup "m_plannedMapping" = some EmSize := by decide
example : StructLayout.offsets.lookup "size" = some Fld.SIZE := by decide
example : EmSize + 8 = Fld.SIZE := EmSize_add

-- The last byte of `m_blocked.excess` is in `Em`.
example (S : Addr) : In S EmSize (S + 16463#64) := by
  unfold In EmSize; bv_omega

-- Negative: the bytes of `m_plannedMapping` are not in `Em`.
example (S : Addr) : ¬ In S EmSize (Fld.plannedMapping S) := by
  rw [EmSize_eq]; unfold In EmSize; bv_omega

example (S : Addr) : ¬ In S EmSize (S + 16471#64) := by
  unfold In EmSize; bv_omega

-- The address before the struct is not in `Em` (no wrap).
example (S : Addr) : ¬ In S EmSize (S - 1#64) := by
  unfold In EmSize; bv_omega

end Bbu.Sep.CarveTest
