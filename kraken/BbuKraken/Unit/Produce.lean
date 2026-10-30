import BbuKraken.Unit.Defs

/-!
# `produce`

`c/bbu/<Names.produce>.S`: 6 `pushq` and `subq $8`, so 8 free words (7 and one for the return
address of a callee). It reads the target word `m_target[t]` and calls `shallowestCopyPosition`,
then `push`, `dup` or `isSpilled` and `push`, or writes `m_blocked`. Then it asserts
`m_positionOf[t] = size - 1` and decrements `m_pendingGenerations`.

The preconditions of the callees: the target word is in the view (`t < n`); its id is in
`splIds` (`isSpilledA`); the copy for `dup` is below `size ≤ n`; `len < n` and `nops < 6n`
(`pushA`, `dupA`). The caller is `generate`, after its check `t < n`.
-/

namespace Bbu.Unit

theorem produce_unit [Host] [FunDecls]
    (hcopy : Sep.Spec Names.shallowestCopyPosition shallowestCopyA 0 shallowestCopyQ)
    (hspill : Sep.Spec Names.isSpilled isSpilledA 0 isSpilledQ)
    (hpush : Sep.Spec Names.push pushA 0 pushQ)
    (hdup : Sep.Spec Names.dup dupA 0 dupQ) :
    UnitThm produceAsm produceA 8 produceQ := by
  sorry

end Bbu.Unit
