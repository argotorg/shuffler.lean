import Shuffler.CostModel

open Shuffler

namespace CostModelTests

-- At each byte boundary: 2^(8k) - 1 needs k bytes, and 2^(8k) needs k + 1.
#guard (List.range 33).all fun k => (Value.Lit (2 ^ (8 * k) - 1)).pushWidth.val = k
#guard (List.range 32).all fun k => (Value.Lit (2 ^ (8 * k))).pushWidth.val = k + 1

-- PUSHn costs n + 1 bytes. PUSH1 to PUSH32 cost 3 gas.
example : ∀ width : PushEncoding, width.cost.bytes = width.val + 1 := by decide
example : ∀ width : PushEncoding, width ≠ 0 → width.cost.gas = 3 := by decide

end CostModelTests
