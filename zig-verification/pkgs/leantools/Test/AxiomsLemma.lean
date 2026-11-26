module

public import Std.Tactic.BVDecide

/-! A lemma in another module whose proof needs the SAT step of `bv_decide`, for
`Test/Axioms.lean`. -/

namespace Test.Axioms

public theorem mul_comm8 (x y : BitVec 8) : x * y = y * x := by bv_decide

end Test.Axioms
