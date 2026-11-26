module

/- The conditions of the lifted code as comparisons. -/
public import Kraken.StateCfg
public import Lift.Core
import VerifiedNix.X64Specs

@[expose] public section

namespace Lift

theorem beq_zero (v : BitVec 64) : (v == 0#64) = decide (v = 0#64) := by
  by_cases h : v = 0#64 <;> simp [h]

theorem sub_zero_iff (a b : BitVec 64) : (a - b == 0#64) = decide (a = b) := by
  by_cases h : a = b
  · simp [h]
  · have : a - b ≠ 0#64 := fun e => h (by bv_omega)
    simp [h, this]

@[simp] theorem z_sub (a b : BitVec 64) :
    CondCode.z.interp (StatusFlags.ofSub a b) = decide (a = b) := by
  simp [CondCode.interp, sub_zero_iff]

@[simp] theorem nz_sub (a b : BitVec 64) :
    CondCode.nz.interp (StatusFlags.ofSub a b) = decide (a ≠ b) := by
  simp [CondCode.interp, sub_zero_iff]

@[simp] theorem z_logic (v : BitVec 64) :
    CondCode.z.interp (StatusFlags.ofLogic (v &&& v) false) = decide (v = 0#64) := by
  simp [CondCode.interp, beq_zero]

@[simp] theorem nz_logic (v : BitVec 64) :
    CondCode.nz.interp (StatusFlags.ofLogic (v &&& v) false) = decide (v ≠ 0#64) := by
  simp [CondCode.interp, beq_zero]

end Lift
