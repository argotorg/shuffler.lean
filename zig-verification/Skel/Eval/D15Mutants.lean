import Skel.Discover.Mutants
import Lift.Shuffler.Zig.Emission

/-! The negative controls of the held-out evaluation D15a: mutants of the shuffler loop `surplusLoop`, made by the D12 code
(`mutate%`, `Skel/Discover/Mutants.lean`) on the `Expr` of its unfolding arm. The ladder must not close them. -/

namespace Skel.Eval.D15

-- The loop calls itself with the entry state: no pass changes the state.
mutate% Lift.Shuffler.Zig.surplusLoop stall 0 as surplusStall
-- The test of the loop has its branches swapped.
mutate% Lift.Shuffler.Zig.surplusLoop wrongExit 0 as surplusSwap

def countStall : String := mutant_result% Lift.Shuffler.Zig.surplusLoop stall
def countExit : String := mutant_result% Lift.Shuffler.Zig.surplusLoop wrongExit
def countNoFall : String := mutant_result% Lift.Shuffler.Zig.surplusLoop noFall
def countBroken : String := mutant_result% Lift.Shuffler.Zig.surplusLoop brokenInv

end Skel.Eval.D15
