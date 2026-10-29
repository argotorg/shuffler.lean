module

/-!
The symbol names of the functions of `c/build_bottom_up.cpp`. The members of `Emission`
have the names that g++ gives them (the Itanium C++ ABI mangling); `build_bottom_up` is
`extern "C"`. These are the names in `c/build_bottom_up.S`, in the binary, and in
`c/bbu/NAME.S`. We do not rename them in the asm: each change to the compiler output is
one more step between the proved program and the program that runs. Each name is here
once; `BbuKraken.Asm`, `BbuKraken.Link` and the specs use these defs.
-/

namespace Bbu.Names

/-- `Emission::isSpilled(StackSlot) const` -/
@[expose] public def isSpilled : String := "_ZNK12_GLOBAL__N_18Emission9isSpilledE9StackSlot"
/-- `Emission::shallowestCopyPosition(StackSlot) const` -/
@[expose] public def shallowestCopyPosition : String :=
  "_ZNK12_GLOBAL__N_18Emission22shallowestCopyPositionE9StackSlot"
/-- `Emission::push(StackSlot, StackOffset)` -/
@[expose] public def push : String := "_ZN12_GLOBAL__N_18Emission4pushE9StackSlot11StackOffset"
/-- `Emission::dup(StackOffset, StackOffset)` -/
@[expose] public def dup : String := "_ZN12_GLOBAL__N_18Emission3dupE11StackOffsetS1_"
/-- `Emission::produce(StackOffset)` -/
@[expose] public def produce : String := "_ZN12_GLOBAL__N_18Emission7produceE11StackOffset"
/-- `Emission::swapWith(StackOffset)` -/
@[expose] public def swapWith : String := "_ZN12_GLOBAL__N_18Emission8swapWithE11StackOffset"
/-- `Emission::generate(StackOffset)` -/
@[expose] public def generate : String := "_ZN12_GLOBAL__N_18Emission8generateE11StackOffset"
/-- `Emission::permuteDestinations()` -/
@[expose] public def permuteDestinations : String :=
  "_ZN12_GLOBAL__N_18Emission19permuteDestinationsEv"
/-- `Emission::buildBottomUp()` -/
@[expose] public def buildBottomUp : String := "_ZN12_GLOBAL__N_18Emission13buildBottomUpEv"
/-- `build_bottom_up`, `extern "C"` -/
@[expose] public def build_bottom_up : String := "build_bottom_up"

end Bbu.Names
