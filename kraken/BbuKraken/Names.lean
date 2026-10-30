module

/-!
The symbol names of the functions of `c/build_bottom_up.cpp`. The members of `Emission`
and `SpillSet` have the names that g++ gives them (the Itanium C++ ABI mangling); the
entries `build_bottom_up`, `emission_pop`, `spill_set`, `remove_surplus` and `permute`
are `extern "C"`. These are the names in `c/build_bottom_up.S`, in the binary, and in
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
/-- `Emission::permute(OffsetArray<StackOffset>&)` -/
@[expose] public def permute : String :=
  "_ZN12_GLOBAL__N_18Emission7permuteERNS_11OffsetArrayI11StackOffsetEE"
/-- `Emission::buildBottomUp()` -/
@[expose] public def buildBottomUp : String := "_ZN12_GLOBAL__N_18Emission13buildBottomUpEv"
/-- `Emission::pop()` -/
@[expose] public def pop : String := "_ZN12_GLOBAL__N_18Emission3popEv"
/-- `build_bottom_up`, `extern "C"` -/
@[expose] public def build_bottom_up : String := "build_bottom_up"
/-- `emission_pop`, `extern "C"` -/
@[expose] public def emission_pop : String := "emission_pop"
/-- `SpillSet::add(StackSlot)` -/
@[expose] public def spillSetAdd : String := "_ZN12_GLOBAL__N_18SpillSet3addE9StackSlot"
/-- `spill_set`, `extern "C"` -/
@[expose] public def spill_set : String := "spill_set"
/-- `Emission::removeSurplus()` -/
@[expose] public def removeSurplus : String := "_ZN12_GLOBAL__N_18Emission13removeSurplusEv"
/-- `remove_surplus`, `extern "C"` -/
@[expose] public def remove_surplus : String := "remove_surplus"

/-- `permute`, `extern "C"`. `Names.permute` is the member `Emission::permute`. -/
@[expose] public def permuteEntry : String := "permute"

end Bbu.Names
