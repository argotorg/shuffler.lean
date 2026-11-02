module

/-! The C++ symbols in `c/shuffler/stack/Shuffler.cpp` and its headers.
The names use the Itanium C++ ABI. The proof input contains no test wrappers. -/

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
/-- `SpillSet::add(StackSlot)` -/
@[expose] public def spillSetAdd : String := "_ZN12_GLOBAL__N_18SpillSet3addE9StackSlot"
/-- `Emission::removeSurplus()` -/
@[expose] public def removeSurplus : String := "_ZN12_GLOBAL__N_18Emission13removeSurplusEv"
/-- `MappingBuilder::map(StackOffset, StackOffset)` -/
@[expose] public def map : String := "_ZN12_GLOBAL__N_114MappingBuilder3mapE11StackOffsetS1_"
/-- `MappingBuilder::closestCopy(StackOffset, CopyLocation) const` -/
@[expose] public def closestCopy : String :=
  "_ZNK12_GLOBAL__N_114MappingBuilder11closestCopyE11StackOffsetNS0_12CopyLocationE"
/-- `MappingBuilder::mapInPlace()` -/
@[expose] public def mapInPlace : String := "_ZN12_GLOBAL__N_114MappingBuilder10mapInPlaceEv"
/-- `MappingBuilder::mapClosestCopies()` -/
@[expose] public def mapClosestCopies : String :=
  "_ZN12_GLOBAL__N_114MappingBuilder16mapClosestCopiesEv"
/-- `MappingBuilder::mapWildcardSlotCopies()` -/
@[expose] public def mapWildcardSlotCopies : String :=
  "_ZN12_GLOBAL__N_114MappingBuilder21mapWildcardSlotCopiesEv"
/-- `MappingBuilder::keepWildcardSlots()` -/
@[expose] public def keepWildcardSlots : String :=
  "_ZN12_GLOBAL__N_114MappingBuilder17keepWildcardSlotsEv"
/-- `MappingBuilder::absorbSurplus()` -/
@[expose] public def absorbSurplus : String := "_ZN12_GLOBAL__N_114MappingBuilder13absorbSurplusEv"

/-- `Emission::permuteAtLowestHeight()` -/
@[expose] public def permuteAtLowestHeight : String :=
  "_ZN12_GLOBAL__N_18Emission21permuteAtLowestHeightEv"

/-- `Planner::isRetained(Mapping const&, StackOffset)`, static -/
@[expose] public def isRetained : String :=
  "_ZN12_GLOBAL__N_17Planner10isRetainedERKNS_7MappingE11StackOffset"
/-- `Planner::hasOtherRetainedCopy(Mapping const&, OffsetArray<uint8_t> const&, StackOffset) const` -/
@[expose] public def hasOtherRetainedCopy : String :=
  "_ZNK12_GLOBAL__N_17Planner20hasOtherRetainedCopyERKNS_7MappingERKNS_11OffsetArrayIhEE11StackOffset"
/-- `Planner::isDemanded(StackSlot) const` -/
@[expose] public def isDemanded : String := "_ZNK12_GLOBAL__N_17Planner10isDemandedE9StackSlot"
/-- `Planner::classify(Mapping const&, OffsetArray<uint8_t> const&, StackOffset) const` -/
@[expose] public def classify : String :=
  "_ZNK12_GLOBAL__N_17Planner8classifyERKNS_7MappingERKNS_11OffsetArrayIhEE11StackOffset"
/-- `Planner::resolve(Mapping const&, Emission::Blocked, Mapping const&, size_t)` -/
@[expose] public def resolve : String :=
  "_ZN12_GLOBAL__N_17Planner7resolveERKNS_7MappingENS_8Emission7BlockedES3_m"

/-- `Emission::isAvailable(StackOffset) const` -/
@[expose] public def isAvailable : String :=
  "_ZNK12_GLOBAL__N_18Emission11isAvailableE11StackOffset"
/-- `Emission::run()` -/
@[expose] public def run : String := "_ZN12_GLOBAL__N_18Emission3runEv"
/-- `Planner::run(MappingBuilder::WildcardSlotsStrategy, StackSlot*, ShuffleOp*,
  Optional<StackOffset>*, size_t&)` -/
@[expose] public def plannerRun : String :=
  "_ZN12_GLOBAL__N_17Planner3runENS_14MappingBuilder21WildcardSlotsStrategyEP9StackSlotP9ShuffleOpPNS_8OptionalI11StackOffsetEERm"

end Bbu.Names
