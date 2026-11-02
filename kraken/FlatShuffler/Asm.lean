module

public import Kraken.StateCfg
import FlatShuffler.Parse
import FlatShuffler.Names

namespace FlatShuffler

/-!
The output of `g++ -O1` for `c/shuffler/stack/Shuffler.cpp`, one program for each function, in
the order of the file. Each Lean name is that of the model function that the C++
function implements; `FlatShuffler.Names` gives the symbol name. `positionOf` is inline: it
is a load of `m_positionOf`. Failed assertions call the external symbol `exit` with status 1.
The phases of `MappingBuilder` are the loops of
`buildMapping`, and have the C++ names.
-/

public def isSpilledAsm : Program := bbuParseFn(Names.isSpilled)
public def shallowestCopyAsm : Program := bbuParseFn(Names.shallowestCopyPosition)
public def pushAsm : Program := bbuParseFn(Names.push)
public def dupAsm : Program := bbuParseFn(Names.dup)
public def produceAsm : Program := bbuParseFn(Names.produce)
public def swapWithAsm : Program := bbuParseFn(Names.swapWith)
public def generateAsm : Program := bbuParseFn(Names.generate)
public def finishAsm : Program := bbuParseFn(Names.permute)
public def loopAsm : Program := bbuParseFn(Names.buildBottomUp)
public def spillSetAddAsm : Program := bbuParseFn(Names.spillSetAdd)
public def mapAsm : Program := bbuParseFn(Names.map)
public def closestCopyAsm : Program := bbuParseFn(Names.closestCopy)
public def mapInPlaceAsm : Program := bbuParseFn(Names.mapInPlace)
public def mapClosestCopiesAsm : Program := bbuParseFn(Names.mapClosestCopies)
public def mapWildcardSlotCopiesAsm : Program := bbuParseFn(Names.mapWildcardSlotCopies)
public def keepWildcardSlotsAsm : Program := bbuParseFn(Names.keepWildcardSlots)
public def absorbSurplusAsm : Program := bbuParseFn(Names.absorbSurplus)
public def popAsm : Program := bbuParseFn(Names.pop)
public def removeSurplusAsm : Program := bbuParseFn(Names.removeSurplus)
public def permuteAtLowestHeightAsm : Program := bbuParseFn(Names.permuteAtLowestHeight)
public def isAvailableAsm : Program := bbuParseFn(Names.isAvailable)
public def runAsm : Program := bbuParseFn(Names.run)
public def isRetainedAsm : Program := bbuParseFn(Names.isRetained)
public def hasOtherRetainedCopyAsm : Program := bbuParseFn(Names.hasOtherRetainedCopy)
public def isDemandedAsm : Program := bbuParseFn(Names.isDemanded)
public def classifyAsm : Program := bbuParseFn(Names.classify)
public def resolveAsm : Program := bbuParseFn(Names.resolve)
public def plannerRunAsm : Program := bbuParseFn(Names.plannerRun)

set_option maxRecDepth 100000 in
/-- The generated assembly checked against the C++ methods in `bbu_harness`. -/
public def bbuAsm : Program := bbuParseFile("../../build/kraken/c/build_bottom_up.S")

end FlatShuffler
