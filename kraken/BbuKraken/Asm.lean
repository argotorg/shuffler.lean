module

public import Kraken.StateCfg
import BbuKraken.Parse
import BbuKraken.Names

namespace Bbu

/-!
The output of `g++ -O1` for `c/build_bottom_up.cpp`, one program for each function, in
the order of the file. Each Lean name is that of the model function that the C++
function implements; `BbuKraken.Names` gives the symbol name. `positionOf` is inline: it
is a load of `m_positionOf`.
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
public def popAsm : Program := bbuParseFn(Names.pop)
public def buildBottomUpAsm : Program := bbuParseFn(Names.build_bottom_up)
public def emissionPopAsm : Program := bbuParseFn(Names.emission_pop)
public def spillSetAddAsm : Program := bbuParseFn(Names.spillSetAdd)
public def spillSetAsm : Program := bbuParseFn(Names.spill_set)

/-- `c/build_bottom_up.S`, the file that `bbu_harness` links. -/
public def bbuAsm : Program := bbuParseFile("c/build_bottom_up.S")

end Bbu
