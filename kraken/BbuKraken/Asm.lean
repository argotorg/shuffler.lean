module

public import Kraken.StateCfg
import BbuKraken.Parse

namespace Bbu

/-!
The output of `gcc -O1` for `c/build_bottom_up.c`, one program for each function.
Each name is that of the model function that the C function implements.
`positionOf` is inline: it is a load of `m_positionOf`.
-/

public def isSpilledAsm : Program := bbuParseFile("c/bbu/isSpilled.S")
public def shallowestCopyAsm : Program := bbuParseFile("c/bbu/shallowestCopyPosition.S")
public def swapWithAsm : Program := bbuParseFile("c/bbu/swapWith.S")
public def pushAsm : Program := bbuParseFile("c/bbu/push.S")
public def dupAsm : Program := bbuParseFile("c/bbu/dup.S")
public def produceAsm : Program := bbuParseFile("c/bbu/produce.S")
public def generateAsm : Program := bbuParseFile("c/bbu/generate.S")
public def finishAsm : Program := bbuParseFile("c/bbu/permuteDestinations.S")
public def loopAsm : Program := bbuParseFile("c/bbu/buildBottomUp.S")
public def buildBottomUpAsm : Program := bbuParseFile("c/bbu/build_bottom_up.S")

/-- `c/build_bottom_up.S`, the file that `bbu_harness` links. -/
public def bbuAsm : Program := bbuParseFile("c/build_bottom_up.S")

end Bbu
