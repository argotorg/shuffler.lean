module

public import Kraken.StateCfg
import Kraken.X64.Parser

open Kraken.X64.Parser

namespace Bbu

/-!
The output of `gcc -O1` for `c/build_bottom_up.c`, one program for each function.
Each name is that of the model function that the C function implements.
-/

public def isSpilledAsm : Program := parseFile("c/bbu/isSpilled.S")
public def positionOfAsm : Program := parseFile("c/bbu/positionOf.S")
public def shallowestCopyAsm : Program := parseFile("c/bbu/shallowestCopyPosition.S")
public def swapWithAsm : Program := parseFile("c/bbu/swapWith.S")
public def pushAsm : Program := parseFile("c/bbu/push.S")
public def dupAsm : Program := parseFile("c/bbu/dup.S")
public def produceAsm : Program := parseFile("c/bbu/produce.S")
public def generateAsm : Program := parseFile("c/bbu/generate.S")
public def finishAsm : Program := parseFile("c/bbu/permuteDestinations.S")
public def loopAsm : Program := parseFile("c/bbu/buildBottomUp.S")
public def buildBottomUpAsm : Program := parseFile("c/bbu/build_bottom_up.S")

/-- `c/build_bottom_up.S`, the file that `bbu_harness` links. -/
public def bbuAsm : Program := parseFile("c/build_bottom_up.S")

end Bbu
