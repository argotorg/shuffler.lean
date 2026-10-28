module

public import Kraken.StateCfg
import Kraken.X64.Parser

open Kraken.X64.Parser

namespace Bbu

/-! The output of `gcc -O1` for `c/build_bottom_up.c`, one program for each function. -/

public def isSpilledAsm : Program := parseFile("c/bbu/is_spilled.S")
public def positionOfAsm : Program := parseFile("c/bbu/position_of.S")
public def shallowestCopyAsm : Program := parseFile("c/bbu/shallowest_copy.S")
public def addAsm : Program := parseFile("c/bbu/add.S")
public def swapWithAsm : Program := parseFile("c/bbu/swap_with.S")
public def produceAsm : Program := parseFile("c/bbu/produce.S")
public def generateAsm : Program := parseFile("c/bbu/generate.S")
public def finishAsm : Program := parseFile("c/bbu/finish.S")
public def takeBoundAsm : Program := parseFile("c/bbu/take_bound.S")
public def urgentAsm : Program := parseFile("c/bbu/urgent.S")
public def stepAsm : Program := parseFile("c/bbu/step.S")
public def buildBottomUpAsm : Program := parseFile("c/bbu/build_bottom_up.S")

/-- `c/build_bottom_up.S`, the file that `bbu_harness` links. -/
public def bbuAsm : Program := parseFile("c/build_bottom_up.S")

end Bbu
