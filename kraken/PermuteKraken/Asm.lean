module

public import Kraken.StateCfg
import Kraken.X64.Parser

open Kraken.X64.Parser

namespace State

/-- `c/permute.S`, the output of `gcc -O1` for `c/permute.c`. -/
public def permuteAsm : Program := parseFile("c/permute.S")

end State
