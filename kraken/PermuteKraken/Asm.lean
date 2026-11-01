module

public import Kraken.StateCfg
import ProofKit.Assembly

open ProofKit

namespace State

/-- `c/permute.S`, the output of `gcc -O1` for `c/permute.c`. -/
public def permuteAsm : Program := assemblyFile("../c/permute.S")

end State
