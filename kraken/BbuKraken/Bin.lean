module

public import BbuKraken.Final
import all BbuKraken.Final
public import BbuKraken.BinHost
import all BbuKraken.BinHost

@[expose] public section

namespace Bbu

/-- The C++ method in the binary checked by `test/bin_check.sh`. -/
theorem buildBottomUp_binary_correct :
    letI := binLinked.decls
    Unit.UnitThmWithExit loopAsm Unit.loopA 2068 Unit.loopQ Unit.loopX :=
  buildBottomUp_correct binLinked binBoundary

end Bbu
