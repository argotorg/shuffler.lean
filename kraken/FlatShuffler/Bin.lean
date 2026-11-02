module

public import FlatShuffler.Final
import all FlatShuffler.Final
public import FlatShuffler.BinHost
import all FlatShuffler.BinHost

@[expose] public section

namespace FlatShuffler

/-- The C++ method in the binary checked by `test/bin_check.sh`. -/
theorem buildBottomUp_binary_correct :
    letI := binLinked.decls
    Unit.UnitThmWithExit loopAsm Unit.loopA 2068 Unit.loopQ Unit.loopX :=
  buildBottomUp_correct binLinked binBoundary

end FlatShuffler
