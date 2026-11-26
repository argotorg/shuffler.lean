module

public import Lift.Sem.Heap

@[expose] public section

namespace Lift.Sem

deriving instance DecidableEq for Cell
deriving instance DecidableEq for Obj
deriving instance DecidableEq for Res

end Lift.Sem
