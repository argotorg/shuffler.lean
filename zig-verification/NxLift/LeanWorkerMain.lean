import NxLift.LeanWorker

/-! The root of the executable `lean-worker` (see `NxLift/LeanWorker.lean`). -/

def main (args : List String) : IO UInt32 := NxLift.LeanWorker.main args
