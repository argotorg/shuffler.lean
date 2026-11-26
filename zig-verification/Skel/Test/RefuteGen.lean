import Skel.Toy.Held

/-! The generated refute text of a function for the suites `sumrefute`, `findrefute`, `walkrefute` and `fillrefute`.
`load fn` runs `generateUpper` (`Skel.Toy.Held.upperOf`), the generator of `skel run`, and keeps its rows, its model text
and the two files of its `RefuteSpec`. `refuteText` and `replayText` give the same texts as `Upper.withRefute` and the
replay of a counterexample, for any seed and number of samples. A change of `modelText` in a `Gen` is in the files that
`refuteText` and `replayText` give. -/

namespace RefuteGen

open Skel Skel.Gen Skel.Toy.RefuteCommon

/-- The generated rows and model text of a function, and the files of its refute spec. -/
structure Gen extends Generated where
  fs : Files

/-- The generation of `fn`, or an IO error that names the cause. -/
def load (fn : String) : IO Gen := do
  match Skel.Toy.Held.upperOf fn with
  | .error e => throw (IO.userError s!"{fn}: generate failed: {Skel.Toy.Held.causeText e}")
  | .ok u =>
    match u.spec with
    | .error e => throw (IO.userError s!"{fn}: no sampler: {Skel.Toy.Held.causeText e}")
    | .ok r => pure { u.generated with fs := r.files }

/-- The refute file of a candidate (`RefuteCommon.refuteText`), for the seed `seed` and `samples` samples. -/
def refuteText (seed samples : Nat) (g : Gen) (ob : ObId) (c : Candidate) : Option String :=
  Skel.Toy.RefuteCommon.refuteText g.fs seed samples g.toGenerated ob c

/-- The file of a stored counterexample (`RefuteCommon.replayText`). -/
def replayText (g : Gen) (cex : Cex) : Option String :=
  Skel.Toy.RefuteCommon.replayText g.fs g.toGenerated cex

end RefuteGen
