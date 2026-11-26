/-! The parallel map of the test suites: `parMapM f xs` runs `f` on each element in a task of its own and gives the results in
the order of `xs`. An IO error of one element is thrown after all tasks end (the first in the order of `xs`). The Lean processes
of the tasks stay under the bound of `NxLift.Proc.runLimited` (the runner sets it), so the map can start one task for
each element. -/

namespace Skel.Test

/-- `List.mapM f xs`, with each `f x` in a task of its own (a dedicated thread: a task waits for its process most of the
time). The results are in the order of `xs`. A task prints to the streams of the caller (the standard streams are per
thread, and the runner captures those of each suite). -/
def parMapM {α β : Type} (f : α → IO β) (xs : List α) : IO (List β) := do
  let out ← IO.getStdout
  let err ← IO.getStderr
  let tasks ← xs.mapM fun x => IO.asTask (prio := .dedicated) (IO.withStdout out (IO.withStderr err (f x)))
  let rs ← tasks.mapM fun t => (IO.wait t : IO _)
  rs.mapM fun r => IO.ofExcept r

end Skel.Test
