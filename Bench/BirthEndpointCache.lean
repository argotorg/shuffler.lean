import Shuffler.Optimality.BirthPlacement.Word.Cached

open Shuffler.Optimality.BirthPlacement

set_option maxRecDepth 10000
set_option maxHeartbeats 0

private def checksum {size : Nat} (perm : Equiv.Perm (Fin size)) : Nat :=
  (List.ofFn fun index => (perm index).val + (perm.symm index).val).sum

def main : IO Unit := do
  for size in [40, 80, 160] do
    let values := List.ofFn fun index : Fin size => index.val % 4
    let word := fun index : Fin size => values[index.val]'(by simp [values])
    -- The local IO cell forces each pure result before its ending time is read.
    let result ← IO.mkRef 0
    let start ← IO.monoMsNow
    result.set (checksum (Word.optimal 16 word word (fun _ => rfl)))
    let middle ← IO.monoMsNow
    let original ← result.get
    result.set (checksum (Word.cachedOptimal 16 word word (fun _ => rfl)))
    let finish ← IO.monoMsNow
    let cached ← result.get
    if original ≠ cached ∨ original ≠ size * (size - 1) then
      throw (IO.userError "endpoint checksum differs")
    IO.println s!"n={size} original_ms={middle - start} cached_ms={finish - middle} checksum={cached}"
