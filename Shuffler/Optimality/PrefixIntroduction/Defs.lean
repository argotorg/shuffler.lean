import Shuffler.Optimality.Lineage
import Mathlib.Data.List.Count
import Batteries.Data.List.Lemmas

namespace Shuffler.Optimality.PrefixIntroduction

def oldCount (source current : Stack) : Nat :=
  current.countP (fun value => decide (value ∈ source))

-- This is the first target index that contains one more old-kind value
-- than can lie below a full sixteen-slot readable region.
def cutoff (old source target : Stack) : Nat :=
  target.findIdxNth (fun value => decide (value ∈ old)) (oldCount old source - 16)

def prefixDemand (value : Value) (current : Stack) (cut : Nat) : Nat :=
  (current.take cut).count value + if value ∈ current.drop cut then 1 else 0

def protectedValues (value : Value) (source : Stack) : Stack :=
  source.filter (fun other => decide (other ≠ value))

-- Protect all source kinds except the tracked value. Initial copies of the
-- tracked value pay part of its prefix demand; each remaining copy needs
-- a direct introduction. The cutoff also reserves one copy for later demand.
def requiredDirect (value : Value) (source target : Stack) : Nat :=
  let old := protectedValues value source
  if 16 ≤ oldCount old source then
    prefixDemand value target (cutoff old source target) - source.count value
  else 0

end Shuffler.Optimality.PrefixIntroduction
