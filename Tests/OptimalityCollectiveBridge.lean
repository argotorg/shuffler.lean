import Shuffler.Optimality.Collective.Bridge
import Shuffler.Optimality.Collective.HeightCut
import Shuffler.Placement.Build

namespace Tests.OptimalityCollectiveBridge

open Shuffler.Placement Shuffler.Optimality.Collective
open Shuffler.Optimality.PrefixIntroduction

private def old : Stack := List.replicate 15 (.Lit 0)
private def fresh : Stack := [.Var ⟨42⟩, .Var ⟨43⟩, .Var ⟨42⟩, .Var ⟨43⟩]
private def spills : SpillSet := {⟨42⟩, ⟨43⟩}
private def sample : Trace spills old (fresh ++ old) :=
  (buildOfReserve spills old (fresh ++ old) (fresh : Multiset Value) (by decide)).trace

-- The first two outputs use real freeze events. The last two use the
-- finished target; the final cut leaves only the fifteen old copies.
#guard (residual 1 sample).length = 16
#guard (residual 2 sample).length = 16
#guard (residual 3 sample).length = 16
#guard (residual 4 sample).length = 15
#guard oldCount old (residual 1 sample) = 15
#guard oldCount old (residual 2 sample) = 15
#guard oldCount old (residual 3 sample) = 15
#guard oldCount old (residual 4 sample) = 15
#guard (freshKinds old (residual 1 sample)).card = 1
#guard (freshKinds old (residual 4 sample)).card = 0

example : (takeHeight 17 sample).Joins sample := takeHeight_joined sample

example : (takeHeight 17 sample).NoPop :=
  takeHeight_noPop sample (buildOfReserve spills old (fresh ++ old)
    (fresh : Multiset Value) (by decide)).noPop

example : (takeHeight 17 sample).current.take 1 = (fresh ++ old).take 1 :=
  takeHeight_take sample (buildOfReserve spills old (fresh ++ old)
    (fresh : Multiset Value) (by decide)).noPop

end Tests.OptimalityCollectiveBridge
