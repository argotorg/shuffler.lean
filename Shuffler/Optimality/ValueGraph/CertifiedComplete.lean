import Shuffler.Optimality.ValueGraph.Certified
import Shuffler.Optimality.ValueGraph.Count

namespace Shuffler.Optimality.ValueGraph

-- Every feasible no-growth input passes both finite certificate checks.
-- Thus the returned proof is available for every input on which any eligible
-- production trace exists.
theorem buildCertified_complete (spills : SpillSet) (source target : Stack)
    (hreserve : Shuffler.Placement.Reserve spills source target 0) :
    (buildCertified spills source target).isSome := by
  have hc : (source : Multiset Value) = (target : Multiset Value) := by
    simpa only [add_zero] using hreserve.1.symm
  have hl : source.length = target.length := by
    simpa only [Multiset.coe_card] using congrArg Multiset.card hc
  by_cases hne : 0 < source.length
  · obtain ⟨built, hb⟩ := Option.isSome_iff_exists.mp (build_complete spills source target hreserve)
    obtain ⟨cert, hcert⟩ := Option.isSome_iff_exists.mp
      (certificate_complete source target hl hc hreserve.2.1)
    have hrun : permuteBuilt spills source target (assignment source target hl) = some built := by
      simpa only [build, dite_eq_left hl] using hb
    have hcount := (permuteBuilt_swapCount spills source target _ hne hrun).trans
      (assignment_swapCount source target hl hc hreserve.2.1 cert hcert hne)
    simp only [buildCertified, hb, bind, Option.bind, dite_eq_left hl, dite_eq_left hne,
      hcert, dite_eq_left hcount, Option.isSome_some]
  · have hs : source = [] := List.length_eq_zero_iff.mp (by omega)
    have ht : target = [] := List.length_eq_zero_iff.mp (by omega)
    subst source target
    simp [buildCertified, build, permuteBuilt, Shuffler.Permute.permute,
      Shuffler.Placement.BuiltTrace.cast, Trace.swapCount]

theorem buildCertified_succeeds_iff_reserve (spills : SpillSet) (source target : Stack) :
    (buildCertified spills source target).isSome ↔ Shuffler.Placement.Reserve spills source target 0 := by
  constructor
  · intro hs
    obtain ⟨result, _⟩ := Option.isSome_iff_exists.mp hs
    exact Shuffler.Placement.CanPlace.reserve
      ⟨result.built.trace, result.built.noPop, result.built.additions⟩
  · exact buildCertified_complete spills source target
 theorem buildCertified_built (spills : SpillSet) (source target : Stack)
    (result : OptimalTrace spills source target)
    (hr : buildCertified spills source target = some result) :
    build spills source target = some result.built := by
  unfold buildCertified at hr
  cases hb : build spills source target with
  | none => simp [hb] at hr
  | some built =>
      simp only [hb, bind, Option.bind] at hr
      split at hr
      · rename_i hlen
        split at hr
        · cases hc : certificate source target hlen with
          | none => simp [hc] at hr
          | some cert =>
              simp only [hc] at hr
              split at hr
              · exact congrArg (fun r : OptimalTrace spills source target => some r.built)
                  (Option.some.inj hr)
              · contradiction
        · split at hr
          · exact congrArg (fun r : OptimalTrace spills source target => some r.built)
              (Option.some.inj hr)
          · contradiction
      · contradiction

-- The plain builder has the same optimum guarantee. A caller need not run
-- the finite certificate checks again to use this theorem.
theorem build_min_swaps (spills : SpillSet) (source target : Stack)
    (built : Shuffler.Placement.BuiltTrace spills source target 0)
    (hb : build spills source target = some built)
    (other : Trace spills source target) (he : Eligible 0 other) :
    built.trace.swapCount ≤ other.swapCount := by
  have hr := Shuffler.Placement.CanPlace.reserve ⟨built.trace, built.noPop, built.additions⟩
  obtain ⟨result, hc⟩ := Option.isSome_iff_exists.mp
    (buildCertified_complete spills source target hr)
  have hs := buildCertified_built spills source target result hc
  have heq : built = result.built := Option.some.inj (hb.symm.trans hs)
  rw [heq]
  exact result.min_swaps other he

theorem build_weightedOptimal (costs : PrimitiveCosts) (weights : Weights)
    (spills : SpillSet) (source target : Stack)
    (built : Shuffler.Placement.BuiltTrace spills source target 0)
    (hb : build spills source target = some built) :
    WeightedOptimal costs weights 0 built.trace :=
  (⟨built, build_min_swaps spills source target built hb⟩ : OptimalTrace spills source target).weightedOptimal
    costs weights

end Shuffler.Optimality.ValueGraph
