import Shuffler.Permute.Theorems
import Shuffler.Placement.Build

namespace Shuffler.Permute

-- A successful permutation run emits SWAP instructions only. The statement
-- also covers the empty stack and the identity permutation.
theorem permute_noPop_additions (spills : SpillSet) (source : Stack)
    (perm : Permutation source) {result : Stack} {trace : Trace spills source result}
    (hresult : permute spills source perm = .ok ⟨result, trace⟩) :
    trace.noPop ∧ trace.additions = 0 := by
  rw [permute] at hresult
  split at hresult
  · rename_i hne
    have hgo := permute.go.induct spills source hne
      (motive := fun current remaining previous hlen =>
        ∀ {result : Stack} {trace : Trace spills source result},
          permute.go spills source current remaining previous hne hlen = .ok ⟨result, trace⟩ →
          previous.noPop → previous.additions = 0 → trace.noPop ∧ trace.additions = 0)
      ?_ ?_ ?_ ?_ ?_ source perm (.Lit source) rfl hresult
    · exact hgo trivial rfl
    · intro current perm previous hlen top htop ht idx hdepth result trace hresult
      rw [permute.go.eq_1, dite_eq_left ht, dite_eq_left hdepth] at hresult
      contradiction
    · intro current perm previous hlen top htop ht idx hdepth stack' perm' h1 h2 h3 trace' ih
        result trace hresult hn ha
      rw [permute.go.eq_1, dite_eq_left ht, dite_eq_right hdepth] at hresult
      exact ih hresult hn ha
    · intro current perm previous hlen top htop ht search pos hpos hsearch idx hdepth
        result trace hresult
      dsimp only [search, idx] at hsearch hdepth
      rw [permute.go.eq_1, dite_eq_right ht] at hresult
      simp only [hsearch, dite_eq_left hdepth] at hresult
      contradiction
    · intro current perm previous hlen top htop ht search pos hpos hsearch idx hdepth hpos_ne hlt
        stack' perm' h1 h2 h3 trace' ih result trace hresult hn ha
      dsimp only [search, idx] at hsearch hdepth
      rw [permute.go.eq_1, dite_eq_right ht] at hresult
      simp only [hsearch, dite_eq_right hdepth] at hresult
      exact ih hresult hn ha
    · intro current perm previous hlen top htop ht search hsearch result trace hresult hn ha
      dsimp only [search] at hsearch
      rw [permute.go.eq_1, dite_eq_right ht, hsearch] at hresult
      cases hresult
      exact ⟨hn, ha⟩
  · cases hresult
    exact ⟨trivial, rfl⟩

end Shuffler.Permute

namespace Shuffler.Optimality.ValueGraph

-- The occurrence assignment is checked against the exact target. The trace
-- itself comes from the existing production permutation algorithm.
def permuteBuilt (spills : SpillSet) (source target : Stack)
    (perm : Shuffler.Permute.Permutation source) :
    Option (Shuffler.Placement.BuiltTrace spills source target 0) :=
  match hrun : Shuffler.Permute.permute spills source perm with
  | .error _ => none
  | .ok ⟨result, trace⟩ =>
      if ht : result = target then
        let h := Shuffler.Permute.permute_noPop_additions spills source perm hrun
        some ((⟨trace, h.1, h.2⟩ : Shuffler.Placement.BuiltTrace spills source result 0).cast
          rfl ht rfl)
      else none

theorem permuteBuilt_complete (spills : SpillSet) (source target : Stack)
    (perm : Shuffler.Permute.Permutation source)
    (hreach : Shuffler.Permute.all_swaps_reachable perm)
    (htarget : Shuffler.Permute.apply_permutation source perm = target) :
    (permuteBuilt spills source target perm).isSome := by
  obtain ⟨result, trace, hrun, hresult⟩ :=
    Shuffler.Permute.permute_applies_permutation_reachable spills source perm hreach
  unfold permuteBuilt
  split
  · rename_i err herr
    rw [hrun] at herr
    contradiction
  · rename_i actual actualTrace hactual
    have he := congrArg (fun r => r.toOption.map (fun item => item.1))
      (hactual.symm.trans hrun)
    have ht : actual = target :=
      (by simpa [Except.toOption] using he : actual = result).trans (hresult.trans htarget)
    simp only [ht, dite_true, Option.isSome_some]

-- The cost theorem for the existing permutation routine also applies to its
-- checked wrapper. It is optimal for this occurrence assignment.
theorem permuteBuilt_swapCount (spills : SpillSet) (source target : Stack)
    (perm : Shuffler.Permute.Permutation source) (hne : 0 < source.length)
    {built : Shuffler.Placement.BuiltTrace spills source target 0}
    (hresult : permuteBuilt spills source target perm = some built) :
    built.trace.swapCount = Shuffler.Permute.Permutation.swapCount perm
      ⟨source.length - 1, by omega⟩ := by
  unfold permuteBuilt at hresult
  split at hresult
  · contradiction
  · rename_i result trace hrun
    split at hresult
    · rename_i ht
      subst target
      cases hresult
      exact Shuffler.Permute.permute_swapCount spills source perm hne hrun
    · contradiction

end Shuffler.Optimality.ValueGraph
