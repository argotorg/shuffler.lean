import Shuffler.Permute.Defs
import Shuffler.Permute.Lemmas

namespace Shuffler.Permute

-- applies the permutation perm to the source stack via the inverse equivalence
-- every proper permutation has an inverse
def apply_permutation (source : Stack) (perm : Permutation source) : Stack :=
  List.ofFn (λ k => source[perm.symm k])

-- Specialize the invariant to the initial state. The first and last equalities
-- unfold permute and apply_permutation respectively.
theorem permute_applies_permutation
  (source : Stack)
  (perm : Permutation source)
  (hlo : source.length > 0)
  (hhi : source.length < 17) :
    (permute source perm hlo hhi).1 = apply_permutation source perm := by
  calc
    (permute source perm hlo hhi).1
        = (permute.go source hlo hhi source perm (.Lit source) rfl).1 := rfl
    _ = apply_permutation' source (n := source.length) perm rfl :=
      permute_go_spec source hlo hhi source perm (.Lit source) rfl
    _ = apply_permutation source perm := rfl

end Shuffler.Permute
