import Mathlib.GroupTheory.Perm.Basic
import Init.Data.Vector.OfFn

namespace Shuffler.Optimality.BirthPlacement.SourceLazy

-- Store both directions once. Repeated cycle scans then read a finite table.
def cachedPermutation {size : Nat} (permutation : Equiv.Perm (Fin size)) :
    Equiv.Perm (Fin size) :=
  let forward := Vector.ofFn permutation
  let backward := Vector.ofFn permutation.symm
  { toFun := fun index => forward[index.val]
    invFun := fun index => backward[index.val]
    left_inv := by intro index; simp only [forward, backward, Vector.getElem_ofFn]; simp
    right_inv := by intro index; simp only [forward, backward, Vector.getElem_ofFn]; simp }

theorem cachedPermutation_eq {size : Nat} (permutation : Equiv.Perm (Fin size)) :
    cachedPermutation permutation = permutation := by
  ext index
  simp only [cachedPermutation, Equiv.coe_fn_mk, Vector.getElem_ofFn]

end Shuffler.Optimality.BirthPlacement.SourceLazy
