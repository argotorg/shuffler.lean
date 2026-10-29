import Shuffler.Mapping

namespace MappingTests

private def partialMapping : Mapping 4 3 :=
  ((⊥ : Mapping 4 3).bind 0 2 rfl rfl).bind 1 0 (by decide) (by decide)

-- Equal positions leave every lookup unchanged, whether bound or unbound.
example : ∀ a : Fin 4,
    List.ofFn (partialMapping.swapDestinations a a) = List.ofFn partialMapping ∧
    List.ofFn (partialMapping.swapDestinations a a).symm = List.ofFn partialMapping.symm := by
  decide

-- Two swaps restore all forward and inverse lookups for every pair of positions.
example : ∀ a b : Fin 4,
    List.ofFn ((partialMapping.swapDestinations a b).swapDestinations a b) =
      List.ofFn partialMapping ∧
    List.ofFn ((partialMapping.swapDestinations a b).swapDestinations a b).symm =
      List.ofFn partialMapping.symm := by
  decide

-- A mapping with no targets can still exchange source positions.
example : ∀ a b p : Fin 2, (⊥ : Mapping 2 0).swapDestinations a b p = none := by
  decide

end MappingTests
