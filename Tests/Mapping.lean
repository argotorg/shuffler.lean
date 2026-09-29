import Shuffler.Mapping

namespace MappingTests

private def partialMapping : Mapping 4 3 :=
  ((⊥ : Mapping 4 3).bind 0 2 rfl rfl).bind 1 0 (by decide) (by decide)

-- Both bound positions exchange destinations, and inverse lookups follow them.
example : List.ofFn (partialMapping.swapDestinations 0 1) =
    [some 0, some 2, none, none] ∧
    List.ofFn (partialMapping.swapDestinations 0 1).symm = [some 0, none, some 1] := by
  decide

-- A binding can move to an unbound position at the end of the source.
example : List.ofFn (partialMapping.swapDestinations 0 3) =
    [none, some 0, none, some 2] ∧
    List.ofFn (partialMapping.swapDestinations 0 3).symm = [some 1, none, some 3] := by
  decide

-- The same move works when the unbound position is the first argument.
example : List.ofFn (partialMapping.swapDestinations 3 0) =
    [none, some 0, none, some 2] ∧
    List.ofFn (partialMapping.swapDestinations 3 0).symm = [some 1, none, some 3] := by
  decide

-- Two unbound positions leave every lookup unchanged.
example : List.ofFn (partialMapping.swapDestinations 2 3) =
    List.ofFn partialMapping ∧
    List.ofFn (partialMapping.swapDestinations 2 3).symm = List.ofFn partialMapping.symm := by
  decide

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

-- Swaps do not require a binding, including on a source with one position.
example : (⊥ : Mapping 1 1).swapDestinations 0 0 0 = none ∧
    ((⊥ : Mapping 1 1).swapDestinations 0 0).symm 0 = none := by
  decide

end MappingTests
