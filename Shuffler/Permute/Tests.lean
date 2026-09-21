import Shuffler.Permute.Defs
import Mathlib.Data.Fintype.Perm

namespace Shuffler.Permute.Tests

-- Observe the production result without requiring equality on proof-carrying traces.
private def result (source : Stack) (perm : Permutation source) : Except ℕ Stack :=
  match permute source perm with
  | .ok ⟨res, _⟩ => .ok res
  | .error (.Blocked depth) => .error depth

#guard result [] 1 = .ok []
#guard result [7] 1 = .ok [7]
#guard result [0, 1, 2] 1 = .ok [0, 1, 2]

-- Exercise a displaced top, a fixed top, and a cycle longer than a swap.
#guard result [0, 1, 2] (Equiv.swap 0 2) = .ok [2, 1, 0]
#guard result [0, 1, 2] (Equiv.swap 0 1) = .ok [1, 0, 2]
#guard result [0, 1, 2] (Equiv.swap 0 1 * Equiv.swap 1 2) = .ok [2, 0, 1]
#guard result [7, 7, 3] (Equiv.swap 0 2) = .ok [3, 7, 7]

-- Depth 16 is reachable, including when the stack has unreachable positions.
#guard result (List.range 17) (Equiv.swap ⟨0, by decide⟩ ⟨16, by decide⟩) =
  .ok ((List.range 17).swap 0 16)
#guard result (List.range 20) (Equiv.swap ⟨3, by decide⟩ ⟨19, by decide⟩) =
  .ok ((List.range 20).swap 3 19)
#guard result (List.range 20) 1 = .ok (List.range 20)

-- Failure with a displaced top, and failure while searching below a fixed top.
#guard result (List.range 18) (Equiv.swap ⟨0, by decide⟩ ⟨17, by decide⟩) = .error 1
#guard result (List.range 19) (Equiv.swap ⟨0, by decide⟩ ⟨1, by decide⟩) = .error 1
#guard result (List.range 20) (Equiv.swap ⟨0, by decide⟩ ⟨19, by decide⟩) = .error 3

-- A reachable cycle completes before the remaining unreachable cycle blocks.
#guard result (List.range 20)
  (Equiv.swap ⟨0, by decide⟩ ⟨1, by decide⟩ *
    Equiv.swap ⟨18, by decide⟩ ⟨19, by decide⟩) = .error 2

-- Compare every permutation of five positions with the reference definition.
#guard decide (∀ perm : Permutation [0, 1, 2, 3, 4],
  result [0, 1, 2, 3, 4] perm = .ok (apply_permutation [0, 1, 2, 3, 4] perm))

end Shuffler.Permute.Tests
