import Shuffler.Optimality.Transport
import Mathlib.Data.Fintype.Fin

namespace Shuffler.Optimality.Transport

-- Cuts with one residue are sixteen positions apart. A legal SWAP can
-- reduce the prefix surplus at at most one of those cuts.
def sparsePotential (residue : Fin 16) (value : Value) (target stack : Stack) : Nat :=
  (Finset.range target.length).sum fun cut =>
    if cut % 16 = residue.val then surplus value target stack cut else 0

def sparseRequiredSwaps (value : Value) (source target : Stack) : Nat :=
  Finset.univ.sup fun residue : Fin 16 => sparsePotential residue value target source

end Shuffler.Optimality.Transport
