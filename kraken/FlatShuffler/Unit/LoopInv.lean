module

public import FlatShuffler.FlatModel
import all FlatShuffler.FlatModel

@[expose] public section

/-!
# `buildBottomUp`: the invariants of the flat state

`FInv` (the mapping), `HInv` (the loop head) and `Bud` (in an iteration). `loopA` of
`Unit/Defs.lean` is `HInv` at `T = 0`. The lemmas are in `Unit/Loop/Model.lean` and
`Unit/Loop/Step.lean`.
-/

namespace FlatShuffler.Flat

/-! ## The invariant of the mapping -/

-- The mapping of `st`: `dest` maps the slots into the target, `pos` is its inverse, and the
-- target offsets without a slot are the pending generations.
structure FInv (st : St) : Prop where
  n : st.targetSize.toNat ≤ MAX_N
  cnt : st.size.toNat + st.pend.toNat = st.targetSize.toNat
  dest : ∀ i, i < st.size → get st.dest i < st.targetSize
  inv : ∀ i, i < st.size → get st.pos (get st.dest i) = i
  pos : ∀ d, d < st.targetSize →
    get st.pos d = NONE ∨ (get st.pos d < st.size ∧ get st.dest (get st.pos d) = d)

-- The invariant at the loop head (`.26`), for the state `st` and the offset `T`. `x` is the room
-- of the trace buffer for the operations before the loop: 0 for `build_bottom_up`, `4m` for
-- `Emission::run`.
structure HInv (st : St) (T : Word) (x : Nat) : Prop where
  f : FInv st
  le : T.toNat ≤ st.size.toNat
  ops : st.trace.length + 2 * st.pend.toNat + 2 * (st.targetSize.toNat - T.toNat)
    ≤ 4 * st.targetSize.toNat + x

-- In the iteration at `T`: `k` more operations keep the trace bound at `T + 1`.
def Bud (st : St) (T : Word) (k x : Nat) : Prop :=
  st.trace.length + k + 2 * st.pend.toNat + 2 * (st.targetSize.toNat - (T.toNat + 1))
    ≤ 4 * st.targetSize.toNat + x

end FlatShuffler.Flat
