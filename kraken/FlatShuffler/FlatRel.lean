module

public import FlatShuffler.FlatModel
import all FlatShuffler.FlatModel
public import FlatShuffler.ModelLemmas
import all FlatShuffler.ModelLemmas

@[expose] public section

/-!
The relation of the flat model (`FlatModel.lean`) to the list model (`Model.lean`).

`listEnv`, `listSource` and `listDests` are the inputs of the list model that the inputs of
`build_bottom_up` give. `Rel r res` is: the result `r` of `build_bottom_up` is the result `res`
of `FlatShuffler.buildBottomUp`. The two results are done, or blocked at the same slot by the same excess,
with the same stack and the same operations; or `r` is `-2` and `res` is an assertion.
`FlatBridge.lean` states that `Rel` holds.
-/

namespace FlatShuffler.Flat

-- The environment: the first `n` slots of `target` and the bytes of `spills`.
def listEnv (n : Nat) (target : Vector StackSlot MAX_N) (spills : BitVec 32 → BitVec 8) : Env :=
  ⟨target.toList.take n, fun i => UInt8.ofBitVec (spills (BitVec.ofNat 32 i))⟩

-- The source stack: the first `m` slots of `data`.
def listSource (m : Nat) (data : Vector StackSlot MAX_N) : List StackSlot := data.toList.take m

-- The destination of each source slot: the first `m` words of `dest`.
def listDests (m : Nat) (dest : Vector Word MAX_N) : List Nat := (dest.toList.take m).map BitVec.toNat

-- The stack of a flat state: the slots below `size`.
def slotsOf (fs : St) : List StackSlot :=
  (List.range fs.size.toNat).map fun i => get fs.data (BitVec.ofNat 64 i)

-- The flat state `fs` has the stack and the operations of the list state `st`, and the
-- blocked slot `pos` with the excess `excess`.
structure Holds (fs : St) (st : FlatShuffler.St) (pos excess : Nat) : Prop where
  trace : fs.trace = st.trace
  data : slotsOf fs = st.slots.map Slot.val
  blk0 : fs.blockedOffset = BitVec.ofNat 64 pos
  blk1 : fs.blockedExcess = BitVec.ofNat 64 excess

-- The result `r` of `build_bottom_up` is the result of the list model. A done result has the
-- blocked words `0`, as `build_bottom_up` writes them.
def Rel (r : Word × Option St) : M FlatShuffler.St → Prop
  | .ok st => ∃ fs, r = (BitVec.ofNat 64 st.trace.length, some fs) ∧ Holds fs st 0 0
  | .error (.blocked pos excess st) =>
    ∃ fs, r = (BitVec.ofNat 64 st.trace.length, some fs) ∧ Holds fs st pos excess
  | .error .assertion => r.1 = -2#64

end FlatShuffler.Flat
