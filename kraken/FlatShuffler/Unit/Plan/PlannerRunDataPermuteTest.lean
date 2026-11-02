module

public import FlatShuffler.Unit.Plan.PlannerRunDataPermute
import all FlatShuffler.Unit.Plan.PlannerRunDataPermute

@[expose] public section

namespace FlatShuffler.Flat.DataPermuteTest

set_option maxRecDepth 4096

private def x : StackSlot := ⟨1, Value, Const⟩
private def y : StackSlot := ⟨2, Value, Const⟩
private def z : StackSlot := ⟨3, Value, Const⟩

private def slots (xs : List StackSlot) : Vector StackSlot maxStackSize :=
  Vector.ofFn fun i => xs[i.val]?.getD .junk

private def words (xs : List Word) : Vector Word maxStackSize :=
  Vector.ofFn fun i => xs[i.val]?.getD 0

private def st : St :=
  ⟨slots [y, x], 2, fun _ => 0, slots [x, y, x], 2, [],
    words [1, 0], words [1, 0], 0, 0, 0⟩

private def old : Vector StackSlot maxStackSize := Vector.replicate maxStackSize z
private def locals : Locals := ⟨initial, initial, initial⟩

-- A zero-size call uses no data elements.
#guard (permute (restoreData 0 old {st with size := 0}) initial).1 = .done
#guard get (permute (restoreData 0 old {st with size := 0}) initial).2.data 0 = z

-- A swap below the capacity leaves the first element above it unchanged.
#guard (permuteMapping (restoreData 2 old st)).1 = .done
#guard get (permuteMapping (restoreData 2 old st)).2.data 0 = y
#guard get (permuteMapping (restoreData 2 old st)).2.data 1 = x
#guard get (permuteMapping (restoreData 2 old st)).2.data 2 = z
#guard (permuteMapping (restoreData 2 old st)).2.trace = [Op.swapW 1]

#guard (permuteAtLowestHeight (words [0, 1]) locals (restoreData 2 old st)).1 = .done
#guard get (permuteAtLowestHeight (words [0, 1]) locals (restoreData 2 old st)).2.data 2 = z
#guard (permuteAtLowestHeight (words [0, 1]) locals st).2.size = st.size
#guard (permuteAtLowestHeight (words [0, 1]) locals st).2.targetSize = st.targetSize

-- The maximum capacity includes the last element of the model array.
#guard get (restoreData maxStackSize old {st with data := Vector.replicate maxStackSize x}).data
  (BitVec.ofNat 64 (maxStackSize - 1)) = x

private def bad : Vector Word maxStackSize := words [0, 2]

-- A malformed permutation can read past the physical capacity.
-- The bijection premise in the frame theorem rules out this case.
example : ¬ Unit.Bij st.size bad := by
  intro h
  have ht : (1#64) < st.size := by decide +kernel
  have hb : ¬ get bad (1#64) < st.size := by decide +kernel
  exact hb (h.1 _ ht)

private def tailY : St := {st with data := slots [x, y, y]}
#guard (permuteLoop 1 (restoreData 2 old tailY) 1 bad).1 = .blocked
#guard (permuteLoop 1 tailY 1 bad).1 = .assertionFailed

-- Arbitrary tail values remain unchanged outside a one-element buffer.
example (tail : Vector StackSlot maxStackSize) :
    get (restoreData 1 tail st).data 0 = get st.data 0 :=
  restoreData_get 1 tail st 0 (by decide +kernel)

example (tail : Vector StackSlot maxStackSize) :
    (restoreData 1 tail st).data[1] = tail[1] := by
  simp only [restoreData, Vector.getElem_ofFn]
  rfl

example (tail : Vector StackSlot maxStackSize) : (restoreData 0 tail st).data = tail := by
  apply Vector.ext
  intro i hi
  simp only [restoreData, Vector.getElem_ofFn, Nat.not_lt_zero, ↓reduceIte]

end FlatShuffler.Flat.DataPermuteTest
