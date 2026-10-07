import Shuffler.Optimality.BirthPlacement.Realize.Lemmas
import Shuffler.Optimality.DirectDominance.Theorems
import Shuffler.Optimality.BirthPlacement.Events.Theorems

namespace Shuffler.Optimality.BirthPlacement

def PhysicallyAvailable (spills : SpillSet) (current : Stack) (value : Value) : BirthMethod → Prop
  | .direct => Shuffler.Placement.Free spills value
  | .dup => value ∈ current.drop (current.length - 16)

theorem physicallyAvailable_of_counts (spills : SpillSet) (current target births : Stack)
    (height : Nat) (value : Value) (method : BirthMethod)
    (hlen : current.length = height)
    (hcount : current.count value = (births.take height).count value)
    (hfrozen : current.take (height - 16) = target.take (height - 16))
    (havailable : BirthAvailable spills target births height value method) :
    PhysicallyAvailable spills current value method := by
  cases method with
  | direct => exact havailable
  | dup =>
    have he := congrArg (List.count value) (List.take_append_drop (height - 16) current)
    simp only [List.count_append, hfrozen, hcount] at he
    have hp : 0 < (current.drop (height - 16)).count value := by
      change (target.take (height - 16)).count value < (births.take height).count value at havailable
      omega
    simpa only [PhysicallyAvailable, hlen] using List.count_pos_iff.mp hp

theorem traceEvents_appendDirect (trace : Trace spills source target) (value : Value)
    (hfree : Shuffler.Placement.Free spills value) :
    traceEvents (DirectDominance.appendDirect trace value hfree) =
      traceEvents trace ++ [(.direct, value)] := by
  cases value <;> try rfl
  simp [Shuffler.Placement.Free, Value.can_be_freely_generated, SpillSet.is_spilled] at hfree

-- Choose the first readable copy only after the count proof supplies one.
-- The requested instruction kind is preserved even when direct generation is free.
def appendBirth (spills : SpillSet) (current : Stack) (value : Value) (method : BirthMethod)
    (havailable : PhysicallyAvailable spills current value method) :
    { trace : Trace spills current (current ++ [value]) //
      trace.noPop ∧ trace.additions = {value} ∧ trace.swapCount = 0 ∧
        traceEvents trace = [(method, value)] } := by
  cases method with
  | direct =>
    change Shuffler.Placement.Free spills value at havailable
    exact ⟨DirectDominance.appendDirect (.Lit current) value havailable,
      (DirectDominance.appendDirect_noPop _ _ _).mpr trivial,
      by rw [DirectDominance.appendDirect_additions]; rfl,
      by rw [DirectDominance.appendDirect_swapCount]; rfl,
      by rw [traceEvents_appendDirect]; rfl⟩
  | dup =>
    let cut := current.length - 16
    let readable := current.drop cut
    let offset := readable.idxOf value
    have hoffset : offset < readable.length := List.idxOf_lt_length_iff.mpr havailable
    have hlength : readable.length = current.length - cut := List.length_drop
    let position := cut + offset
    have hposition : position < current.length := by dsimp [position]; omega
    let depth := current.length - position
    have hdlen : depth ≤ current.length := Nat.sub_le _ _
    have hdpos : 1 ≤ depth := by dsimp [depth]; omega
    have hdreach : depth ≤ MAX_DUP_DEPTH + 1 := by
      dsimp [depth, position, cut]
      unfold MAX_DUP_DEPTH
      omega
    have hv : current[current.length - depth] = value := by
      have he : current.length - depth = position := by dsimp [depth]; omega
      have hr : readable[offset]'hoffset = value := List.getElem_idxOf hoffset
      simpa only [he, readable, position, List.getElem_drop] using hr
    let trace := Trace.Dup depth hdlen hdpos hdreach (.Lit (spills := spills) current)
    have he : current ++ [current[current.length - depth]] = current ++ [value] := by rw [hv]
    refine ⟨he ▸ trace, (Trace.noPop_cast _ _).mpr trivial, ?_, ?_, ?_⟩
    · rw [Trace.additions_cast]
      simp only [trace, Trace.additions, hv, zero_add]
    · rw [swapCount_cast]
      rfl
    · rw [traceEvents_cast]
      simp only [trace, traceEvents, hv, List.nil_append]

end Shuffler.Optimality.BirthPlacement
