#!/usr/bin/env bash
# Check the public proof boundary and reject imports that bypass it.
set -euo pipefail
dir=$(cd "$(dirname "$0")/.." && pwd)
root=$(cd "$dir/.." && pwd)
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

lean_file() {
  (cd "$root" && LEAN_NUM_THREADS=1 nice lake env lean -DElab.async=false -E warning "$1")
}

cat > "$tmp/Public.lean" <<'EOF'
module
import Theorems.Main
import Lean

example : ShufflerVerification.PlannerAssemblyContract
    ShufflerVerification.PlannerInputAssumptions
    ShufflerVerification.PlannerResultMatchesModel :=
  ShufflerVerification.planner_assembly_matches_model

example : ShufflerVerification.PlannerBinaryContract
    ShufflerVerification.PlannerInputAssumptions
    ShufflerVerification.PlannerResultMatchesModel :=
  ShufflerVerification.planner_binary_matches_model

example : ShufflerVerification.PlannerAssemblyNormalReturnContract
    ShufflerVerification.PlannerInputsValidForNormalReturn
    ShufflerVerification.PlannerResultMatchesModel :=
  ShufflerVerification.planner_assembly_returns_normally

example : ShufflerVerification.PlannerBinaryNormalReturnContract
    ShufflerVerification.PlannerInputsValidForNormalReturn
    ShufflerVerification.PlannerResultMatchesModel :=
  ShufflerVerification.planner_binary_returns_normally

open ShufflerVerification in
example (input : PlannerInput) (validInput : PlannerInputsValidForNormalReturn input) :
    PlannerModelPostcondition PlannerReturnsCorrectPlanOrBlocked input :=
  planner_model_returns_correct_plan_or_blocked input validInput

open ShufflerVerification in
example : PlannerAssemblyNormalReturnContract PlannerInputsValidForNormalReturn
    PlannerReturnsCorrectPlanOrBlocked :=
  planner_assembly_returns_correct_plan_or_blocked

open ShufflerVerification in
example : PlannerBinaryNormalReturnContract PlannerInputsValidForNormalReturn
    PlannerReturnsCorrectPlanOrBlocked :=
  planner_binary_returns_correct_plan_or_blocked

open ShufflerVerification in
example {inputAssumptions : PlannerInput → Prop}
    {postcondition : PlannerInput → PlannerExecutionResult → Prop}
    (representationAssumptions : ∀ input, inputAssumptions input → PlannerInputAssumptions input)
    (modelPostcondition : ∀ input, inputAssumptions input →
      PlannerModelPostcondition postcondition input) :
    PlannerAssemblyContract inputAssumptions postcondition :=
  planner_assembly_transfers_model_postcondition representationAssumptions modelPostcondition

open ShufflerVerification in
example {inputAssumptions : PlannerInput → Prop}
    {postcondition : PlannerInput → PlannerExecutionResult → Prop}
    (representationAssumptions : ∀ input, inputAssumptions input → PlannerInputAssumptions input)
    (modelPostcondition : ∀ input, inputAssumptions input →
      PlannerModelPostcondition postcondition input) :
    PlannerBinaryContract inputAssumptions postcondition :=
  planner_binary_transfers_model_postcondition representationAssumptions modelPostcondition

open ShufflerVerification in
example (input : PlannerInput) (locals : Nat → FlatShuffler.Flat.RunU)
    (assumptions : PlannerInputAssumptions input)
    (postcondition : PlannerInput → PlannerExecutionResult → Prop)
    (modelPostcondition : PlannerModelPostcondition postcondition input) :
    postcondition input (input.execute locals) :=
  planner_flat_execution_transfers_model_postcondition input locals assumptions
    postcondition modelPostcondition

open ShufflerVerification in
example (input : PlannerInput) (validInput : PlannerInputsValidForNormalReturn input) :
    PlannerInputAssumptions input :=
  PlannerInputsValidForNormalReturn.inputAssumptions input validInput

open ShufflerVerification in
example (input : PlannerInput) (locals : Nat → FlatShuffler.Flat.RunU)
    (validInput : PlannerInputsValidForNormalReturn input) :
    (input.execute locals).1 ≠ .assertionFailed :=
  planner_flat_execution_does_not_assert input locals validInput

open ShufflerVerification in
example (input : PlannerInput) (oversized : FlatShuffler.maxStackSize < input.planner.sourceSize.toNat) :
    ¬ PlannerInputAssumptions input := fun assumptions =>
  Nat.not_le_of_lt oversized assumptions.sourceSizeFitsBuffer

open ShufflerVerification in
example (input : PlannerInput) (oversized : FlatShuffler.maxStackSize < input.planner.targetSize.toNat) :
    ¬ PlannerInputAssumptions input := fun assumptions =>
  Nat.not_le_of_lt oversized assumptions.targetSizeFitsBuffer

open ShufflerVerification in
example (input : PlannerInput) (slot : FlatShuffler.StackSlot)
    (active : slot ∈ input.sourceSlots ++ input.targetSlots)
    (unsupported : 4 ≤ slot.kind.toNat) : ¬ PlannerInputAssumptions input :=
  fun assumptions => Nat.not_lt_of_ge unsupported (assumptions.slotKindsAreSupported slot active)

open ShufflerVerification in
example (input : PlannerInput) (slot : FlatShuffler.StackSlot)
    (active : slot ∈ input.sourceSlots ++ input.targetSlots)
    (junkKind : slot.kind = FlatShuffler.Junk) (noncanonical : slot ≠ .junk) :
    ¬ PlannerInputAssumptions input := fun assumptions =>
  noncanonical ((assumptions.slotsHaveCanonicalEncoding slot active).1 junkKind)

open ShufflerVerification in
example (input : PlannerInput) (position : Fin input.sourceSlots.length)
    (nonzero : FlatShuffler.Flat.get input.initialState.dropped (.ofNat 64 position.val) ≠ 0) :
    ¬ PlannerInputAssumptions input := fun assumptions =>
  nonzero (assumptions.sourceDroppedBytesAreZero position)

open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  for n in [`List.allSome, `Mem, `Shuffler.Planner.run, `ShufflerBridge.Planner.plannerRun_corr] do
    if env.contains n then throwError "implementation declaration is public: {n}"
EOF
lean_file "$tmp/Public.lean"

cat > "$tmp/ModelReview.lean" <<'EOF'
module
import Theorems.PlannerModel

open ShufflerVerification in
example (input : PlannerInput) (validInput : PlannerInputsValidForNormalReturn input) :
    PlannerModelPostcondition PlannerReturnsCorrectPlanOrBlocked input :=
  planner_model_returns_correct_plan_or_blocked input validInput

open ShufflerVerification in
example (input : PlannerInput) (locals : Nat → FlatShuffler.Flat.RunU)
    (assumptions : PlannerInputAssumptions input) :
    PlannerResultMatchesModel input (input.execute locals) :=
  planner_flat_execution_matches_model input locals assumptions
EOF
lean_file "$tmp/ModelReview.lean"

cat > "$tmp/PlannerSizeFields.lean" <<'EOF'
module
import Theorems.PlannerInput

open FlatShuffler FlatShuffler.Flat ShufflerVerification

example : maxStackSize = 1024 := rfl

private def inputWithSizes (sourceSize targetSize : Word) : PlannerInput :=
  { planner :=
      { source := Vector.replicate maxStackSize .junk
        sourceSize := sourceSize
        target := Vector.replicate maxStackSize .junk
        targetSize := targetSize
        allowed := false }
    takeWildcardSlots := false
    initialState :=
      { spills := fun _ => 0
        dropped := Vector.replicate maxStackSize 0
        saw := false
        data := Vector.replicate maxStackSize .junk
        trace := []
        sources := Vector.replicate maxStackSize 0 } }

-- Each size selects the active prefix of its own input buffer.
example : (inputWithSizes 0 (.ofNat 64 maxStackSize)).sourceSlots = [] ∧
    (inputWithSizes 0 (.ofNat 64 maxStackSize)).targetSlots.length = maxStackSize := by
  change (Vector.replicate maxStackSize (.junk : StackSlot)).toList.take 0 = [] ∧
    ((Vector.replicate maxStackSize (.junk : StackSlot)).toList.take maxStackSize).length = maxStackSize
  simp only [List.take_zero, List.length_take, Vector.length_toList, Nat.min_self, and_self]

example : (inputWithSizes (.ofNat 64 maxStackSize) 0).sourceSlots.length = maxStackSize ∧
    (inputWithSizes (.ofNat 64 maxStackSize) 0).targetSlots = [] := by
  change ((Vector.replicate maxStackSize (.junk : StackSlot)).toList.take maxStackSize).length = maxStackSize ∧
    (Vector.replicate maxStackSize (.junk : StackSlot)).toList.take 0 = []
  simp only [List.take_zero, List.length_take, Vector.length_toList, Nat.min_self, and_self]
EOF
lean_file "$tmp/PlannerSizeFields.lean"

cat > "$tmp/AssemblyReview.lean" <<'EOF'
module
import Theorems.PlannerAssembly

open ShufflerVerification in
example {assumptions : PlannerInput → Prop}
    {postcondition : PlannerInput → PlannerExecutionResult → Prop}
    (flatPostcondition : ∀ input locals, assumptions input →
      postcondition input (input.execute locals)) :
    PlannerAssemblyContract assumptions postcondition :=
  planner_assembly_satisfies_model_contract flatPostcondition
EOF
lean_file "$tmp/AssemblyReview.lean"

cat > "$tmp/NormalReturn.lean" <<'EOF'
module
import all Theorems.PlannerAssembly
import all FlatShuffler.Unit.Lowest.Defs

open FlatShuffler FlatShuffler.Unit in
example {f : Flat.St → Flat.Status × Flat.St} {before after : Sep.G} {returned : MachineData}
    (result : NormalResult f before after returned) : al returned ≠ ASSERTION_FAILED :=
  result.2

open FlatShuffler FlatShuffler.Unit in
example {planned : Vector Word maxStackSize} {before after : Sep.G} {entry returned : MachineData}
    (result : permuteQ planned before after entry returned) : al returned ≠ ASSERTION_FAILED :=
  result.2

open FlatShuffler FlatShuffler.Unit in
example {before after : Sep.G} {entry returned : MachineData}
    (result : loopQ before after entry returned) : al returned ≠ ASSERTION_FAILED :=
  result.2

open FlatShuffler FlatShuffler.Unit in
example {planned : Vector Word maxStackSize} {before after : Sep.G} {entry returned : MachineData}
    (result : lowestQ planned before after entry returned) : al returned ≠ ASSERTION_FAILED := by
  obtain ⟨_, normalReturn⟩ := result
  exact normalReturn.2

open ShufflerVerification FlatShuffler FlatShuffler.Unit in
example {comparison : PlannerInput → PlannerExecutionResult → Prop}
    {address : Addr} {before : PlannerCallMemory} {frame : MProp 64}
    {entry returned : MachineData}
    (normalReturn : PlannerNormalReturn comparison address before frame entry returned) :
    al returned ≠ 2#8 := by
  obtain ⟨after, _, _, _, locals, returnByte, statusIsNormal, _⟩ := normalReturn
  intro forbiddenByte
  apply statusIsNormal
  have codeIsAssertion := returnByte.symm.trans forbiddenByte
  cases status : ((plannerInputAtEntry before entry).execute locals).1 <;>
    simp_all [code, DONE, BLOCKED, ASSERTION_FAILED]
EOF
lean_file "$tmp/NormalReturn.lean"

cat > "$tmp/ValidInputs.lean" <<'EOF'
module
import all Theorems.PlannerModel

open ShufflerVerification Shuffler

example (source target : Stack) (spills : SpillSet)
    (spillingAllowed : Bool) (strategy : BuildMapping.WildcardSlotsStrategy)
    (availableTargets : ∀ value ∈ target,
      value.is_junk ∨ value.can_be_freely_generated ∨ value ∈ source ∨ spills.is_spilled value)
    (enoughReturnLabels :
      target.count .FunctionReturnLabel ≤ source.count .FunctionReturnLabel) :
    ∃ result, Shuffler.Planner.run source target spills spillingAllowed strategy = .ok result ∧
      ∀ plan, result.result = some plan → StackMatches plan.stack target :=
  planner_model_correct source target spills spillingAllowed strategy
    availableTargets enoughReturnLabels

example (input : PlannerInput) (state : FlatShuffler.Flat.PSt) :
    PlannerReturnsCorrectPlanOrBlocked input (.blocked, state) := Or.inl rfl

-- An assertion exit cannot satisfy the correctness claim.
example (input : PlannerInput) (execution : PlannerExecutionResult)
    (failed : execution.1 = .assertionFailed) :
    ¬ PlannerReturnsCorrectPlanOrBlocked input execution := by
  intro correct
  rcases correct with blocked | ⟨done, _⟩
  · cases failed.symm.trans blocked
  · cases failed.symm.trans done

-- A Done result with the wrong target stack cannot satisfy the correctness claim.
example (input : PlannerInput) (execution : PlannerExecutionResult)
    (done : execution.1 = .done)
    (mismatch : ¬ StackMatches
      ((execution.2.data.toList.take input.targetStack.length).map
        ShufflerBridge.Emission.decodeStackSlot) input.targetStack) :
    ¬ PlannerReturnsCorrectPlanOrBlocked input execution := by
  intro correct
  rcases correct with blocked | ⟨_, stack, matchesTarget, trace, outputStack, _⟩
  · cases done.symm.trans blocked
  · exact mismatch (outputStack ▸ matchesTarget)

-- A target value that cannot be generated, copied, or loaded is not a valid input.
example (input : PlannerInput) (value : Value)
    (inTarget : value ∈ input.targetStack)
    (notJunk : ¬ value.is_junk)
    (notGenerated : ¬ value.can_be_freely_generated)
    (notInSource : value ∉ input.sourceStack)
    (notSpilled : ¬ (input.spillsFromBytes input.initialState.spills).is_spilled value) :
    ¬ PlannerInputsValidForNormalReturn input := by
  intro validInput
  rcases validInput.2.1 value inTarget with junk | generated | source | spilled
  · exact notJunk junk
  · exact notGenerated generated
  · exact notInSource source
  · exact notSpilled spilled

-- Return labels cannot be copied to fill extra target positions.
example (input : PlannerInput)
    (excessLabels : input.sourceStack.count .FunctionReturnLabel <
      input.targetStack.count .FunctionReturnLabel) :
    ¬ PlannerInputsValidForNormalReturn input := fun validInput =>
  Nat.not_le_of_lt excessLabels validInput.2.2
EOF
lean_file "$tmp/ValidInputs.lean"

cat > "$tmp/Mixed.lean" <<'EOF'
module
import all Theorems.PlannerAssembly
import all Theorems.PlannerModel
EOF
if lean_file "$tmp/Mixed.lean" > "$tmp/mixed.out" 2>&1; then
  echo 'modules_test: mixed implementation imports passed' >&2
  exit 1
fi
if ! grep -q "already contains 'List.allSome'" "$tmp/mixed.out"; then
  cat "$tmp/mixed.out" >&2
  exit 1
fi

cat > "$tmp/Legacy.lean" <<'EOF'
import Theorems.Main
EOF
if lean_file "$tmp/Legacy.lean" > "$tmp/legacy.out" 2>&1; then
  echo 'modules_test: legacy import passed' >&2
  exit 1
fi
if ! grep -q "already contains 'List.allSome'" "$tmp/legacy.out"; then
  cat "$tmp/legacy.out" >&2
  exit 1
fi

echo 'modules_test: public composition passes; mixed and legacy imports are rejected'
