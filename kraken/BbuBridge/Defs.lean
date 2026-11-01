module

public import Shuffler.BuildBottomUp.Theorems
import all Shuffler.BuildBottomUp.Theorems
public import Shuffler.Emission.Lemmas
import all Shuffler.Emission.Lemmas
public import BbuKraken.ModelLemmas
import all BbuKraken.ModelLemmas

@[expose] public section

/-!
The link between the model `Bbu.buildBottomUp` and the original
`Shuffler.Emission.buildBottomUp`: the decoding of the model inputs, the initial
original state, the relation between the states, and the relation between the
results.

The original target is `e.target.map decode`, and the original spill set is
`spillSet e source`. A model state `st` and an original state are related (`Rel`) if
they have the same stack (after `decode`), the same destination for each slot,
the same `pending` and the same operations (after `encodeOp`).

A model result and an original `Result` are related (`ResCorr`) if both are
done with related states, both are blocked at the same slot by the same excess
with related states, or both fail an assertion. The model returns a block as the
error `Err.blocked` with the state at the block.
-/

namespace BbuBridge

open Shuffler Shuffler.Emission

/-! ## Values -/

-- The number of a slot: the payload, the kind and the opcode.
def number (s : Bbu.StackSlot) : Nat :=
  s.payload.toNat + 2 ^ 32 * s.kind.toNat + 2 ^ 40 * s.valueOpcode.toNat

def ofNumber (n : Nat) : Bbu.StackSlot :=
  ⟨.ofNat 32 n, .ofNat 8 (n / 2 ^ 32), .ofNat 8 (n / 2 ^ 40)⟩

theorem number_lt (s : Bbu.StackSlot) : number s < 2 ^ 48 := by
  have := s.payload.isLt; have := s.kind.isLt; have := s.valueOpcode.isLt
  simp only [number]; omega

theorem ofNumber_number (s : Bbu.StackSlot) : ofNumber (number s) = s := by
  obtain ⟨p, k, o⟩ := s
  have := p.isLt; have := k.isLt; have := o.isLt
  simp only [ofNumber, number, Bbu.StackSlot.mk.injEq]
  refine ⟨?_, ?_, ?_⟩ <;> apply BitVec.eq_of_toNat_eq <;> simp only [BitVec.toNat_ofNat] <;> omega

-- The function return label slot of the harness.
def frl : Bbu.StackSlot := ⟨0, Bbu.FunctionReturnLabel, Bbu.Unreachable⟩

-- The value of a slot: a junk slot is a wildcard, a literal or a function call
-- return label is a literal, a function return label is a function return
-- label, and each other slot is a variable. The number of the slot is the
-- literal or the variable id.
def decode (s : Bbu.StackSlot) : Value :=
  if s.kind = Bbu.Junk then .Wildcard
  else if s.valueOpcode = Bbu.Const ∨ s.kind = Bbu.FunctionCallReturnLabel then
    .Lit (Fin.ofNat _ (number s))
  else if s.kind = Bbu.FunctionReturnLabel then .FunctionReturnLabel
  else .Var ⟨number s⟩

def encode : Value → Bbu.StackSlot
  | .Wildcard => .junk
  | .FunctionReturnLabel => frl
  | .Var id => ofNumber id.val
  | .Lit w => ofNumber w.val

-- The model compares slots and the original compares values, so a junk slot
-- must be `StackSlot.junk`, and a function return label must be `frl`.
def Canon (s : Bbu.StackSlot) : Prop :=
  (s.kind = Bbu.Junk → s = .junk) ∧ (s.kind = Bbu.FunctionReturnLabel → s = frl)

theorem canon_default : Canon default := by
  constructor <;> intro h <;> cases h

theorem encode_decode {s : Bbu.StackSlot} (h : Canon s) : encode (decode s) = s := by
  unfold decode
  split_ifs with h0 h1 h2
  · exact (h.1 h0).symm
  · simp only [encode, Fin.val_ofNat]
    rw [Nat.mod_eq_of_lt (by have := number_lt s; omega), ofNumber_number]
  · exact (h.2 h2).symm
  · exact ofNumber_number s

theorem decode_inj {a b : Bbu.StackSlot} (ha : Canon a) (hb : Canon b)
    (h : decode a = decode b) : a = b := by
  rw [← encode_decode ha, ← encode_decode hb, h]

-- The original target.
abbrev tgt (e : Bbu.Env) : Stack := e.target.map decode

-- The spilled variables: the ids of the variables of the source and the target that the model
-- takes as spilled. The model keys the spills by the payload only. If no two variables of the
-- source and the target have the same payload, a spill of a source variable in the model adds
-- exactly its id to this set, as `SpillSet.add` of the original.
def spillSet (e : Bbu.Env) (source : Stack) : SpillSet :=
  ((Finset.range (2 ^ 48)).filter (fun i => Bbu.isSpilled e (ofNumber i) = true ∧
    Value.Var ⟨i⟩ ∈ source ++ tgt e)).image VarId.mk

-- An original state for the model environment `e`.
abbrev OState (e : Bbu.Env) (source : Stack) := State source (tgt e) (spillSet e source)

-- An original result for the model environment `e`.
abbrev OResult (e : Bbu.Env) (source : Stack) := Result source (tgt e) (spillSet e source)

/-! ## Operations -/

-- One op of a trace.
inductive TraceOp where
  | swap (depth : Nat)
  | dup (depth : Nat)
  | pop
  | push (v : Value)
  | load (id : VarId)

-- The ops of a trace, in order of application.
def traceOps {spills : SpillSet} {source result : Stack} : Trace spills source result → List TraceOp
  | .Lit _ => []
  | .Swap idx _ _ _ t => traceOps t ++ [.swap idx]
  | .Dup idx _ _ _ _ t => traceOps t ++ [.dup idx]
  | .Pop _ t => traceOps t ++ [.pop]
  | .Push v _ t => traceOps t ++ [.push v]
  | .Load id _ t => traceOps t ++ [.load id]

theorem traceOps_concat {spills : SpillSet} {a b c : Stack} (t1 : Trace spills a b)
    (t2 : Trace spills b c) : traceOps (t1.concat t2) = traceOps t1 ++ traceOps t2 := by
  induction t2 <;> simp_all [Trace.concat, traceOps]

-- The model operation of a trace operation. A load is a push of the variable.
-- `buildBottomUp` never pops; a pop has an unused kind.
def encodeOp : TraceOp → Bbu.Op
  | .swap d => .swap d
  | .dup d => .dup d
  | .push v => .push (encode v)
  | .load id => .push (encode (.Var id))
  | .pop => ⟨2, 0, .junk⟩

/-! ## Results -/

-- A model result and an original result agree: related values, or both fail an
-- assertion. The original actions never block.
def Corr {α β : Type} (R : α → β → Prop) : Bbu.M α → Except ShuffleErr β → Prop
  | .ok a, .ok b => R a b
  | .error .assertion, .error (.assertion _) => True
  | _, _ => False

-- A model result and an original `Result` agree: both are done with related
-- states, both are blocked at the same slot by the same excess with related
-- states, or both fail an assertion.
def ResCorr {source target : Stack} {spills : SpillSet}
    (R : Bbu.St → State source target spills → Prop) :
    Bbu.M Bbu.St → Except ShuffleErr (Result source target spills) → Prop
  | .ok st, .ok r => r.blocked = none ∧ R st r.state
  | .error (.blocked pos excess st), .ok r => r.blocked = some ⟨pos, excess⟩ ∧ R st r.state
  | .error .assertion, .error (.assertion _) => True
  | _, _ => False

/-! ## The precondition -/

-- A target value can be pushed, loaded or DUPed from the source.
def Available (e : Bbu.Env) (source : List Bbu.StackSlot) (v : Bbu.StackSlot) : Prop :=
  Bbu.canBeFreelyGenerated v = true ∨ Bbu.isSpilled e v = true ∨ v ∈ source

-- The precondition of the model. `TopPre` gives the first three fields; the
-- original also needs that each target value is available and that a slot is
-- bound for each function return label of the target (`State.Valid`). The junk
-- slots and the function return labels of the inputs are canonical.
structure ModelValid (e : Bbu.Env) (source : List Bbu.StackSlot) (dests : List Nat) : Prop where
  length : dests.length = source.length
  le : source.length ≤ e.n
  labels : ∀ d (hd : d < e.target.length), e.target[d].kind = Bbu.FunctionReturnLabel → d ∈ dests
  dests : Bbu.Dests e.n dests
  available : ∀ v ∈ e.target, Available e source v
  canonSource : ∀ v ∈ source, Canon v
  canonTarget : ∀ v ∈ e.target, Canon v

/-! ## The initial state -/

-- The mapping that binds source position `i` to `ds[i]`.
def ofDests {m n : Nat} (ds : List Nat) (hl : ds.length = m) (hd : Bbu.Dests n ds) : Mapping m n where
  toFun i := some ⟨ds[i.val], hd.1 _ _⟩
  invFun j := (List.finRange m).find? fun i => ds[i.val] = j.val
  inv i j := by
    simp only [Option.some.injEq]
    constructor
    · intro h
      have := List.find?_some h
      simp only [decide_eq_true_eq] at this
      exact Fin.ext this
    · intro h
      have hs : ((List.finRange m).find? fun i => ds[i.val] = j.val).isSome := by
        rw [List.find?_isSome]
        exact ⟨i, List.mem_finRange i, by simp [← h]⟩
      obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp hs
      rw [hk]
      have := List.find?_some hk
      simp only [decide_eq_true_eq] at this
      congr 1
      exact Fin.ext (hd.2 _ _ _ _ (this.trans (by rw [← h])))

-- The original initial state of the model inputs.
def initState (e : Bbu.Env) (source : List Bbu.StackSlot) (dests : List Nat)
    (h : ModelValid e source dests) : OState e (source.map decode) :=
  let mapping : Mapping (source.map decode).length (tgt e).length :=
    ofDests dests (by simp [h.length]) (by simpa [tgt, Bbu.Env.n] using h.dests)
  { planned_mapping := mapping
    stack := source.map decode
    trace := .Lit _
    mapping := mapping
    pending_generations := e.n - source.length }

-- The stack that `buildBottomUp` builds: the source value bound for each
-- offset, or the target value. This is `State.expectedStack` of `initState`.
def expected (e : Bbu.Env) (source : List Bbu.StackSlot) (dests : List Nat) : List Bbu.StackSlot :=
  (List.range e.n).map fun d =>
    match dests.idxOf? d with
    | some i => source[i]!
    | none => e.target[d]!

-- The mapping connects only equal values.
def Mapped (e : Bbu.Env) (source : List Bbu.StackSlot) (dests : List Nat) : Prop :=
  ∀ i (h : i < source.length) (hd : i < dests.length), e.target[dests[i]]? = some source[i]

/-! ## The relation -/

-- The model state `st` and the original state agree. Also, `st.positionOf` is
-- the position of each destination, and the slots and the target are canonical.
-- `planned_mapping` does not change in `buildBottomUp`, and the model does not
-- keep it.
structure Rel {source : Stack} (e : Bbu.Env) (st : Bbu.St) (state : OState e source) : Prop where
  stack : state.stack = st.slots.map fun s => decode s.val
  dest : ∀ i : Fin state.stack.length, (state.mapping i).map Fin.val = some (st.dest i)
  pendingGenerations : state.pending_generations = st.pendingGenerations
  trace : (traceOps state.trace).map encodeOp = st.trace
  pos : Bbu.Pos e.n st
  canon : ∀ s ∈ st.slots, Canon s.val
  target : ∀ v ∈ e.target, Canon v

/-! ## Parts of the original loop -/

-- The `urgentToDup` scan of `buildBottomUp.loop`, followed by `rest`.
def origScan {source target : Stack} {spills : SpillSet}
    (state : State source target spills) (targetOffset : Nat)
    (rest : Option Nat → Except ShuffleErr (Result source target spills)) :
    Except ShuffleErr (Result source target spills) := do
  let mut urgentToDup := none
  for offset in [targetOffset : target.length] do
    if (state.mapping.positionOf (← index target.length offset)).isSome then
      continue
    let slot ← slotAt target offset
    if slot.is_junk ∨ slot.can_be_freely_generated ∨ spills.is_spilled slot then
      continue
    if let some sourceCopy := state.stack.shallowestCopyPosition slot then
      if ¬ state.stack.isDupReachable sourceCopy then
        return ← state.blockDupUnreachable sourceCopy
      if (state.depthOf sourceCopy) = MAX_DUP_DEPTH ∧ sourceCopy.val ≠ targetOffset ∧ urgentToDup.isNone then
        urgentToDup := some offset
  rest urgentToDup

-- The search of `buildBottomUp.loop` for a movable copy of the slot at `bound`.
def origCopyScan {source target : Stack} {spills : SpillSet}
    (state : State source target spills) (bound : Fin state.stack.length) : Except ShuffleErr Nat := do
  let mut pos := bound.val
  for candidate in (List.range state.stack.length).reverse.take (state.depthOf bound) do
    if (← slotAt state.stack candidate) = (← slotAt state.stack bound) ∧
        ¬ state.isFinal (← index state.stack.length candidate) then
      pos := candidate
      break
  return pos

-- The final permutation of `buildBottomUp.loop`.
def origFinish {source target : Stack} {spills : SpillSet} (state : State source target spills) :
    Except ShuffleErr (Result source target spills) := do
  let ⟨hlen⟩ ← requires (state.stack.length = target.length) "working stack does not match target size"
  let ⟨hbound⟩ ← requires (∀ i, (state.mapping.destinationOf i).isSome) "unmapped source slots"
  Shuffler.Permute.permute state (state.mapping.toPermutation hlen hbound)

-- The check of `buildBottomUp` after the loop.
def post {source target : Stack} {spills : SpillSet}
    (x : Except ShuffleErr (Result source target spills)) :
    Except ShuffleErr (Result source target spills) := do
  let result ← x
  if result.blocked.isSome then return result
  _ ← requires (result.state.stack.length = target.length) "stack and target sizes differ"
  return result

theorem buildBottomUp_eq_post {source target : Stack} {spills : SpillSet}
    (initial : State source target spills) (h : initial.Valid) :
    buildBottomUp initial h = post (buildBottomUp.loop 0 initial) := rfl

-- The original computation `x` continues as the model step `r` says: with the
-- loop at the next offset and a related state, with the final permutation,
-- blocked with a related state, or with an assertion.
def StepCorr {source : Stack} (e : Bbu.Env) (r : Bbu.M (Bbu.St × Bbu.Next)) (state : OState e source)
    (x : Except ShuffleErr (OResult e source)) : Prop :=
  match r with
  | .ok (st', .next t') => ∃ state' : OState e source, Rel e st' state' ∧ x = buildBottomUp.loop t' state'
  | .ok (st', .finish) => Rel e st' state ∧ x = origFinish state
  | .error (.blocked pos excess st') =>
    ∃ state' : OState e source, Rel e st' state' ∧ x = .ok ⟨some ⟨pos, excess⟩, state'⟩
  | .error .assertion => ∃ reason, x = .error (.assertion reason)

end BbuBridge
