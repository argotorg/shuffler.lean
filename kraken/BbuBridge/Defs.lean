import Shuffler.BuildBottomUp.Theorems
import BbuKraken.ModelLemmas
import BbuBridge.Permute

/-!
The link between the model `Bbu.buildBottomUp` and the original
`Shuffler.Emission.buildBottomUp`: the decoding of the model inputs, the initial
original state, the relation between the states, and the encoding of the
results.

The original target is `e.target.map decode`, and the original spill set is
`spillSet e`. A model state `st` and an original state are related (`Rel`) if
they have the same stack (after `decode`), the same destination for each slot,
the same `pending` and the same operations (after `encodeOp`).
-/

namespace BbuBridge

open Shuffler Shuffler.Emission

/-! ## Values -/

-- The value of a word: 0 is a wildcard, 1 a function return label, 2 + 2 id a
-- variable and 3 + 2 id a literal.
def decode (w : Bbu.Word) : Value :=
  if w.toNat = 0 then .Wildcard
  else if w.toNat = 1 then .FunctionReturnLabel
  else if w.toNat % 2 = 0 then .Var ⟨(w.toNat - 2) / 2⟩
  else .Lit (Fin.ofNat _ ((w.toNat - 3) / 2))

def number : Value → Nat
  | .Wildcard => 0
  | .FunctionReturnLabel => 1
  | .Var id => 2 + 2 * id.val
  | .Lit w => 3 + 2 * w.val

def encode (v : Value) : Bbu.Word := BitVec.ofNat 64 (number v)

theorem encode_decode (w : Bbu.Word) : encode (decode w) = w := by
  have hw := w.isLt
  apply BitVec.eq_of_toNat_eq
  simp only [encode, BitVec.toNat_ofNat]
  unfold decode
  split_ifs with h0 h1 h2
  · simp [number, h0]
  · simp [number, h1]
  · simp only [number]; omega
  · simp only [number, Fin.val_ofNat]
    rw [Nat.mod_eq_of_lt (a := (w.toNat - 3) / 2) (by omega)]
    omega

theorem decode_injective : Function.Injective decode := fun a b h => by
  rw [← encode_decode a, ← encode_decode b, h]

-- The spilled variables: the ids of all words (below 2 ^ 63) with a nonzero byte.
def spillSet (e : Bbu.Env) : SpillSet :=
  ((Finset.range (2 ^ 63)).filter (fun i => e.spills i ≠ 0)).image VarId.mk

-- The original target.
abbrev tgt (e : Bbu.Env) : Stack := e.target.map decode

-- An original state for the model environment `e`.
abbrev OState (e : Bbu.Env) (source : Stack) := State source (tgt e) (spillSet e)

/-! ## Operations and results -/

-- The model operation of a trace operation. A load is a push of the variable.
-- `buildBottomUp` never pops.
def encodeOp : TraceOp → Bbu.Op
  | .swap d => .swap d
  | .dup d => .dup d
  | .push v => .push (encode v)
  | .load id => .push (encode (.Var id))
  | .pop => ⟨3, 0⟩

def encodeErr : ShuffleErr → Bbu.Err
  | .Blocked b => .blocked b.offset b.excess
  | .assertion _ => .assertion

-- A result of the original as a model result.
def encodeM {α β : Type} (f : α → β) : Except ShuffleErr α → Bbu.M β
  | .ok a => .ok (f a)
  | .error err => .error (encodeErr err)

-- The operations of a result of `buildBottomUp`.
def encodeRes {spills : SpillSet} {source : Stack} :
    Except ShuffleErr ((res : Stack) × Trace spills source res) → Bbu.M (List Bbu.Op) :=
  encodeM fun r => (traceOps r.2).map encodeOp

-- A model result and an original result agree: related values, or the same error.
def Corr {α β : Type} (R : α → β → Prop) : Bbu.M α → Except ShuffleErr β → Prop
  | .ok a, .ok b => R a b
  | .error err, .error err' => err = encodeErr err'
  | _, _ => False

/-! ## The precondition -/

-- A target value can be pushed, loaded or DUPed from the source.
def Available (e : Bbu.Env) (source : List Bbu.Word) (v : Bbu.Word) : Prop :=
  Bbu.isFree v = true ∨ Bbu.isSpilled e v = true ∨ v ∈ source

-- The precondition of the model. `TopPre` gives the first three fields; the
-- original also needs that each target value is available (`State.Valid`).
structure ModelValid (e : Bbu.Env) (source : List Bbu.Word) (dests : List Nat) : Prop where
  length : dests.length = source.length
  le : source.length ≤ e.n
  dests : Bbu.Dests e.n dests
  available : ∀ v ∈ e.target, Available e source v

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
def initState (e : Bbu.Env) (source : List Bbu.Word) (dests : List Nat)
    (h : ModelValid e source dests) : OState e (source.map decode) :=
  let mapping : Mapping (source.map decode).length (tgt e).length :=
    ofDests dests (by simp [h.length]) (by simpa [tgt, Bbu.Env.n] using h.dests)
  { planned_mapping := mapping
    stack := source.map decode
    trace := .Lit _
    mapping := mapping
    pending_generations := e.n - source.length }

-- The initial model state, as in `Bbu.buildBottomUp`.
def initSt (e : Bbu.Env) (source : List Bbu.Word) (dests : List Nat) : Bbu.St :=
  ⟨List.zipWith Bbu.Slot.mk source dests, e.n - source.length, []⟩

-- The stack that `buildBottomUp` builds: the source value bound for each
-- offset, or the target value. This is `State.expectedStack` of `initState`.
def expected (e : Bbu.Env) (source : List Bbu.Word) (dests : List Nat) : List Bbu.Word :=
  (List.range e.n).map fun d =>
    match dests.idxOf? d with
    | some i => source[i]!
    | none => e.target[d]!

-- The mapping connects only equal values.
def Mapped (e : Bbu.Env) (source : List Bbu.Word) (dests : List Nat) : Prop :=
  ∀ i (h : i < source.length) (hd : i < dests.length), e.target[dests[i]]? = some source[i]

/-! ## The relation -/

-- The model state `st` and the original state agree.
structure Rel {source : Stack} (e : Bbu.Env) (st : Bbu.St) (state : OState e source) : Prop where
  stack : state.stack = st.slots.map fun s => decode s.val
  dest : ∀ i : Fin state.stack.length, (state.mapping i).map Fin.val = some (st.dest i)
  pendingGenerations : state.pending_generations = st.pendingGenerations
  trace : (traceOps state.trace).map encodeOp = st.trace

/-! ## Parts of the original loop -/

-- The `urgentToDup` scan of `buildBottomUp.loop`.
def origUrgent {source target : Stack} {spills : SpillSet}
    (state : State source target spills) (targetOffset : Nat) : Except ShuffleErr (Option Nat) := do
  let mut urgentToDup := none
  for offset in [targetOffset : target.length] do
    if (state.positionOf (← index target.length offset)).isSome then
      continue
    let slot ← slotAt target offset
    if slot.is_junk ∨ slot.can_be_freely_generated ∨ spills.is_spilled slot then
      continue
    if let some sourceCopy := state.stack.shallowestCopyPosition slot then
      if ¬ state.stack.isDupReachable sourceCopy then
        throw (← state.blockDupUnreachable sourceCopy)
      if (state.depthOf sourceCopy) = MAX_DUP_DEPTH ∧ sourceCopy.val ≠ targetOffset ∧ urgentToDup.isNone then
        urgentToDup := some offset
  return urgentToDup

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
    Except ShuffleErr ((res : Stack) × Trace spills source res) := do
  let ⟨hlen⟩ ← requires (state.stack.length = target.length) "working stack does not match target size"
  let ⟨hbound⟩ ← requires (∀ i, (state.destinationOf i).isSome) "unmapped source slots"
  let ⟨res, trace⟩ ←
    Shuffler.Permute.permute spills state.stack (state.mapping.toPermutation hlen hbound)
  return ⟨res, state.trace.concat trace⟩

-- The check of `buildBottomUp` after the loop.
def post {spills : SpillSet} {source : Stack} (target : Stack)
    (x : Except ShuffleErr ((res : Stack) × Trace spills source res)) :
    Except ShuffleErr ((res : Stack) × Trace spills source res) := do
  let ⟨res, trace⟩ ← x
  _ ← requires (res.length = target.length) "stack and target sizes differ"
  return ⟨res, trace⟩

theorem buildBottomUp_eq_post {source target : Stack} {spills : SpillSet}
    (initial : State source target spills) (h : initial.Valid) :
    buildBottomUp initial h = post target (buildBottomUp.loop 0 initial) := rfl

-- The original computation `x` continues as the model step `r` says: with the
-- loop at the next offset and a related state, with the final permutation, or
-- with the same error.
def StepCorr {source : Stack} (e : Bbu.Env) (r : Bbu.M (Bbu.St × Bbu.Next)) (state : OState e source)
    (x : Except ShuffleErr ((res : Stack) × Trace (spillSet e) source res)) : Prop :=
  match r with
  | .ok (st', .next t') => ∃ state' : OState e source, Rel e st' state' ∧ x = buildBottomUp.loop t' state'
  | .ok (st', .finish) => Rel e st' state ∧ x = origFinish state
  | .error err => ∃ err', x = .error err' ∧ err = encodeErr err'

end BbuBridge
