import PermuteKraken.Model

/-!
A model of `Shuffler.Emission.buildBottomUp` without Mathlib. Each definition
mirrors a function of `c/build_bottom_up.c`, and so the parts of the Lean
original.

A `StackSlot` and an `Op` have the fields of `StackSlot` and `struct op` in the
C, which have the layout of the C++ `StackSlot` and `ShuffleOp`. The padding is
not part of the model; `BbuKraken.Layout` gives the bytes of the fields. A slot
of the working stack (`Slot`) is a `StackSlot` and the target offset that it is
bound for: the C keeps these in `m_data` and `m_destinationOf`. The original
allows slots that are bound for no offset; `buildBottomUp` starts with every
slot bound, so the model does not represent them. `St.positionOf` is
`m_positionOf`: the position of the slot bound for each target offset.
-/

namespace Bbu

abbrev Word := BitVec 64

def MAX_SWAP_DEPTH : Nat := 16
def MAX_DUP_DEPTH : Nat := 15
-- The bound on `n` in `c/build_bottom_up.c`: the EVM stack limit.
def MAX_N : Nat := 1024

-- `StackSlot::Kind`
def Value : BitVec 8 := 0
def Junk : BitVec 8 := 1
def FunctionCallReturnLabel : BitVec 8 := 2
def FunctionReturnLabel : BitVec 8 := 3

-- The `InstOpcode`s that the C reads or writes.
def Const : BitVec 8 := 0
def Unreachable : BitVec 8 := 5

-- `StackSlot`
structure StackSlot where
  payload : BitVec 32
  kind : BitVec 8
  valueOpcode : BitVec 8
  deriving DecidableEq, Repr, Inhabited

-- `StackSlot::makeJunk`
def StackSlot.junk : StackSlot := ⟨0, Junk, Unreachable⟩

-- `ShuffleOp::Kind`
def Swap : BitVec 8 := 0
def Dup : BitVec 8 := 1
def Push : BitVec 8 := 3
def Load : BitVec 8 := 4

-- `struct op`: a swap or dup with its depth and a junk slot, or a push or load
-- with depth 0 and its slot.
structure Op where
  kind : BitVec 8
  depth : BitVec 8
  slot : StackSlot
  deriving DecidableEq, Repr

-- `record`
def Op.swap (depth : Nat) : Op := ⟨Swap, .ofNat 8 depth, .junk⟩
def Op.dup (depth : Nat) : Op := ⟨Dup, .ofNat 8 depth, .junk⟩

-- The inputs that do not change: `spills id` is not zero if variable `id` is spilled.
structure Env where
  target : List StackSlot
  spills : Nat → UInt8

def Env.n (e : Env) : Nat := e.target.length

structure Slot where
  val : StackSlot
  dest : Nat
  deriving DecidableEq, Repr

structure St where
  slots : List Slot
  positionOf : List (Option Nat)
  pendingGenerations : Nat
  trace : List Op
  deriving DecidableEq, Repr

def St.len (st : St) : Nat := st.slots.length
def St.val (st : St) (i : Nat) : StackSlot := (st.slots[i]?.map Slot.val).getD default
def St.dest (st : St) (i : Nat) : Nat := (st.slots[i]?.map Slot.dest).getD 0

inductive Err where
  -- The slot at `pos` is out of reach by `excess` slots.
  | blocked (pos excess : Nat)
  | assertion
  deriving DecidableEq, Repr

abbrev M := Except Err

-- The next target offset of the loop, or the final permutation.
inductive Next where
  | next (targetOffset : Nat)
  | finish
  deriving DecidableEq, Repr

/-! ## Queries -/

-- `StackSlot::isJunk`
def isJunk (slot : StackSlot) : Bool := slot.kind == Junk

-- `StackSlot::isLiteralValue`
def isLiteralValue (slot : StackSlot) : Bool := slot.valueOpcode == Const

-- `canBeFreelyGenerated`
def canBeFreelyGenerated (slot : StackSlot) : Bool :=
  isLiteralValue slot || slot.kind == Junk || slot.kind == FunctionCallReturnLabel

-- `isSpilled`
def isSpilled (e : Env) (slot : StackSlot) : Bool :=
  slot.kind == Value && !isLiteralValue slot && e.spills slot.payload.toNat != 0

-- `recordPush`: a pushed non-literal value can only be a spill reload.
def Op.push (slot : StackSlot) : Op :=
  ⟨if slot.kind == Value && !isLiteralValue slot then Load else Push, 0, slot⟩

-- `Mapping.positionOf`: the position of the slot bound for `destination`.
def positionOf (st : St) (destination : Nat) : Option Nat :=
  (st.positionOf[destination]?).join

-- `Stack.shallowestCopyPosition`: the last position that holds `slot`.
def shallowestCopyPosition (st : St) (slot : StackSlot) : Option Nat :=
  (List.range st.len).reverse.find? (st.val · == slot)

/-! ## Actions -/

-- `Mapping.swapDestinations`: the slots at `a` and `b` exchange their
-- destinations, and `m_positionOf` follows.
def swapDestinations (st : St) (a b : Nat) : St :=
  let st := { st with
    slots := (st.slots.set a ⟨st.val a, st.dest b⟩).set b ⟨st.val b, st.dest a⟩ }
  { st with positionOf := (st.positionOf.set (st.dest a) (some a)).set (st.dest b) (some b) }

-- `push` and `dup`: `m_mapping.push(destination)` binds a new top slot
-- `slot`, with the operation `op`.
def add (st : St) (slot : StackSlot) (destination : Nat) (op : Op) : M St :=
  if (positionOf st destination).isSome then .error .assertion
  else .ok { st with
    slots := st.slots ++ [⟨slot, destination⟩]
    positionOf := st.positionOf.set destination (some st.len)
    trace := st.trace ++ [op] }

-- `swapWith`: the slots at `pos` and the top exchange, then their destinations,
-- so that the destinations travel along.
def swapWith (st : St) (pos : Nat) : M St :=
  if st.len ≤ pos ∨ st.dest pos = pos then .error .assertion
  else
    let top := st.len - 1
    let depth := top - pos
    if depth < 1 ∨ MAX_SWAP_DEPTH < depth then .error .assertion
    else .ok (swapDestinations { st with
      slots := (st.slots.set pos ⟨st.val top, st.dest pos⟩).set top ⟨st.val pos, st.dest top⟩
      trace := st.trace ++ [.swap depth] } pos top)

-- The push or dup of `produce`
def emit (e : Env) (st : St) (targetOffset : Nat) : M St :=
  let slot := e.target[targetOffset]!
  let copy := shallowestCopyPosition st slot
  if isJunk slot then add st slot targetOffset (.push slot)
  else match copy.filter (fun copy => st.len - 1 - copy ≤ MAX_DUP_DEPTH) with
    | some copy => add st slot targetOffset (.dup (st.len - copy))
    | none =>
      if canBeFreelyGenerated slot || isSpilled e slot then add st slot targetOffset (.push slot)
      else match copy with
        | some copy => .error (.blocked copy (st.len - 1 - copy - MAX_DUP_DEPTH))
        | none => .error .assertion

-- `produce`, for `targetOffset < n`
def produce (e : Env) (st : St) (targetOffset : Nat) : M St :=
  (emit e st targetOffset).bind fun st =>
  if positionOf st targetOffset ≠ some (st.len - 1) then .error .assertion
  else .ok { st with pendingGenerations := st.pendingGenerations - 1 }

-- `generate`
def generate (e : Env) (st : St) (targetOffset : Nat) : M St :=
  if e.n ≤ targetOffset then .error .assertion
  else
    (produce e st targetOffset).bind fun st =>
    if targetOffset + 1 < st.len ∧ st.dest targetOffset ≠ targetOffset then
      let top := st.len - 1
      if st.val targetOffset = st.val top then .ok (swapDestinations st targetOffset top)
      else if top - targetOffset ≤ MAX_SWAP_DEPTH then swapWith st targetOffset
      else .ok st
    else .ok st

-- The `urgentToDup` scan of `buildBottomUp` from `offset` on, with the result
-- `urgentToDup` so far, or `n` for none.
def urgentFrom (e : Env) (st : St) (targetOffset offset urgentToDup : Nat) : M Nat :=
  if offset < e.n then
    if (positionOf st offset).isSome then urgentFrom e st targetOffset (offset + 1) urgentToDup
    else
      let slot := e.target[offset]!
      if isJunk slot || canBeFreelyGenerated slot || isSpilled e slot then
        urgentFrom e st targetOffset (offset + 1) urgentToDup
      else match shallowestCopyPosition st slot with
        | none => urgentFrom e st targetOffset (offset + 1) urgentToDup
        | some sourceCopy =>
          let depth := st.len - 1 - sourceCopy
          if MAX_DUP_DEPTH < depth then .error (.blocked sourceCopy (depth - MAX_DUP_DEPTH))
          else urgentFrom e st targetOffset (offset + 1)
            (if depth = MAX_DUP_DEPTH ∧ sourceCopy ≠ targetOffset ∧ urgentToDup = e.n
              then offset
              else urgentToDup)
  else .ok urgentToDup
termination_by e.n - offset

-- `urgentToDup`: the first offset at or above `targetOffset` that is urgent, or
-- `n` if there is none.
def urgent (e : Env) (st : St) (targetOffset : Nat) : M Nat :=
  urgentFrom e st targetOffset targetOffset e.n

-- The shallowest copy of the slot at `sourceForTargetOffset` above it that is not final.
def movableCopy (st : St) (sourceForTargetOffset : Nat) : Option Nat :=
  ((List.range st.len).reverse.take (st.len - 1 - sourceForTargetOffset)).find?
    (fun candidate => st.val candidate == st.val sourceForTargetOffset
      && st.dest candidate != candidate)

-- The branch of `buildBottomUp` for the slot at `sourceForTargetOffset` that is
-- bound for `targetOffset`: the new state, and whether `targetOffset` is done.
def takeBound (st : St) (targetOffset sourceForTargetOffset : Nat) : M (St × Bool) :=
  if sourceForTargetOffset < targetOffset then .error .assertion
  else
    let pos := if st.val targetOffset = st.val sourceForTargetOffset then targetOffset
      else (movableCopy st sourceForTargetOffset).getD sourceForTargetOffset
    let st := swapDestinations st pos sourceForTargetOffset
    if pos = targetOffset then .ok (st, true)
    else if pos ≠ st.len - 1 then
      let depth := st.len - 1 - pos
      if MAX_SWAP_DEPTH < depth then .error (.blocked pos (depth - MAX_SWAP_DEPTH))
      else (swapWith st pos).map (·, false)
    else .ok (st, false)

-- The end of an iteration of `buildBottomUp`: swap the top down into `targetOffset`.
def placeTop (st : St) (targetOffset : Nat) : M (St × Next) :=
  if st.len ≤ targetOffset ∨ st.dest targetOffset = targetOffset then .error .assertion
  else if targetOffset ≠ st.len - 1 then
    let depth := st.len - 1 - targetOffset
    if MAX_SWAP_DEPTH < depth then .error (.blocked targetOffset (depth - MAX_SWAP_DEPTH))
    else (swapWith st targetOffset).map (·, .next (targetOffset + 1))
  else .ok (st, .next (targetOffset + 1))

-- One iteration of `buildBottomUp` at `targetOffset < n`. `st.len` is `sourceTop`.
def step (e : Env) (st : St) (targetOffset : Nat) : M (St × Next) :=
  if targetOffset < st.len ∧ st.dest targetOffset = targetOffset then
    .ok (st, .next (targetOffset + 1))
  else if st.pendingGenerations = 0 then .ok (st, .finish)
  else (urgent e st targetOffset).bind fun urgentToDup =>
    if urgentToDup ≠ e.n ∧ urgentToDup ≠ targetOffset ∧
        st.len < targetOffset + MAX_SWAP_DEPTH then
      (generate e st urgentToDup).map (·, .next targetOffset)
    else if urgentToDup = e.n ∧ targetOffset < st.len ∧ st.len < e.n ∧
        positionOf st st.len = none ∧ st.len < targetOffset + MAX_SWAP_DEPTH then
      (generate e st st.len).map (·, .next targetOffset)
    else match positionOf st targetOffset with
      | some sourceForTargetOffset =>
        (takeBound st targetOffset sourceForTargetOffset).bind fun (st, done) =>
        if done then .ok (st, .next (targetOffset + 1)) else placeTop st targetOffset
      | none => (generate e st targetOffset).bind fun st =>
        if targetOffset < st.len ∧ st.dest targetOffset = targetOffset then
          .ok (st, .next (targetOffset + 1))
        else placeTop st targetOffset

-- The destinations form a permutation.
def IsPerm (l : List Nat) : Prop :=
  (∀ i (h : i < l.length), l[i] < l.length) ∧
    ∀ i (hi : i < l.length) j (hj : j < l.length), l[i] = l[j] → i = j

instance (l : List Nat) : Decidable (IsPerm l) := by unfold IsPerm; infer_instance

-- A swap of `permuteDestinations`: the slots at `top - depth` and the top
-- exchange; the mapping does not change.
def swapTop (st : St) (depth : Nat) : St :=
  let top := st.len - 1
  { st with
    slots := (st.slots.set (top - depth) ⟨st.val top, st.dest (top - depth)⟩).set top
      ⟨st.val (top - depth), st.dest top⟩
    trace := st.trace ++ [.swap depth] }

-- `permuteDestinations`: the final permutation. `buildBottomUp` keeps the
-- destinations a permutation, so the assertion does not occur; the C code has
-- no such check.
def finish (st : St) : M St :=
  let ds := st.slots.map Slot.dest
  if h : IsPerm ds then
    match PermuteKraken.permute ⟨ds, h.1, fun i j hi hj => h.2 i hi j hj⟩ with
    | .ok swaps => .ok (swaps.foldl swapTop st)
    | .error b => .error (.blocked b.offset b.excess)
  else .error .assertion

/-! ## Termination -/

theorem bind_ok {α β : Type} {x : M α} {f : α → M β} {y : β} (h : x.bind f = .ok y) :
    ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x <;> simp_all [Except.bind]

theorem map_ok {α β : Type} {x : M α} {f : α → β} {y : β} (h : x.map f = .ok y) :
    ∃ a, x = .ok a ∧ f a = y := by
  cases x <;> simp_all [Except.map]

theorem add_pending {st st' : St} {slot : StackSlot} {destination : Nat} {op : Op}
    (h : add st slot destination op = .ok st') :
    st'.pendingGenerations = st.pendingGenerations := by
  unfold add at h
  split at h <;> cases h; rfl

theorem swapWith_pending {st st' : St} {pos : Nat} (h : swapWith st pos = .ok st') :
    st'.pendingGenerations = st.pendingGenerations := by
  unfold swapWith at h
  split at h
  · cases h
  · dsimp only at h; split at h <;> cases h; rfl

theorem emit_pending {e : Env} {st st' : St} {targetOffset : Nat}
    (h : emit e st targetOffset = .ok st') :
    st'.pendingGenerations = st.pendingGenerations := by
  unfold emit at h
  dsimp only at h
  repeat' split at h
  all_goals first | exact add_pending h | cases h

-- Generating a slot lowers `pendingGenerations` by one.
theorem produce_pending {e : Env} {st st' : St} {targetOffset : Nat}
    (h : produce e st targetOffset = .ok st') :
    st'.pendingGenerations = st.pendingGenerations - 1 := by
  obtain ⟨s, hs, h⟩ := bind_ok h
  split at h <;> cases h
  simp [emit_pending hs]

theorem generate_pending {e : Env} {st st' : St} {targetOffset : Nat}
    (h : generate e st targetOffset = .ok st') :
    st'.pendingGenerations = st.pendingGenerations - 1 := by
  unfold generate at h
  split at h
  · cases h
  · obtain ⟨s, hs, h⟩ := bind_ok h
    have := produce_pending hs
    dsimp only at h
    repeat' split at h
    all_goals first
      | (cases h; simpa [swapDestinations] using this)
      | (rw [swapWith_pending h, this])

theorem placeTop_next {st st' : St} {targetOffset : Nat} {nx : Next}
    (h : placeTop st targetOffset = .ok (st', nx)) :
    nx = .next (targetOffset + 1) := by
  unfold placeTop at h
  dsimp only at h
  repeat' split at h
  all_goals first | (cases h; rfl) | cases h | (obtain ⟨s, _, h⟩ := map_ok h; cases h; rfl)

-- Each iteration advances `targetOffset`, or generates a slot.
theorem step_progress {e : Env} {st st' : St} {targetOffset targetOffset' : Nat}
    (h : step e st targetOffset = .ok (st', .next targetOffset')) :
    targetOffset' = targetOffset + 1
      ∨ (targetOffset' = targetOffset ∧ st'.pendingGenerations < st.pendingGenerations) := by
  unfold step at h
  split at h
  · cases h; exact .inl rfl
  split at h
  · cases h
  rename_i hp
  obtain ⟨urgentToDup, _, h⟩ := bind_ok h
  split at h
  · obtain ⟨s, hs, h⟩ := map_ok h
    cases h
    exact .inr ⟨rfl, by rw [generate_pending hs]; omega⟩
  split at h
  · obtain ⟨s, hs, h⟩ := map_ok h
    cases h
    exact .inr ⟨rfl, by rw [generate_pending hs]; omega⟩
  split at h
  · obtain ⟨⟨s, done⟩, _, h⟩ := bind_ok h
    cases done
    · cases placeTop_next h; exact .inl rfl
    · cases h; exact .inl rfl
  · obtain ⟨s, _, h⟩ := bind_ok h
    split at h
    · cases h; exact .inl rfl
    · cases placeTop_next h; exact .inl rfl

-- The loop of `buildBottomUp` from `targetOffset`: the final state.
def loop (e : Env) (st : St) (targetOffset : Nat) : M St :=
  if targetOffset < e.n then
    match _h : step e st targetOffset with
    | .ok (st', .next targetOffset') => loop e st' targetOffset'
    | .ok (st', .finish) => if st'.len = e.n then finish st' else .error .assertion
    | .error err => .error err
  else if st.len = e.n then .ok st else .error .assertion
termination_by (e.n - targetOffset, st.pendingGenerations)
decreasing_by
  rcases step_progress _h with h' | ⟨h', hp⟩
  · exact Prod.Lex.left _ _ (by omega)
  · subst h'; exact Prod.Lex.right _ hp

-- The initial `m_positionOf`: `bind` of each source slot in order.
def initPositionOf (n : Nat) (dests : List Nat) : List (Option Nat) :=
  (List.range dests.length).foldl (fun p i => p.set dests[i]! (some i)) (List.replicate n none)

-- The initial state for the source stack with the destination of each slot.
def init (e : Env) (source : List StackSlot) (dests : List Nat) : St :=
  ⟨List.zipWith Slot.mk source dests, initPositionOf e.n dests, e.n - source.length, []⟩

-- `buildBottomUp` from the source stack with the destination of each slot: the
-- final state, whose slots are the result stack and whose trace is the operations.
def buildBottomUp (e : Env) (source : List StackSlot) (dests : List Nat) : M St :=
  loop e (init e source dests) 0

end Bbu
