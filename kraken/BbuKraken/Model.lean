import PermuteKraken.Model

/-!
A model of `Shuffler.Emission.buildBottomUp` without Mathlib. Each definition
mirrors a function of `c/build_bottom_up.c`, and so the parts of the Lean
original.

A value is a 64-bit word: 0 is a wildcard, 1 the function return label,
2 + 2 * i the variable with index i and 3 + 2 * i the literal with index i. A
slot of the working stack is a value and the target offset that it is bound
for. The original allows slots that are bound for no offset; `buildBottomUp`
starts with every slot bound, so the model does not represent them.
-/

namespace Bbu

abbrev Word := BitVec 64

def MAX_SWAP_DEPTH : Nat := 16
def MAX_DUP_DEPTH : Nat := 15
-- The bound on `n` in `c/build_bottom_up.c`: the EVM stack limit.
def MAX_N : Nat := 1024

-- An operation: `kind` is 0 for a swap, 1 for a dup and 2 for a push, `arg` the
-- depth of a swap or dup, or the value of a push.
structure Op where
  kind : Word
  arg : Word
  deriving DecidableEq, Repr

def Op.swap (depth : Nat) : Op := ⟨0, .ofNat 64 depth⟩
def Op.dup (depth : Nat) : Op := ⟨1, .ofNat 64 depth⟩
def Op.push (v : Word) : Op := ⟨2, v⟩

-- The inputs that do not change: `spills id` is not zero if variable `id` is spilled.
structure Env where
  target : List Word
  spills : Nat → UInt8

def Env.n (e : Env) : Nat := e.target.length

structure Slot where
  val : Word
  dest : Nat
  deriving DecidableEq, Repr

structure St where
  slots : List Slot
  pendingGenerations : Nat
  trace : List Op
  deriving DecidableEq, Repr

def St.len (st : St) : Nat := st.slots.length
def St.val (st : St) (i : Nat) : Word := (st.slots[i]?.map Slot.val).getD 0
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

def isFree (slot : Word) : Bool := slot == 0 || (slot.toNat % 2 == 1 && slot != 1)

def isSpilled (e : Env) (slot : Word) : Bool :=
  2 ≤ slot.toNat && slot.toNat % 2 == 0 && e.spills ((slot.toNat - 2) / 2) != 0

-- `Mapping.positionOf`: the position of the slot bound for `destination`.
def positionOf (st : St) (destination : Nat) : Option Nat :=
  st.slots.findIdx? (·.dest == destination)

-- `Stack.shallowestCopyPosition`: the last position that holds `slot`.
def shallowestCopyPosition (st : St) (slot : Word) : Option Nat :=
  (List.range st.len).reverse.find? (st.val · == slot)

/-! ## Actions -/

-- `Mapping.swapDestinations`
def swapDestinations (st : St) (a b : Nat) : St :=
  { st with slots := (st.slots.set a ⟨st.val a, st.dest b⟩).set b ⟨st.val b, st.dest a⟩ }

-- `push` and `dup`: add `slot` bound for `destination` on top, with the operation `op`.
def add (st : St) (slot : Word) (destination : Nat) (op : Op) : M St :=
  if (positionOf st destination).isSome then .error .assertion
  else .ok { st with slots := st.slots ++ [⟨slot, destination⟩], trace := st.trace ++ [op] }

-- `swapWith`
def swapWith (st : St) (pos : Nat) : M St :=
  if st.len ≤ pos ∨ st.dest pos = pos then .error .assertion
  else
    let top := st.len - 1
    let depth := top - pos
    if depth < 1 ∨ MAX_SWAP_DEPTH < depth then .error .assertion
    else .ok { st with
      slots := (st.slots.set pos ⟨st.val top, st.dest top⟩).set top ⟨st.val pos, st.dest pos⟩
      trace := st.trace ++ [.swap depth] }

-- The push or dup of `produce`
def emit (e : Env) (st : St) (targetOffset : Nat) : M St :=
  let slot := e.target[targetOffset]!
  let copy := shallowestCopyPosition st slot
  if slot = 0 then add st slot targetOffset (.push slot)
  else match copy.filter (fun copy => st.len - 1 - copy ≤ MAX_DUP_DEPTH) with
    | some copy => add st slot targetOffset (.dup (st.len - copy))
    | none =>
      if isFree slot || isSpilled e slot then add st slot targetOffset (.push slot)
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
      if isFree slot || isSpilled e slot then
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

-- The final permutation. `buildBottomUp` keeps the destinations a permutation,
-- so the assertion does not occur; the C code has no such check.
def finish (st : St) : M (List Op) :=
  let ds := st.slots.map Slot.dest
  if h : IsPerm ds then
    match PermuteKraken.permute ⟨ds, h.1, fun i j hi hj => h.2 i hi j hj⟩ with
    | .ok swaps => .ok (st.trace ++ swaps.map Op.swap)
    | .error b => .error (.blocked b.offset b.excess)
  else .error .assertion

/-! ## Termination -/

theorem bind_ok {α β : Type} {x : M α} {f : α → M β} {y : β} (h : x.bind f = .ok y) :
    ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x <;> simp_all [Except.bind]

theorem map_ok {α β : Type} {x : M α} {f : α → β} {y : β} (h : x.map f = .ok y) :
    ∃ a, x = .ok a ∧ f a = y := by
  cases x <;> simp_all [Except.map]

theorem add_pending {st st' : St} {slot : Word} {destination : Nat} {op : Op}
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

-- The loop of `buildBottomUp` from `targetOffset`.
def loop (e : Env) (st : St) (targetOffset : Nat) : M (List Op) :=
  if targetOffset < e.n then
    match _h : step e st targetOffset with
    | .ok (st', .next targetOffset') => loop e st' targetOffset'
    | .ok (st', .finish) => if st'.len = e.n then finish st' else .error .assertion
    | .error err => .error err
  else if st.len = e.n then .ok st.trace else .error .assertion
termination_by (e.n - targetOffset, st.pendingGenerations)
decreasing_by
  rcases step_progress _h with h' | ⟨h', hp⟩
  · exact Prod.Lex.left _ _ (by omega)
  · subst h'; exact Prod.Lex.right _ hp

-- `buildBottomUp` from the source stack with the destination of each slot.
def buildBottomUp (e : Env) (source : List Word) (dests : List Nat) : M (List Op) :=
  loop e ⟨List.zipWith Slot.mk source dests, e.n - source.length, []⟩ 0

end Bbu
