module

public import FlatShuffler.Model
import all FlatShuffler.Model

@[expose] public section

/-!
A model of `c/shuffler/stack/Shuffler.cpp` whose state is the image of `class Emission`.
`Model.lean` is the list model. `FlatModelTest.lean` compares the two by evaluation;
there is no proof that they agree.

- `St` has one field for each member of `Emission`, with the C++ type:
  `std::size_t` and `StackOffset` are `Word`, `Optional<StackOffset>` is a `Word`
  with the niche `NONE`, and an array of `maxStackSize` elements is a
  `Vector _ maxStackSize`. The trace is the list of the operations that `m_trace` holds
  below `m_traceSize`.
- Each unit returns a `Status` and the state, also when it fails, as the C++ does.
- There is one function for each function of the C++, and its statements are in
  the order of the C++. A `yulAssert` returns `.assertionFailed`. `permuteMapping` holds
  statements of `buildBottomUp`: the loop that reads the destinations and the call of `permute`.
- A loop is a recursive function. The loop of `permute` has no bound in the C++, so
  the model gives it fuel (`permuteLoop`).

The C++ reads a member of `Emission` only after it writes it, or below the sizes
that the constructor gets. The arrays are `Vector`s, so a read or a write out of
bounds is total: `get` returns `default`, `put` changes nothing.
-/

namespace FlatShuffler.Flat

-- `enum class Status`
inductive Status where
  | done
  | blocked
  | assertionFailed
  deriving DecidableEq, Repr

-- `Niche<StackOffset>::value`: the empty `Optional<StackOffset>`.
def NONE : Word := -1

-- `maxSwapDepth` and `maxDupDepth`
def maxSwapDepth : Word := 16
def maxDupDepth : Word := 15

-- `a[i]` for an array of `maxStackSize` elements.
def get {α : Type} [Inhabited α] (v : Vector α maxStackSize) (i : Word) : α :=
  if h : i.toNat < maxStackSize then v[i.toNat] else default

-- `a[i] = x` for an array of `maxStackSize` elements.
def put {α : Type} (v : Vector α maxStackSize) (i : Word) (x : α) : Vector α maxStackSize :=
  v.setIfInBounds i.toNat x

-- The members of `Emission`, in the order of the C++.
structure St where
  target : Vector StackSlot maxStackSize  -- m_target[0 .. m_targetSize)
  targetSize : Word                -- m_targetSize
  spills : BitVec 32 → BitVec 8    -- m_spills
  data : Vector StackSlot maxStackSize    -- m_stack.m_data
  size : Word                      -- m_stack.m_size
  trace : List Op                  -- m_stack.m_trace[0 .. m_stack.m_traceSize)
  dest : Vector Word maxStackSize         -- m_mapping.m_destinationOf
  pos : Vector Word maxStackSize          -- m_mapping.m_positionOf
  pend : Word                      -- m_pendingGenerations
  blockedOffset : Word             -- m_blocked.offset
  blockedExcess : Word             -- m_blocked.excess

-- `ShuffleOp::swap` and `ShuffleOp::dup`: the cast of the depth to `std::uint8_t`.
def _root_.FlatShuffler.Op.swapW (depth : Word) : Op := ⟨Swap, depth.setWidth 8, .junk⟩
def _root_.FlatShuffler.Op.dupW (depth : Word) : Op := ⟨Dup, depth.setWidth 8, .junk⟩

/-! ## `Stack` -/

-- `Stack::swap(StackOffset)`
def stackSwap (st : St) (offset : Word) : St :=
  let slot := get st.data offset
  let data := put st.data offset (get st.data (st.size - 1))
  let data := put data (st.size - 1) slot
  { st with data, trace := st.trace ++ [Op.swapW (st.size - 1 - offset)] }

-- `Stack::push`. `Op.push` is a load for a non-literal value.
def stackPush (st : St) (slot : StackSlot) : St :=
  { st with data := put st.data st.size slot, size := st.size + 1,
            trace := st.trace ++ [.push slot] }

-- `Stack::dup`
def stackDup (st : St) (offset : Word) : St :=
  let st := { st with trace := st.trace ++ [Op.dupW (st.size - 1 - offset + 1)] }
  { st with data := put st.data st.size (get st.data offset), size := st.size + 1 }

/-! ## `Mapping` -/

-- `Mapping::bind`
def bind (st : St) (pos destination : Word) : St :=
  { st with dest := put st.dest pos destination, pos := put st.pos destination pos }

-- `Mapping::swapDestinations`
def swapDestinations (st : St) (a b : Word) : St :=
  let destinationOfA := get st.dest a
  let dest := put st.dest a (get st.dest b)
  let dest := put dest b destinationOfA
  let pos := if get dest a ≠ NONE then put st.pos (get dest a) a else st.pos
  let pos := if get dest b ≠ NONE then put pos (get dest b) b else pos
  { st with dest, pos }

/-! ## Queries -/

-- `isSpilled`
def isSpilled (st : St) (slot : StackSlot) : Bool :=
  slot.kind == Value && !isLiteralValue slot && st.spills slot.payload != 0

-- `isFinal`
def isFinal (st : St) (pos : Word) : Bool := get st.dest pos == pos

-- `depthOf`
def depthOf (st : St) (pos : Word) : Word := st.size - 1 - pos

-- `isSwapReachable` and `isDupReachable`
def isSwapReachable (st : St) (pos : Word) : Bool := depthOf st pos ≤ maxSwapDepth
def isDupReachable (st : St) (pos : Word) : Bool := depthOf st pos ≤ maxDupDepth

-- The loop of `shallowestCopyPosition` from `pos` down.
def copyBelow (st : St) (slot : StackSlot) (pos : Word) : Word :=
  if h : pos = 0 then NONE
  else if get st.data (pos - 1) = slot then pos - 1
  else copyBelow st slot (pos - 1)
termination_by pos.toNat
decreasing_by bv_omega

-- `shallowestCopyPosition`
def shallowestCopyPosition (st : St) (slot : StackSlot) : Word :=
  copyBelow st slot st.size

/-! ## Actions -/

-- `swapWith`
def swapWith (st : St) (pos : Word) : Status × St :=
  if ¬pos < st.size then (.assertionFailed, st)
  else if isFinal st pos then (.assertionFailed, st)
  else
    let depth := depthOf st pos
    if ¬(1 ≤ depth ∧ depth ≤ maxSwapDepth) then (.assertionFailed, st)
    else
      let st := stackSwap st pos
      (.done, swapDestinations st pos (st.size - 1))

-- `push`
def push (st : St) (slot : StackSlot) (destination : Word) : Status × St :=
  let st := stackPush st slot
  if get st.pos destination ≠ NONE then (.assertionFailed, st)
  else (.done, bind st (st.size - 1) destination)

-- `dup`, with the check of `Stack.h`'s `dup`.
def dup (st : St) (copy destination : Word) : Status × St :=
  if (get st.data copy).kind = FunctionReturnLabel then (.assertionFailed, st)
  else
    let st := stackDup st copy
    if get st.pos destination ≠ NONE then (.assertionFailed, st)
    else (.done, bind st (st.size - 1) destination)

-- `block`
def block (st : St) (position excess : Word) : Status × St :=
  if excess = 0 then (.assertionFailed, st)
  else (.blocked, { st with blockedOffset := position, blockedExcess := excess })

-- `blockSwapUnreachable` and `blockDupUnreachable`
def blockSwapUnreachable (st : St) (position : Word) : Status × St :=
  block st position (depthOf st position - maxSwapDepth)
def blockDupUnreachable (st : St) (position : Word) : Status × St :=
  block st position (depthOf st position - maxDupDepth)

-- `produce`
def produce (st : St) (targetOffset : Word) : Status × St :=
  let slot := get st.target targetOffset
  let copy := shallowestCopyPosition st slot
  let r :=
    if isJunk slot then push st slot targetOffset
    else if copy ≠ NONE ∧ isDupReachable st copy then dup st copy targetOffset
    else if canBeFreelyGenerated slot || isSpilled st slot then push st slot targetOffset
    else if copy ≠ NONE then blockDupUnreachable st copy
    else (.assertionFailed, st)
  if r.1 ≠ .done then r
  else
    let st := r.2
    if get st.pos targetOffset ≠ st.size - 1 then (.assertionFailed, st)
    else (.done, { st with pend := st.pend - 1 })

-- `generate`
def generate (st : St) (targetOffset : Word) : Status × St :=
  if ¬targetOffset < st.targetSize then (.assertionFailed, st)
  else
    let r := produce st targetOffset
    if r.1 ≠ .done then r
    else
      let st := r.2
      if targetOffset + 1 < st.size ∧ ¬isFinal st targetOffset then
        if get st.data targetOffset = get st.data (st.size - 1) then
          (.done, swapDestinations st targetOffset (st.size - 1))
        else if isSwapReachable st targetOffset then swapWith st targetOffset
        else (.done, st)
      else (.done, st)

/-! ## `permute`

The array `permutation` of `buildBottomUp` and the local array `desiredBy` of `permute` are
`Vector`s. The C++ writes each element below the size before it reads it, so their content at
the start does not matter: the model starts with `initial`. -/

-- The content of the local arrays at the start.
def initial : Vector Word maxStackSize := Vector.replicate maxStackSize 0

-- The measure of a loop `for (i = a; i < b; ++i)`.
theorem sub_succ_lt {a b : Word} (h : a < b) : (b - (a + 1)).toNat < (b - a).toNat := by
  bv_omega

-- The loop that reads the destinations into `permutation`, from `pos` on; none if a slot
-- has no destination.
def readDestinations (st : St) (pos : Word) (permutation : Vector Word maxStackSize) :
    Option (Vector Word maxStackSize) :=
  if h : pos < st.size then
    let destination := get st.dest pos
    if destination = NONE then none
    else readDestinations st (pos + 1) (put permutation pos destination)
  else some permutation
termination_by (st.size - pos).toNat
decreasing_by bv_omega

-- The loop that sets `desiredBy` to none, from `offset` on.
def clearDesired (st : St) (offset : Word) (desiredBy : Vector Word maxStackSize) : Vector Word maxStackSize :=
  if h : offset < st.size then clearDesired st (offset + 1) (put desiredBy offset NONE)
  else desiredBy
termination_by (st.size - offset).toNat
decreasing_by bv_omega

-- The loop that marks the desired offsets of the group of `leader`, whose slot is
-- `slot`, from `pos` up to `leader`.
def markDesired (st : St) (leader : Word) (hl : leader < st.size) (slot : StackSlot)
    (permutation : Vector Word maxStackSize) (pos : Word) (desiredBy : Vector Word maxStackSize) :
    Vector Word maxStackSize :=
  if h : pos ≤ leader then
    let desiredBy :=
      if get st.data pos = slot then put desiredBy (get permutation pos) leader else desiredBy
    markDesired st leader hl slot permutation (pos + 1) desiredBy
  else desiredBy
termination_by (leader + 1 - pos).toNat
decreasing_by bv_omega

-- The `vacant` loop: from `vacant` on, the first offset that the group of `leader`
-- desires and that does not hold `slot`, or the size.
def nextVacant (st : St) (leader : Word) (slot : StackSlot) (desiredBy : Vector Word maxStackSize)
    (vacant : Word) : Word :=
  if h : vacant < st.size ∧ ¬(get desiredBy vacant = leader ∧ ¬get st.data vacant = slot) then
    nextVacant st leader slot desiredBy (vacant + 1)
  else vacant
termination_by (st.size - vacant).toNat
decreasing_by bv_omega

-- The loop that gives each slot of the group of `leader` an offset in `permutation`, from
-- `pos` up to `leader`; none if no vacant offset is left.
def placeGroup (st : St) (leader : Word) (hl : leader < st.size) (slot : StackSlot)
    (desiredBy : Vector Word maxStackSize) (pos vacant : Word) (permutation : Vector Word maxStackSize) :
    Option (Vector Word maxStackSize) :=
  if h : pos ≤ leader then
    if ¬get st.data pos = slot then
      placeGroup st leader hl slot desiredBy (pos + 1) vacant permutation
    else if get desiredBy pos = leader then
      placeGroup st leader hl slot desiredBy (pos + 1) vacant (put permutation pos pos)
    else
      let vacant := nextVacant st leader slot desiredBy vacant
      if ¬vacant < st.size then none
      else placeGroup st leader hl slot desiredBy (pos + 1) (vacant + 1) (put permutation pos vacant)
  else some permutation
termination_by (leader + 1 - pos).toNat
decreasing_by all_goals bv_omega

-- The `leader` loop, from `leader` on; none if a group has no vacant offset left.
def regroup (st : St) (leader : Word) (permutation desiredBy : Vector Word maxStackSize) :
    Option (Vector Word maxStackSize) :=
  if h : leader < st.size then
    let slot := get st.data leader
    if shallowestCopyPosition st slot ≠ leader then regroup st (leader + 1) permutation desiredBy
    else
      let desiredBy := markDesired st leader h slot permutation 0 desiredBy
      match placeGroup st leader h slot desiredBy 0 0 permutation with
      | none => none
      | some permutation => regroup st (leader + 1) permutation desiredBy
  else some permutation
termination_by (st.size - leader).toNat
decreasing_by all_goals exact sub_succ_lt h

-- The `candidate` loop of `permute`: the shallowest offset below `candidate` whose slot is
-- misplaced, or `top`.
def misplacedBelow (permutation : Vector Word maxStackSize) (top candidate : Word) : Word :=
  if h : candidate = 0 then top
  else if get permutation (candidate - 1) ≠ candidate - 1 then candidate - 1
  else misplacedBelow permutation top (candidate - 1)
termination_by candidate.toNat
decreasing_by bv_omega

-- How an iteration of the loop of `permute` ends: the next state and `permutation`, or
-- `return`.
inductive PNext where
  | cont (st : St) (permutation : Vector Word maxStackSize)
  | ret (r : Status × St)

-- The end of an iteration of the loop of `permute`: the slot at `pos` and the top.
def exchange (st : St) (top : Word) (permutation : Vector Word maxStackSize) (pos : Word) : PNext :=
  let r : Except (Status × St) St :=
    if get st.data pos = get st.data (st.size - 1) then .ok (swapDestinations st pos top)
    else if !isSwapReachable st pos then .error (blockSwapUnreachable st pos)
    else .ok (swapDestinations (stackSwap st pos) pos top)
  match r with
  | .error r => .ret r
  | .ok st =>
    let desired := get permutation pos
    let permutation := put permutation pos (get permutation top)
    .cont st (put permutation top desired)

-- An iteration of the loop of `permute`.
def permuteStep (st : St) (top : Word) (permutation : Vector Word maxStackSize) : PNext :=
  let pos := get permutation top
  if pos = top then
    let pos := misplacedBelow permutation top top
    if pos = top then .ret (.done, st)
    else exchange st top permutation pos
  else exchange st top permutation pos

-- The loop of `permute`, for at most `fuel` iterations. If `permutation` is a permutation
-- of the offsets below the size, the loop ends after at most `2 * size - 1` iterations
-- (see the C++). Else the C++ loop can run forever, and the model fails when `fuel` is 0.
def permuteLoop (fuel : Nat) (st : St) (top : Word) (permutation : Vector Word maxStackSize) :
    Status × St :=
  match fuel with
  | 0 => (.assertionFailed, st)
  | fuel + 1 =>
    match permuteStep st top permutation with
    | .ret r => r
    | .cont st permutation => permuteLoop fuel st top permutation

-- `permute(_permutation)`: the slot at each offset `pos` goes to `permutation[pos]`. The C++
-- changes the caller's array in place; the caller does not read it after the call, so the model
-- does not return it.
def permute (st : St) (permutation : Vector Word maxStackSize) : Status × St :=
  if st.size = 0 then (.done, st)
  else
    let desiredBy := clearDesired st 0 initial
    match regroup st 0 permutation desiredBy with
    | none => (.assertionFailed, st)
    | some permutation =>
      let top := st.size - 1
      permuteLoop (2 * st.size.toNat) st top permutation

-- The end of `buildBottomUp` when no generation is pending: the loop that reads the
-- destinations into `permutation`, then `permute(permutation)`. The C++ has these statements
-- in `buildBottomUp`.
def permuteMapping (st : St) : Status × St :=
  match readDestinations st 0 initial with
  | none => (.assertionFailed, st)
  | some permutation => permute st permutation

/-! ## `buildBottomUp` -/

-- The `urgentToDup` loop from `offset` on, with the value of `urgentToDup` so far,
-- or the result of `blockDupUnreachable`.
def urgentFrom (st : St) (targetOffset offset urgentToDup : Word) : Except (Status × St) Word :=
  if h : offset < st.targetSize then
    if get st.pos offset ≠ NONE then urgentFrom st targetOffset (offset + 1) urgentToDup
    else
      let slot := get st.target offset
      if isJunk slot || canBeFreelyGenerated slot || isSpilled st slot then
        urgentFrom st targetOffset (offset + 1) urgentToDup
      else
        let sourceCopy := shallowestCopyPosition st slot
        if sourceCopy ≠ NONE then
          if !isDupReachable st sourceCopy then .error (blockDupUnreachable st sourceCopy)
          else urgentFrom st targetOffset (offset + 1)
            (if depthOf st sourceCopy = maxDupDepth ∧ sourceCopy ≠ targetOffset ∧ urgentToDup = NONE
              then offset else urgentToDup)
        else urgentFrom st targetOffset (offset + 1) urgentToDup
  else .ok urgentToDup
termination_by (st.targetSize - offset).toNat
decreasing_by all_goals bv_omega

-- The `candidate` loop: the shallowest copy of `slot` from `candidate` down to above
-- `source` that is not final, or `source`.
def candidateFrom (st : St) (slot : StackSlot) (source candidate : Word) : Word :=
  if h : candidate > source then
    if get st.data candidate = slot ∧ !isFinal st candidate then candidate
    else candidateFrom st slot source (candidate - 1)
  else source
termination_by candidate.toNat
decreasing_by bv_omega

-- How an iteration of the loop of `buildBottomUp` ends: `continue` with the value of
-- `targetOffset`, or `return`.
inductive Next where
  | cont (st : St) (targetOffset : Word)
  | ret (r : Status × St)

-- The end of an iteration: swap the top down into `targetOffset`.
def placeTop (st : St) (targetOffset : Word) : Next :=
  if ¬targetOffset < st.size then .ret (.assertionFailed, st)
  else if isFinal st targetOffset then .ret (.assertionFailed, st)
  else if targetOffset ≠ st.size - 1 then
    if !isSwapReachable st targetOffset then .ret (blockSwapUnreachable st targetOffset)
    else
      let r := swapWith st targetOffset
      if r.1 ≠ .done then .ret r else .cont r.2 targetOffset
  else .cont st targetOffset

-- The branch for an offset that a slot is bound for.
def bound (st : St) (targetOffset : Word) : Next :=
  let boundForTarget := get st.pos targetOffset
  if ¬(boundForTarget ≠ NONE ∧ boundForTarget ≥ targetOffset) then .ret (.assertionFailed, st)
  else
    let sourceForTargetOffset := boundForTarget
    let slot := get st.data sourceForTargetOffset
    let pos :=
      if get st.data targetOffset = slot then targetOffset
      else candidateFrom st slot sourceForTargetOffset (st.size - 1)
    if get st.data pos ≠ get st.data sourceForTargetOffset then .ret (.assertionFailed, st)
    else
      let st := swapDestinations st pos sourceForTargetOffset
      if pos = targetOffset then .cont st targetOffset
      else if pos ≠ st.size - 1 then
        if !isSwapReachable st pos then .ret (blockSwapUnreachable st pos)
        else
          let r := swapWith st pos
          if r.1 ≠ .done then .ret r else placeTop r.2 targetOffset
      else placeTop st targetOffset

-- An iteration of the loop of `buildBottomUp`, for `targetOffset < m_targetSize`.
def body (st : St) (targetOffset : Word) : Next :=
  if targetOffset < st.size ∧ isFinal st targetOffset then .cont st targetOffset
  else if st.pend = 0 then
    if st.size ≠ st.targetSize then .ret (.assertionFailed, st)
    else .ret (permuteMapping st)
  else match urgentFrom st targetOffset targetOffset NONE with
  | .error r => .ret r
  | .ok urgentToDup =>
    if urgentToDup ≠ NONE ∧ urgentToDup ≠ targetOffset ∧ st.size - targetOffset < maxSwapDepth then
      let r := generate st urgentToDup
      if r.1 ≠ .done then .ret r else .cont r.2 (targetOffset - 1)
    else
      let sourceTop := st.size
      if urgentToDup = NONE ∧ sourceTop > targetOffset ∧ sourceTop < st.targetSize ∧
          get st.pos sourceTop = NONE ∧ sourceTop - targetOffset < maxSwapDepth then
        let r := generate st sourceTop
        if r.1 ≠ .done then .ret r else .cont r.2 (targetOffset - 1)
      else if get st.pos targetOffset ≠ NONE then bound st targetOffset
      else
        let r := generate st targetOffset
        if r.1 ≠ .done then .ret r
        else
          let st := r.2
          if ¬targetOffset < st.size then .ret (.assertionFailed, st)
          else if isFinal st targetOffset then .cont st targetOffset
          else placeTop st targetOffset

/-! ## Termination -/

-- The units do not write `m_targetSize`, and only `produce` writes `m_pendingGenerations`.
private theorem ite_of_pos {α : Type} {c : Prop} [Decidable c] {a b : α} (h : c) :
    (if c then a else b) = a := by
  cases ‹Decidable c› with
  | isTrue _ => rfl
  | isFalse hn => exact absurd h hn

private theorem ite_of_neg {α : Type} {c : Prop} [Decidable c] {a b : α} (h : ¬c) :
    (if c then a else b) = b := by
  cases ‹Decidable c› with
  | isTrue hp => exact absurd hp h
  | isFalse _ => rfl

def Keep (st st' : St) : Prop := st'.targetSize = st.targetSize ∧ st'.pend = st.pend

theorem push_keep (st : St) (slot : StackSlot) (d : Word) : Keep st (push st slot d).2 := by
  unfold push; dsimp only; split <;> exact ⟨rfl, rfl⟩

theorem dup_keep (st : St) (copy d : Word) : Keep st (dup st copy d).2 := by
  unfold dup; dsimp only; repeat' split
  all_goals exact ⟨rfl, rfl⟩

theorem swapWith_keep (st : St) (pos : Word) : Keep st (swapWith st pos).2 := by
  unfold swapWith; dsimp only; repeat' split
  all_goals exact ⟨rfl, rfl⟩

theorem block_keep (st : St) (pos excess : Word) : Keep st (block st pos excess).2 := by
  unfold block; split <;> exact ⟨rfl, rfl⟩

-- The end of `produce`, after the status of the action is `r.1`.
theorem produce_tail {st : St} {t : Word} {r : Status × St} (hr : Keep st r.2)
    (h : (if r.1 ≠ .done then r
          else if get r.2.pos t ≠ r.2.size - 1 then (.assertionFailed, r.2)
          else (.done, { r.2 with pend := r.2.pend - 1 })).1 = .done) :
    (if r.1 ≠ .done then r
      else if get r.2.pos t ≠ r.2.size - 1 then (.assertionFailed, r.2)
      else (.done, { r.2 with pend := r.2.pend - 1 })).2.targetSize = st.targetSize ∧
    (if r.1 ≠ .done then r
      else if get r.2.pos t ≠ r.2.size - 1 then (.assertionFailed, r.2)
      else (.done, { r.2 with pend := r.2.pend - 1 })).2.pend = st.pend - 1 := by
  by_cases hs : r.1 = .done
  · rw [ite_of_neg (fun h' => h' hs)] at h ⊢
    by_cases hp : get r.2.pos t ≠ r.2.size - 1
    · rw [ite_of_pos hp] at h; cases h
    · rw [ite_of_neg hp]
      exact ⟨hr.1, congrArg (· - 1) hr.2⟩
  · rw [ite_of_pos hs] at h; exact absurd h hs

theorem produce_done {st : St} {t : Word} (h : (produce st t).1 = .done) :
    (produce st t).2.targetSize = st.targetSize ∧ (produce st t).2.pend = st.pend - 1 := by
  unfold produce at h ⊢
  refine produce_tail ?_ h
  repeat' split
  all_goals first
    | exact push_keep _ _ _
    | exact dup_keep _ _ _
    | exact block_keep _ _ _
    | exact ⟨rfl, rfl⟩

theorem generate_done {st : St} {t : Word} (h : (generate st t).1 = .done) :
    (generate st t).2.targetSize = st.targetSize ∧ (generate st t).2.pend = st.pend - 1 := by
  unfold generate at h ⊢
  by_cases h0 : ¬t < st.targetSize
  · rw [ite_of_pos h0] at h; cases h
  rw [ite_of_neg h0] at h ⊢
  by_cases h1 : (produce st t).1 = .done
  · have hp := produce_done h1
    rw [ite_of_neg (fun h' => h' h1)]
    dsimp only
    repeat' split
    all_goals first
      | exact hp
      | exact ⟨(swapWith_keep _ _).1.trans hp.1, (swapWith_keep _ _).2.trans hp.2⟩
  · rw [ite_of_pos h1] at h; exact absurd h h1

theorem placeTop_cont {st st' : St} {t t' : Word} (h : placeTop st t = .cont st' t') :
    st'.targetSize = st.targetSize ∧ t' = t := by
  unfold placeTop at h
  dsimp only at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | (cases h; exact ⟨rfl, rfl⟩)
    | (cases h; exact ⟨(swapWith_keep _ _).1, rfl⟩)

theorem bound_cont {st st' : St} {t t' : Word} (h : bound st t = .cont st' t') :
    st'.targetSize = st.targetSize ∧ t' = t := by
  unfold bound at h
  dsimp only at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | (cases h; exact ⟨rfl, rfl⟩)
    | (obtain ⟨h1, h2⟩ := placeTop_cont h; exact ⟨h1.trans (swapWith_keep _ _).1, h2⟩)
    | (obtain ⟨h1, h2⟩ := placeTop_cont h; exact ⟨h1, h2⟩)

-- Each iteration that continues keeps `targetOffset`, or generates a slot and
-- decrements `targetOffset`.
theorem body_cont {st st' : St} {t t' : Word} (h : body st t = .cont st' t') :
    st'.targetSize = st.targetSize ∧
      (t' = t ∨ (t' = t - 1 ∧ st'.pend.toNat < st.pend.toNat)) := by
  unfold body at h
  split at h
  · cases h; exact ⟨rfl, .inl rfl⟩
  split at h
  · split at h <;> cases h
  rename_i hp
  split at h
  · cases h
  try dsimp only at h
  split at h
  · split at h
    · cases h
    · cases h
      rename_i h1
      obtain ⟨g1, g2⟩ := generate_done (Decidable.not_not.mp h1)
      exact ⟨g1, .inr ⟨rfl, by rw [g2]; bv_omega⟩⟩
  split at h
  · split at h
    · cases h
    · cases h
      rename_i h1
      obtain ⟨g1, g2⟩ := generate_done (Decidable.not_not.mp h1)
      exact ⟨g1, .inr ⟨rfl, by rw [g2]; bv_omega⟩⟩
  split at h
  · exact ⟨(bound_cont h).1, .inl (bound_cont h).2⟩
  split at h
  · cases h
  rename_i h1
  obtain ⟨g1, -⟩ := generate_done (Decidable.not_not.mp h1)
  try dsimp only at h
  split at h
  · cases h
  split at h
  · cases h; exact ⟨g1, .inl rfl⟩
  · obtain ⟨k1, k2⟩ := placeTop_cont h
    exact ⟨k1.trans g1, .inl k2⟩

-- The loop of `buildBottomUp` from `targetOffset`.
def loop (st : St) (targetOffset : Word) : Status × St :=
  if targetOffset < st.targetSize then
    match h : body st targetOffset with
    | .ret r => r
    | .cont st' targetOffset' => loop st' (targetOffset' + 1)
  else if st.size ≠ st.targetSize then (.assertionFailed, st)
  else (.done, st)
termination_by ((st.targetSize - targetOffset).toNat, st.pend.toNat)
decreasing_by
  obtain ⟨hn, h' | ⟨h', hp⟩⟩ := body_cont h
  · subst h'
    rw [hn]
    exact Prod.Lex.left _ _ (by bv_omega)
  · subst h'
    rw [hn, BitVec.sub_add_cancel]
    exact Prod.Lex.right _ hp

-- `buildBottomUp`
def buildBottomUp (st : St) : Status × St := loop st 0

/-! ## The constructor and the entry -/

-- The members that the constructor does not initialize: their content before it.
structure Uninit where
  dest : Vector Word maxStackSize
  pos : Vector Word maxStackSize
  blockedOffset : Word
  blockedExcess : Word

-- The offsets below `k`.
def offsets (k : Word) : List Word := (List.range k.toNat).map (BitVec.ofNat 64)

-- The constructor of `Emission`, with the constructor of `Mapping`: `data` holds the
-- `m` slots of the source stack, and the source slot at `i` is bound for `dests[i]`.
def ctor (data : Vector StackSlot maxStackSize) (m : Word) (target : Vector StackSlot maxStackSize) (n : Word)
    (dests : Vector Word maxStackSize) (spills : BitVec 32 → BitVec 8) (u : Uninit) : St :=
  let st : St := { target, targetSize := n, spills, data, size := m, trace := [],
                   dest := u.dest, pos := u.pos, pend := 0,
                   blockedOffset := u.blockedOffset, blockedExcess := u.blockedExcess }
  let st := (offsets n).foldl (fun st d => { st with pos := put st.pos d NONE }) st
  let st := (offsets m).foldl (fun st p => bind st p (get dests p)) st
  (offsets n).foldl (fun st d => if get st.pos d = NONE then { st with pend := st.pend + 1 } else st) st

-- `build_bottom_up`: the result and the final state, whose `data` holds the stack
-- below `size`, `trace` the operations, and `blockedOffset` and `blockedExcess` the
-- words that it writes to `blocked` (0 and 0 if not blocked). `u` is the content of the
-- members that the constructor does not initialize.
def build_bottom_up (m n : Word) (data target : Vector StackSlot maxStackSize) (dest : Vector Word maxStackSize)
    (spilled : BitVec 32 → BitVec 8) (u : Uninit) : Word × Option St :=
  if m > n ∨ n > .ofNat 64 maxStackSize then (-2, none)
  else
    let r := buildBottomUp (ctor data m target n dest spilled u)
    match r.1 with
    | .done => (.ofNat 64 r.2.trace.length, some { r.2 with blockedOffset := 0, blockedExcess := 0 })
    | .blocked => (.ofNat 64 r.2.trace.length, some r.2)
    | .assertionFailed => (-2, some r.2)

end FlatShuffler.Flat
