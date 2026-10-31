import BbuKraken.FlatSurplus
import BbuKraken.FlatLowest
import BbuKraken.FlatSpill

/-!
The flat model of `MappingBuilder`, `Planner`, `Emission::isAvailable`, `Emission::run` and the
entry `plan` in `c/build_bottom_up.cpp`, as in `FlatModel.lean`: one function for each function of
the C++, with the statements in the order of the C++, a loop is a recursive function, and a
`yulAssert` returns `.assertionFailed`.

- An `Optional<StackOffset>` is a `Word` with the niche `NONE`, and an `Optional<Class>` a byte
  with the niche `0xff`.
- The buffer `m_dropped` is a `Vector (BitVec 8) MAX_N`, and the spill set the function of its
  bytes, as in `FlatSpill.lean`.
- The local arrays have no initial value. `RunU` is the content of the locals of one attempt of
  `Planner::run` before the attempt writes them; `run` gets one for each attempt.
-/

namespace Bbu.Flat

-- `Optional<Class>`: the classes 0 to 4, and the niche.
def NOCLASS : BitVec 8 := 0xff
def SPILL : BitVec 8 := 4

/-! ## `MappingBuilder` -/

-- The members of `MappingBuilder` that do not change. `take` is `m_wildcardSlotsStrategy == Take`.
structure Builder where
  source : Vector StackSlot MAX_N
  m : Word
  target : Vector StackSlot MAX_N
  n : Word
  dropped : Vector (BitVec 8) MAX_N
  take : Bool

-- `mappable`
def mappable (b : Builder) (M : Mapping) (p : Word) : Bool :=
  get b.dropped p == 0 && get M.dest p == NONE

-- `hasSourceAssigned`
def hasSourceAssigned (M : Mapping) (t : Word) : Bool := get M.pos t != NONE

-- `isWildcardTarget`
def isWildcardTarget (b : Builder) (t : Word) : Bool := isJunk (get b.target t)

-- `inWildcardSlot`
def inWildcardSlot (b : Builder) (p : Word) : Bool := decide (p < b.n) && isWildcardTarget b p

-- `absDiff`
def absDiff (a c : Word) : Word := if a > c then a - c else c - a

-- `commonSize`
def commonSize (b : Builder) : Word := if b.m < b.n then b.m else b.n

-- `MappingBuilder::map`
def mbMap (b : Builder) (M : Mapping) (p t : Word) : Status × Mapping :=
  if !mappable b M p then (.assertionFailed, M)
  else if get M.dest p ≠ NONE then (.assertionFailed, M)
  else if get M.pos t ≠ NONE then (.assertionFailed, M)
  else (.done, M.bind p t)

-- The loop of `closestCopy` from `i` on.
def closestFrom (b : Builder) (M : Mapping) (t : Word) (inW : Bool) (i best : Word) : Word :=
  if h : i < b.m then
    let best :=
      if get b.source i = get b.target t && mappable b M i && inWildcardSlot b i == inW then
        if best = NONE || absDiff i t ≤ absDiff best t then i else best
      else best
    closestFrom b M t inW (i + 1) best
  else best
termination_by (b.m - i).toNat
decreasing_by bv_omega

-- `closestCopy`
def closestCopy (b : Builder) (M : Mapping) (t : Word) (inW : Bool) : Word :=
  closestFrom b M t inW 0 NONE

-- The loop of `mapInPlace` from `j` on.
def inPlaceFrom (b : Builder) (M : Mapping) (j : Word) : Status × Mapping :=
  if h : j < commonSize b then
    if get b.source j = get b.target j && mappable b M j then
      let r := mbMap b M j j
      if r.1 ≠ .done then r else inPlaceFrom b r.2 (j + 1)
    else inPlaceFrom b M (j + 1)
  else (.done, M)
termination_by (commonSize b - j).toNat
decreasing_by all_goals bv_omega

-- `mapInPlace`
def mapInPlace (b : Builder) (M : Mapping) : Status × Mapping := inPlaceFrom b M 0

-- The loop of `mapClosestCopies` from `j` on.
def closestCopiesFrom (b : Builder) (M : Mapping) (j : Word) : Status × Mapping :=
  if h : j < b.n then
    if !hasSourceAssigned M j && !isWildcardTarget b j && closestCopy b M j false ≠ NONE then
      let r := mbMap b M (closestCopy b M j false) j
      if r.1 ≠ .done then r else closestCopiesFrom b r.2 (j + 1)
    else closestCopiesFrom b M (j + 1)
  else (.done, M)
termination_by (b.n - j).toNat
decreasing_by all_goals bv_omega

-- `mapClosestCopies`
def mapClosestCopies (b : Builder) (M : Mapping) : Status × Mapping := closestCopiesFrom b M 0

-- The loop of `mapWildcardSlotCopies` from `j` on, with `m_sawWildcardCopy`.
def wildcardFrom (b : Builder) (M : Mapping) (saw : Bool) (j : Word) : Status × Mapping × Bool :=
  if h : j < b.n then
    if !hasSourceAssigned M j && !isWildcardTarget b j && closestCopy b M j true ≠ NONE then
      let copy := closestCopy b M j true
      if (get b.target j).kind = FunctionReturnLabel then
        let r := mbMap b M copy j
        if r.1 ≠ .done then (r.1, r.2, saw) else wildcardFrom b r.2 saw (j + 1)
      else if b.take then
        let r := mbMap b M copy j
        if r.1 ≠ .done then (r.1, r.2, true) else wildcardFrom b r.2 true (j + 1)
      else wildcardFrom b M true (j + 1)
    else wildcardFrom b M saw (j + 1)
  else (.done, M, saw)
termination_by (b.n - j).toNat
decreasing_by all_goals bv_omega

-- `mapWildcardSlotCopies`
def mapWildcardSlotCopies (b : Builder) (M : Mapping) (saw : Bool) : Status × Mapping × Bool :=
  wildcardFrom b M saw 0

-- The loop of `keepWildcardSlots` from `j` on.
def keepFrom (b : Builder) (M : Mapping) (j : Word) : Status × Mapping :=
  if h : j < commonSize b then
    if isWildcardTarget b j && !hasSourceAssigned M j && mappable b M j then
      let r := mbMap b M j j
      if r.1 ≠ .done then r else keepFrom b r.2 (j + 1)
    else keepFrom b M (j + 1)
  else (.done, M)
termination_by (commonSize b - j).toNat
decreasing_by all_goals bv_omega

-- `keepWildcardSlots`
def keepWildcardSlots (b : Builder) (M : Mapping) : Status × Mapping := keepFrom b M 0

-- The inner loop of `absorbSurplus` from `o` on.
def absorbBest (b : Builder) (M : Mapping) (j o best : Word) : Word :=
  if h : o < b.m then
    let best := if mappable b M o && (best = NONE || absDiff o j < absDiff best j) then o else best
    absorbBest b M j (o + 1) best
  else best
termination_by (b.m - o).toNat
decreasing_by bv_omega

-- The outer loop of `absorbSurplus` from `j` on.
def absorbFrom (b : Builder) (M : Mapping) (j : Word) : Status × Mapping :=
  if h : j < b.n then
    if isWildcardTarget b j && !hasSourceAssigned M j && absorbBest b M j 0 NONE ≠ NONE then
      let r := mbMap b M (absorbBest b M j 0 NONE) j
      if r.1 ≠ .done then r else absorbFrom b r.2 (j + 1)
    else absorbFrom b M (j + 1)
  else (.done, M)
termination_by (b.n - j).toNat
decreasing_by all_goals bv_omega

-- `absorbSurplus`
def absorbSurplus (b : Builder) (M : Mapping) : Status × Mapping := absorbFrom b M 0

-- The five phases of `build_mapping` and `Planner::run` on the mapping `M`, with
-- `m_sawWildcardCopy = false`: the mapping and `sawWildcardCopy()`, or none if a phase fails.
def buildMapping (b : Builder) (M : Mapping) : Option (Mapping × Bool) :=
  let r := mapInPlace b M
  if r.1 ≠ .done then none else
  let r := mapClosestCopies b r.2
  if r.1 ≠ .done then none else
  let w := mapWildcardSlotCopies b r.2 false
  if w.1 ≠ .done then none else
  let r := keepWildcardSlots b w.2.1
  if r.1 ≠ .done then none else
  let r := absorbSurplus b r.2
  if r.1 ≠ .done then none else some (r.2, w.2.2)

/-! ## `Planner` -/

-- The members of `Planner` that do not change. `m_spills` and `m_dropped` point to buffers that
-- the planner writes: they are arguments.
structure Planner where
  source : Vector StackSlot MAX_N
  m : Word
  target : Vector StackSlot MAX_N
  n : Word
  allowed : Bool

-- `Planner::isRetained`
def isRetained (M : Mapping) (p : Word) : Bool := get M.dest p != NONE

-- The loop of `hasOtherRetainedCopy` from `o` on.
def otherFrom (pl : Planner) (M : Mapping) (dn : Vector (BitVec 8) MAX_N) (offset o : Word) :
    Bool :=
  if h : o < pl.m then
    if o ≠ offset && get pl.source o = get pl.source offset && isRetained M o && get dn o = 0 then
      true
    else otherFrom pl M dn offset (o + 1)
  else false
termination_by (pl.m - o).toNat
decreasing_by bv_omega

-- `hasOtherRetainedCopy`
def hasOtherRetainedCopy (pl : Planner) (M : Mapping) (dn : Vector (BitVec 8) MAX_N)
    (offset : Word) : Bool :=
  otherFrom pl M dn offset 0

-- The loop of `isDemanded` from `j` on.
def demandedFrom (pl : Planner) (slot : StackSlot) (j : Word) : Bool :=
  if h : j < pl.n then
    if !isJunk (get pl.target j) && get pl.target j = slot then true
    else demandedFrom pl slot (j + 1)
  else false
termination_by (pl.n - j).toNat
decreasing_by bv_omega

-- `isDemanded`
def isDemanded (pl : Planner) (slot : StackSlot) : Bool := demandedFrom pl slot 0

-- `classify`
def classify (pl : Planner) (sp : BitVec 32 → BitVec 8) (M : Mapping)
    (dn : Vector (BitVec 8) MAX_N) (offset : Word) : BitVec 8 :=
  let slot := get pl.source offset
  if slot.kind = FunctionReturnLabel then NOCLASS
  else
    let regenerable := isJunk slot || canBeFreelyGenerated slot || spillIsSpilled sp slot ||
      hasOtherRetainedCopy pl M dn offset
    if isJunk (get pl.target (get M.dest offset)) && (regenerable || !isDemanded pl slot) then 0
    else if canBeFreelyGenerated slot then 1
    else if spillIsSpilled sp slot then 2
    else if hasOtherRetainedCopy pl M dn offset then 3
    else if pl.allowed && isVariable slot then SPILL
    else NOCLASS

-- `enum class Resolution`
inductive Resolution where
  | dropped
  | stuck
  | assertionFailed
  deriving DecidableEq, Repr

-- The locals of `resolve`: their content before it writes them.
structure ResolveU where
  droppedNow : Vector (BitVec 8) MAX_N
  candidates : Vector Word MAX_N

-- The loop of `resolve` that zeroes `droppedNow` from `o` on.
def zeroFrom (m o : Word) (dn : Vector (BitVec 8) MAX_N) : Vector (BitVec 8) MAX_N :=
  if h : o < m then zeroFrom m (o + 1) (put dn o 0) else dn
termination_by (m - o).toNat
decreasing_by bv_omega

-- The loop of `resolve` that collects the candidates from `pos` on: the candidates and their
-- count, or none for the failed check.
def candidatesFrom (M current : Mapping) (currentSize pos : Word) (cand : Vector Word MAX_N)
    (count : Word) : Option (Vector Word MAX_N × Word) :=
  if h : pos < currentSize then
    let destination := get current.dest pos
    if destination ≠ NONE ∧ get M.pos destination ≠ NONE then
      let source := get M.pos destination
      if get M.dest source = NONE then none
      else candidatesFrom M current currentSize (pos + 1) (put cand count source) (count + 1)
    else candidatesFrom M current currentSize (pos + 1) cand count
  else some (cand, count)
termination_by (currentSize - pos).toNat
decreasing_by all_goals bv_omega

-- The inner loop of a pass of `resolve` from `i` on: `best` and `bestClass`.
def pickFrom (pl : Planner) (sp : BitVec 32 → BitVec 8) (M : Mapping)
    (dn : Vector (BitVec 8) MAX_N) (cand : Vector Word MAX_N) (count i best : Word)
    (bestClass : BitVec 8) : Word × BitVec 8 :=
  if h : i < count then
    let offset := get cand i
    if get dn offset ≠ 0 then pickFrom pl sp M dn cand count (i + 1) best bestClass
    else
      let cls := classify pl sp M dn offset
      if cls = NOCLASS then pickFrom pl sp M dn cand count (i + 1) best bestClass
      else if best = NONE || cls < bestClass ||
          (cls == bestClass && get M.dest offset > get M.dest best) then
        pickFrom pl sp M dn cand count (i + 1) offset cls
      else pickFrom pl sp M dn cand count (i + 1) best bestClass
  else (best, bestClass)
termination_by (count - i).toNat
decreasing_by all_goals bv_omega

-- The state that `resolve` changes: the spill set, `m_dropped` and `droppedNow`.
structure RState where
  spills : BitVec 32 → BitVec 8
  dropped : Vector (BitVec 8) MAX_N
  droppedNow : Vector (BitVec 8) MAX_N

-- The passes of `resolve` from `k` on.
def passFrom (pl : Planner) (M : Mapping) (cand : Vector Word MAX_N) (count excess k : Word)
    (s : RState) : Resolution × RState :=
  if h : k < excess then
    let r := pickFrom pl s.spills M s.droppedNow cand count 0 NONE 0
    let best := r.1
    if best = NONE then (.stuck, s)
    else
      let a := spillAdd s.spills (get pl.source best)
      if r.2 = SPILL ∧ a.1 ≠ .done then (.assertionFailed, s)
      else
        let spills := if r.2 = SPILL then a.2 else s.spills
        passFrom pl M cand count excess (k + 1)
          ⟨spills, put s.dropped best 1, put s.droppedNow best 1⟩
  else (.dropped, s)
termination_by (excess - k).toNat
decreasing_by bv_omega

-- `resolve`: `M` is the plan, `current` the working mapping of a stack of `currentSize` slots,
-- and the slot at `blockedOffset` is blocked by `excess` slots.
def resolve (pl : Planner) (sp : BitVec 32 → BitVec 8) (dropped : Vector (BitVec 8) MAX_N)
    (M : Mapping) (blockedOffset excess : Word) (current : Mapping) (currentSize : Word)
    (u : ResolveU) : Resolution × (BitVec 32 → BitVec 8) × Vector (BitVec 8) MAX_N :=
  let dn := zeroFrom pl.m 0 u.droppedNow
  match candidatesFrom M current currentSize (blockedOffset + 1) u.candidates 0 with
  | none => (.assertionFailed, sp, dropped)
  | some (cand, count) =>
    let r := passFrom pl M cand count excess 0 ⟨sp, dropped, dn⟩
    (r.1, r.2.spills, r.2.dropped)

/-! ## `Emission::run` -/

-- `Emission::isAvailable`
def isAvailable (st : St) (offset : Word) : Bool :=
  let slot := get st.target offset
  canBeFreelyGenerated slot || isSpilled st slot || shallowestCopyPosition st slot ≠ NONE

-- The loop of `run` that counts the unmapped target offsets from `o` on.
def unmappedFrom (st : St) (o count : Word) : Word :=
  if h : o < st.targetSize then
    unmappedFrom st (o + 1) (if get st.pos o = NONE then count + 1 else count)
  else count
termination_by (st.targetSize - o).toNat
decreasing_by bv_omega

-- The loop of `run` that checks `isAvailable` from `o` on.
def availableFrom (st : St) (o : Word) : Bool :=
  if h : o < st.targetSize then isAvailable st o && availableFrom st (o + 1) else true
termination_by (st.targetSize - o).toNat
decreasing_by bv_omega

-- The loop of `run` that checks the function return labels from `o` on.
def labelsFrom (st : St) (o : Word) : Bool :=
  if h : o < st.targetSize then
    ((get st.target o).kind ≠ FunctionReturnLabel || get st.pos o ≠ NONE) && labelsFrom st (o + 1)
  else true
termination_by (st.targetSize - o).toNat
decreasing_by bv_omega

-- `Emission::run`: `planned` is the `m_positionOf` array of the planned mapping, and `l` the
-- content of the local arrays of `permuteAtLowestHeight`.
def emissionRun (planned : Vector Word MAX_N) (l : Locals) (st : St) : Status × St :=
  let r := removeSurplus st
  if r.1 ≠ .done then r else
  let r := permuteAtLowestHeight planned l r.2
  if r.1 ≠ .done then r else
  let st := r.2
  if st.size + st.pend ≠ st.targetSize then (.assertionFailed, st)
  else if unmappedFrom st 0 0 ≠ st.pend then (.assertionFailed, st)
  else if !availableFrom st 0 then (.assertionFailed, st)
  else if !labelsFrom st 0 then (.assertionFailed, st)
  else buildBottomUp st

/-! ## `Planner::run` -/

-- The locals of an attempt of `Planner::run`: their content before the attempt writes them.
structure RunU where
  mapping : Mapping
  u : Uninit
  l : Locals
  r : ResolveU

-- The state that `Planner::run` changes: the spill set, `m_dropped`, `m_sawWildcardCopy`, and the
-- caller's buffers `_data` and `_sources`. `trace` is the content of `_ops` below the trace size
-- of the last attempt.
structure PSt where
  spills : BitVec 32 → BitVec 8
  dropped : Vector (BitVec 8) MAX_N
  saw : Bool
  data : Vector StackSlot MAX_N
  trace : List Op
  sources : Vector Word MAX_N

-- The loop of `contains` from `i` on.
def containsFrom (stack : Vector StackSlot MAX_N) (size : Word) (slot : StackSlot) (i : Word) :
    Bool :=
  if h : i < size then
    if get stack i = slot then true else containsFrom stack size slot (i + 1)
  else false
termination_by (size - i).toNat
decreasing_by bv_omega

-- The check of `Planner::run` for the target slots from `j` on.
def targetsFrom (pl : Planner) (sp : BitVec 32 → BitVec 8) (j : Word) : Bool :=
  if h : j < pl.n then
    let slot := get pl.target j
    (isJunk slot || canBeFreelyGenerated slot || containsFrom pl.source pl.m slot 0 ||
      spillIsSpilled sp slot) && targetsFrom pl sp (j + 1)
  else true
termination_by (pl.n - j).toNat
decreasing_by bv_omega

-- The loop of `run` that counts the dropped bytes from `i` on.
def droppedFrom (m : Word) (d : Vector (BitVec 8) MAX_N) (i count : Word) : Word :=
  if h : i < m then droppedFrom m d (i + 1) (if get d i ≠ 0 then count + 1 else count)
  else count
termination_by (m - i).toNat
decreasing_by bv_omega

theorem droppedFrom_le (m : Word) (d : Vector (BitVec 8) MAX_N) (i count : Word)
    (h : count.toNat + (m - i).toNat ≤ m.toNat) (hi : i ≤ m) :
    (droppedFrom m d i count).toNat ≤ m.toNat := by
  unfold droppedFrom
  split
  · apply droppedFrom_le
    · split <;> bv_omega
    · bv_omega
  · omega
termination_by (m - i).toNat
decreasing_by bv_omega

-- The number of dropped bytes below `m`.
def droppedCount (m : Word) (d : Vector (BitVec 8) MAX_N) : Word := droppedFrom m d 0 0

theorem droppedCount_le (m : Word) (d : Vector (BitVec 8) MAX_N) :
    (droppedCount m d).toNat ≤ m.toNat :=
  droppedFrom_le m d 0 0 (by simp) (by bv_omega)

theorem sub_lt_sub {m a b : Word} (ha : a.toNat ≤ m.toNat) (_hb : b.toNat ≤ m.toNat) (h : a > b) :
    (m - a).toNat < (m - b).toNat := by
  bv_omega

-- The loop of `run` that copies the source to `_data` from `i` on.
def copyFrom (pl : Planner) (i : Word) (data : Vector StackSlot MAX_N) : Vector StackSlot MAX_N :=
  if h : i < pl.m then copyFrom pl (i + 1) (put data i (get pl.source i)) else data
termination_by (pl.m - i).toNat
decreasing_by bv_omega

-- The loop of `run` that writes `_sources` from `j` on.
def sourcesFrom (n j : Word) (M : Mapping) (sources : Vector Word MAX_N) : Vector Word MAX_N :=
  if h : j < n then sourcesFrom n (j + 1) M (put sources j (get M.pos j)) else sources
termination_by (n - j).toNat
decreasing_by bv_omega

-- The `for (;;)` loop of `Planner::run`, with the content `us k` of the locals of attempt `k`.
-- Each attempt that does not return drops more slots, and at most `m` slots can be dropped.
def runLoop (pl : Planner) (take : Bool) (s : PSt) (us : Nat → RunU) : Status × PSt :=
  let M := (us 0).mapping.init pl.m pl.n
  match buildMapping ⟨pl.source, pl.m, pl.target, pl.n, s.dropped, take⟩ M with
  | none => (.assertionFailed, s)
  | some (M, saw) =>
    let s := { s with saw := s.saw || saw, data := copyFrom pl 0 s.data }
    let r := emissionRun M.pos (us 0).l (ctorP s.data pl.m pl.target pl.n M s.spills (us 0).u)
    let s := { s with data := r.2.data, trace := r.2.trace }
    if r.1 ≠ .blocked then
      if r.1 = .done then (r.1, { s with sources := sourcesFrom pl.n 0 M s.sources }) else (r.1, s)
    else
      let before := droppedCount pl.m s.dropped
      let q := resolve pl s.spills s.dropped M r.2.blockedOffset r.2.blockedExcess
        ⟨r.2.dest, r.2.pos⟩ r.2.size (us 0).r
      let s := { s with spills := q.2.1, dropped := q.2.2 }
      match q.1 with
      | .stuck => (.blocked, s)
      | .assertionFailed => (.assertionFailed, s)
      | .dropped =>
        if h : droppedCount pl.m s.dropped > before then runLoop pl take s fun k => us (k + 1)
        else (.assertionFailed, s)
termination_by (pl.m - droppedCount pl.m s.dropped).toNat
decreasing_by exact sub_lt_sub (droppedCount_le _ _) (droppedCount_le _ _) h

-- `Planner::run`
def plannerRun (pl : Planner) (take : Bool) (s : PSt) (us : Nat → RunU) : Status × PSt :=
  let s := { s with saw := false }
  if !targetsFrom pl s.spills 0 then (.assertionFailed, s)
  else runLoop pl take s us

/-! ## The entry -/

-- The entry `plan` (the name `plan` is the planned mapping of `FlatPop.lean`): the result and the
-- final state. `dropped`, `data` and `sources` are the content of the caller's buffers, and `us`
-- that of the locals of the attempts. The C++ writes `saw` for `.done` and `.blocked`, and `data`
-- below `n`, the operations of `trace` and `sources` below `n` for `.done`.
def planEntry (m n : Word) (source target : Vector StackSlot MAX_N) (spilled : BitVec 32 → BitVec 8)
    (idCount : Word) (allowed strategy : BitVec 8) (dropped : Vector (BitVec 8) MAX_N)
    (data : Vector StackSlot MAX_N) (sources : Vector Word MAX_N) (us : Nat → RunU) :
    Word × Option (Status × PSt) :=
  if m > .ofNat 64 MAX_N ∨ n > .ofNat 64 MAX_N ∨ allowed > 1 ∨ strategy > 1 then (-2, none)
  else if !((offsets m).all fun i => idOk idCount (get source i)) then (-2, none)
  else if !((offsets n).all fun j => idOk idCount (get target j)) then (-2, none)
  else
    let dropped := zeroFrom m 0 dropped
    let r := plannerRun ⟨source, m, target, n, allowed = 1⟩ (strategy = 1)
      ⟨spilled, dropped, false, data, [], sources⟩ us
    match r.1 with
    | .done => (.ofNat 64 r.2.trace.length, some r)
    | .blocked => (-1, some r)
    | .assertionFailed => (-2, some r)

end Bbu.Flat
