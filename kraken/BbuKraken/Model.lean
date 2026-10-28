import PermuteKraken.Model

/-!
A model of `Shuffler.Emission.buildBottomUp` without Mathlib. Each definition
mirrors a function of `c/build_bottom_up.c`, and so the parts of the Lean
original.

A value is a 64-bit word: 0 is a wildcard, 1 a function return label, 2 + 2 id
a variable and 3 + 2 id a literal. A slot of the working stack is a value and
the target offset that it is bound for. The original allows slots that are bound
for no offset; `buildBottomUp` starts with every slot bound, so the model does
not represent them.
-/

namespace Bbu

abbrev Word := BitVec 64

def MAX_SWAP_DEPTH : Nat := 16
def MAX_DUP_DEPTH : Nat := 15

-- An operation: `kind` is 0 for a swap, 1 for a dup and 2 for a push, `arg` the
-- depth of a swap or dup, or the value of a push.
structure Op where
  kind : Word
  arg : Word
  deriving DecidableEq, Repr

def Op.swap (depth : Nat) : Op := ⟨0, .ofNat 64 depth⟩
def Op.dup (depth : Nat) : Op := ⟨1, .ofNat 64 depth⟩
def Op.push (v : Word) : Op := ⟨2, v⟩

-- The inputs that do not change: `spilled[id]` is not zero if variable `id` is spilled.
structure Env where
  target : List Word
  spilled : Nat → UInt8

def Env.n (e : Env) : Nat := e.target.length

structure Slot where
  val : Word
  dest : Nat
  deriving DecidableEq, Repr

structure St where
  slots : List Slot
  pending : Nat
  ops : List Op
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

-- The next offset of the loop, or the final permutation.
inductive Next where
  | next (t : Nat)
  | finish
  deriving DecidableEq, Repr

/-! ## Queries -/

def isFree (v : Word) : Bool := v == 0 || (v.toNat % 2 == 1 && v != 1)

def isSpilled (e : Env) (v : Word) : Bool :=
  2 ≤ v.toNat && v.toNat % 2 == 0 && e.spilled ((v.toNat - 2) / 2) != 0

-- `State.positionOf`: the position of the slot bound for `d`.
def positionOf (st : St) (d : Nat) : Option Nat := st.slots.findIdx? (·.dest == d)

-- `Stack.shallowestCopyPosition`: the last position that holds `v`.
def shallowestCopy (st : St) (v : Word) : Option Nat :=
  (List.range st.len).reverse.find? (st.val · == v)

/-! ## Actions -/

-- `State.swapDestinations`
def swapDest (st : St) (a b : Nat) : St :=
  { st with slots := (st.slots.set a ⟨st.val a, st.dest b⟩).set b ⟨st.val b, st.dest a⟩ }

-- `State.push` and `State.dup`: add `v` bound for `d` on top, with the operation `op`.
def add (st : St) (v : Word) (d : Nat) (op : Op) : M St :=
  if (positionOf st d).isSome then .error .assertion
  else .ok { st with slots := st.slots ++ [⟨v, d⟩], ops := st.ops ++ [op] }

-- `State.swapWith`
def swapWith (st : St) (pos : Nat) : M St :=
  if st.len ≤ pos ∨ st.dest pos = pos then .error .assertion
  else
    let top := st.len - 1
    let depth := top - pos
    if depth < 1 ∨ MAX_SWAP_DEPTH < depth then .error .assertion
    else .ok { st with
      slots := (st.slots.set pos ⟨st.val top, st.dest top⟩).set top ⟨st.val pos, st.dest pos⟩
      ops := st.ops ++ [.swap depth] }

-- The push or dup of `State.produce`
def emit (e : Env) (st : St) (d : Nat) : M St :=
  let v := e.target[d]!
  let copy := shallowestCopy st v
  if v = 0 then add st v d (.push v)
  else match copy.filter (fun c => st.len - 1 - c ≤ MAX_DUP_DEPTH) with
    | some c => add st v d (.dup (st.len - c))
    | none =>
      if isFree v || isSpilled e v then add st v d (.push v)
      else match copy with
        | some c => .error (.blocked c (st.len - 1 - c - MAX_DUP_DEPTH))
        | none => .error .assertion

-- `State.produce`, for `d < n`
def produce (e : Env) (st : St) (d : Nat) : M St :=
  (emit e st d).bind fun st =>
  if positionOf st d ≠ some (st.len - 1) then .error .assertion
  else .ok { st with pending := st.pending - 1 }

-- `State.generate`
def generate (e : Env) (st : St) (d : Nat) : M St :=
  if e.n ≤ d then .error .assertion
  else
    (produce e st d).bind fun st =>
    if d + 1 < st.len ∧ st.dest d ≠ d then
      let top := st.len - 1
      if st.val d = st.val top then .ok (swapDest st d top)
      else if top - d ≤ MAX_SWAP_DEPTH then swapWith st d
      else .ok st
    else .ok st

-- The `urgentToDup` scan from offset `d` on, with the result `u` so far, or `n` for none.
def urgentFrom (e : Env) (st : St) (t d u : Nat) : M Nat :=
  if d < e.n then
    if (positionOf st d).isSome then urgentFrom e st t (d + 1) u
    else
      let v := e.target[d]!
      if isFree v || isSpilled e v then urgentFrom e st t (d + 1) u
      else match shallowestCopy st v with
        | none => urgentFrom e st t (d + 1) u
        | some c =>
          let depth := st.len - 1 - c
          if MAX_DUP_DEPTH < depth then .error (.blocked c (depth - MAX_DUP_DEPTH))
          else urgentFrom e st t (d + 1)
            (if depth = MAX_DUP_DEPTH ∧ c ≠ t ∧ u = e.n then d else u)
  else .ok u
termination_by e.n - d

-- The first offset at or above `t` that is urgent, or `n` if there is none.
def urgent (e : Env) (st : St) (t : Nat) : M Nat := urgentFrom e st t t e.n

-- The shallowest copy of the slot at `b` above `b` that is not final.
def movableCopy (st : St) (b : Nat) : Option Nat :=
  ((List.range st.len).reverse.take (st.len - 1 - b)).find?
    (fun c => st.val c == st.val b && st.dest c != c)

-- The branch of `buildBottomUp.loop` for the slot `b` bound for `t`: the new
-- state, and whether `t` is done.
def takeBound (st : St) (t b : Nat) : M (St × Bool) :=
  if b < t then .error .assertion
  else
    let pos := if st.val t = st.val b then t else (movableCopy st b).getD b
    let st := swapDest st pos b
    if pos = t then .ok (st, true)
    else if pos ≠ st.len - 1 then
      let depth := st.len - 1 - pos
      if MAX_SWAP_DEPTH < depth then .error (.blocked pos (depth - MAX_SWAP_DEPTH))
      else (swapWith st pos).map (·, false)
    else .ok (st, false)

-- The end of an iteration of `buildBottomUp.loop`: swap the top down into `t`.
def placeTop (st : St) (t : Nat) : M (St × Next) :=
  if st.len ≤ t ∨ st.dest t = t then .error .assertion
  else if t ≠ st.len - 1 then
    let depth := st.len - 1 - t
    if MAX_SWAP_DEPTH < depth then .error (.blocked t (depth - MAX_SWAP_DEPTH))
    else (swapWith st t).map (·, .next (t + 1))
  else .ok (st, .next (t + 1))

-- One iteration of `buildBottomUp.loop` at `t < n`.
def step (e : Env) (st : St) (t : Nat) : M (St × Next) :=
  if t < st.len ∧ st.dest t = t then .ok (st, .next (t + 1))
  else if st.pending = 0 then .ok (st, .finish)
  else (urgent e st t).bind fun u =>
    if u ≠ e.n ∧ u ≠ t ∧ st.len < t + MAX_SWAP_DEPTH then
      (generate e st u).map (·, .next t)
    else if u = e.n ∧ t < st.len ∧ st.len < e.n ∧ positionOf st st.len = none ∧
        st.len < t + MAX_SWAP_DEPTH then
      (generate e st st.len).map (·, .next t)
    else match positionOf st t with
      | some b => (takeBound st t b).bind fun (st, done) =>
        if done then .ok (st, .next (t + 1)) else placeTop st t
      | none => (generate e st t).bind fun st =>
        if t < st.len ∧ st.dest t = t then .ok (st, .next (t + 1)) else placeTop st t

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
    | .ok swaps => .ok (st.ops ++ swaps.map Op.swap)
    | .error b => .error (.blocked b.offset b.excess)
  else .error .assertion

/-! ## Termination -/

theorem bind_ok {α β : Type} {x : M α} {f : α → M β} {y : β} (h : x.bind f = .ok y) :
    ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x <;> simp_all [Except.bind]

theorem map_ok {α β : Type} {x : M α} {f : α → β} {y : β} (h : x.map f = .ok y) :
    ∃ a, x = .ok a ∧ f a = y := by
  cases x <;> simp_all [Except.map]

theorem add_pending {st st' : St} {v : Word} {d : Nat} {op : Op} (h : add st v d op = .ok st') :
    st'.pending = st.pending := by
  unfold add at h
  split at h <;> cases h; rfl

theorem swapWith_pending {st st' : St} {pos : Nat} (h : swapWith st pos = .ok st') :
    st'.pending = st.pending := by
  unfold swapWith at h
  split at h
  · cases h
  · dsimp only at h; split at h <;> cases h; rfl

theorem emit_pending {e : Env} {st st' : St} {d : Nat} (h : emit e st d = .ok st') :
    st'.pending = st.pending := by
  unfold emit at h
  dsimp only at h
  repeat' split at h
  all_goals first | exact add_pending h | cases h

-- Generating a slot lowers `pending` by one.
theorem produce_pending {e : Env} {st st' : St} {d : Nat} (h : produce e st d = .ok st') :
    st'.pending = st.pending - 1 := by
  obtain ⟨s, hs, h⟩ := bind_ok h
  split at h <;> cases h
  simp [emit_pending hs]

theorem generate_pending {e : Env} {st st' : St} {d : Nat} (h : generate e st d = .ok st') :
    st'.pending = st.pending - 1 := by
  unfold generate at h
  split at h
  · cases h
  · obtain ⟨s, hs, h⟩ := bind_ok h
    have := produce_pending hs
    dsimp only at h
    repeat' split at h
    all_goals first | (cases h; simpa [swapDest] using this) | (rw [swapWith_pending h, this])

theorem placeTop_next {st st' : St} {t : Nat} {nx : Next} (h : placeTop st t = .ok (st', nx)) :
    nx = .next (t + 1) := by
  unfold placeTop at h
  dsimp only at h
  repeat' split at h
  all_goals first | (cases h; rfl) | cases h | (obtain ⟨s, _, h⟩ := map_ok h; cases h; rfl)

-- Each iteration advances `t`, or generates a slot.
theorem step_progress {e : Env} {st st' : St} {t t' : Nat} (h : step e st t = .ok (st', .next t')) :
    t' = t + 1 ∨ (t' = t ∧ st'.pending < st.pending) := by
  unfold step at h
  split at h
  · cases h; exact .inl rfl
  split at h
  · cases h
  rename_i hp
  obtain ⟨u, _, h⟩ := bind_ok h
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

-- `buildBottomUp.loop` from offset `t`.
def loop (e : Env) (st : St) (t : Nat) : M (List Op) :=
  if t < e.n then
    match _h : step e st t with
    | .ok (st', .next t') => loop e st' t'
    | .ok (st', .finish) => if st'.len = e.n then finish st' else .error .assertion
    | .error err => .error err
  else if st.len = e.n then .ok st.ops else .error .assertion
termination_by (e.n - t, st.pending)
decreasing_by
  rcases step_progress _h with h' | ⟨h', hp⟩
  · exact Prod.Lex.left _ _ (by omega)
  · subst h'; exact Prod.Lex.right _ hp

-- `buildBottomUp` from the source stack with the destination of each slot.
def buildBottomUp (e : Env) (source : List Word) (dests : List Nat) : M (List Op) :=
  loop e ⟨List.zipWith Slot.mk source dests, e.n - source.length, []⟩ 0

end Bbu
