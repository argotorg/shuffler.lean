module

public import FlatShuffler.FlatPopRel
import all FlatShuffler.FlatPopRel

@[expose] public section

/-!
Tests of `FlatPop.lean`, `MapModel.lean` and `FlatPopRel.lean`: `pop` on an empty stack, on a
bound top and on a top with no destination; `popLoop` up to the size and one more; the
constructor (the pending count, no write above the sizes); `ctorP` of `plan` is `ctor`, and a
destination at or above `n` (outside `ctorP_plan`) breaks it; the bounds of `emission_pop`;
and the agreement of the flat model and the list model on all pop cases with `m, n ≤ 3`.
`test/pop_diff.sh` compares `emission_pop` with the PR31 model and the asm on more cases.
-/

namespace FlatShuffler.Flat.PopTest

open FlatShuffler

/-! ## Inputs -/

def x : StackSlot := ⟨1, Value, Const⟩
def y : StackSlot := ⟨2, Value, Const⟩
def var (i : Nat) : StackSlot := ⟨.ofNat 32 i, Value, 1⟩

-- A buffer that holds `l` from offset 0, and `default` above it.
def vec {α : Type} [Inhabited α] (l : List α) : Vector α maxStackSize :=
  Vector.ofFn fun i => l[i.val]?.getD default

-- Content of memory that the C++ does not write before it reads it.
def junkWords (k : Nat) : Vector Word maxStackSize := Vector.ofFn fun i => .ofNat 64 (i.val * k + 5)
def u1 : Uninit := ⟨junkWords 7, junkWords 13, 77, 99⟩
def up1 : Mapping := ⟨junkWords 3, junkWords 11⟩

def words (l : List Nat) : List Word := l.map (BitVec.ofNat 64)

-- The `dest` argument of `emission_pop`: `NONE` for `none`.
def destWords (ds : List (Option Nat)) : Vector Word maxStackSize :=
  vec (ds.map fun | some d => .ofNat 64 d | none => NONE)

-- The state of the constructor, with the planned mapping of `emission_pop`.
def mk (source target : List StackSlot) (ds : List (Option Nat)) : St :=
  let m : Word := .ofNat 64 source.length
  let n : Word := .ofNat 64 target.length
  ctorP (vec source) m (vec target) n (plan up1 m n (destWords ds)) (fun _ => 0) u1

/-! ## Views -/

def below (k : Word) : List Word := (List.range k.toNat).map (BitVec.ofNat 64)

-- The members that the units write: the slots, the destinations, the positions, the pending
-- count and the trace.
def view (st : St) : List StackSlot × List Word × List Word × Word × List Op :=
  ((below st.size).map (get st.data), (below st.size).map (get st.dest),
    (below st.targetSize).map (get st.pos), st.pend, st.trace)

def viewR (r : EmissionOutcome × St) := (r.1, view r.2)

-- All members but `spills` are equal.
def same (a b : St) : Bool :=
  a.target == b.target && a.targetSize == b.targetSize && a.data == b.data && a.size == b.size &&
    a.trace == b.trace && a.dest == b.dest && a.pos == b.pos && a.pend == b.pend &&
    a.blockedOffset == b.blockedOffset && a.blockedExcess == b.blockedExcess

-- `M` has no `DecidableEq`.
def res : M Map.State → Err ⊕ Map.State
  | .error e => .inl e
  | .ok s => .inr s

/-! ## The constructor -/

-- Two slots bound for `1` and `0`: no offset is pending.
#guard view (mk [x, y] [y, x] [some 1, some 0]) = ([x, y], words [1, 0], words [1, 0], 0, [])
-- A slot with no destination, and a target offset with no position.
#guard view (mk [x, y] [x, y] [some 1, none]) = ([x, y], [1, NONE], [NONE, 0], 1, [])
#guard view (mk [] [] []) = ([], [], [], 0, [])
#guard view (mk [] [x, y] []) = ([], [], [NONE, NONE], 2, [])
#guard view (mk [x, y] [] [none, none]) = ([x, y], [NONE, NONE], [], 0, [])
-- The constructor writes no entry above the sizes, and not the blocked members.
#guard (mk [x] [x, y] [some 1]).dest[1] = u1.dest[1]
#guard (mk [x] [x, y] [some 1]).pos[2] = u1.pos[2]
#guard (mk [x] [x] [some 0]).blockedOffset = 77 ∧ (mk [x] [x] [some 0]).blockedExcess = 99
-- `plan` writes no entry above the sizes.
#guard (plan up1 1 2 (destWords [some 1])).dest[1] = up1.dest[1]
#guard (plan up1 1 2 (destWords [some 1])).pos[2] = up1.pos[2]

/-! ## `ctorP` of `plan` is `ctor` (`ctorP_plan`) -/

def viaPlan (m n : Nat) (ds : List (Option Nat)) : St :=
  ctorP (vec [x, y, x]) (.ofNat 64 m) (vec [y, x, y]) (.ofNat 64 n)
    (plan up1 (.ofNat 64 m) (.ofNat 64 n) (destWords ds)) (fun _ => 0) u1

def viaCtor (m n : Nat) (ds : List (Option Nat)) : St :=
  ctor (vec [x, y, x]) (.ofNat 64 m) (vec [y, x, y]) (.ofNat 64 n) (destWords ds) (fun _ => 0) u1

#guard same (viaPlan 3 3 [some 2, some 0, some 1]) (viaCtor 3 3 [some 2, some 0, some 1])
#guard same (viaPlan 3 3 [none, some 0, none]) (viaCtor 3 3 [none, some 0, none])
#guard same (viaPlan 0 0 []) (viaCtor 0 0 [])
-- Negative: a destination `2 ≥ n` (outside `hd`). `ctor` binds the target offset `2` and
-- `ctorP` does not copy it: `m_positionOf[2]` differs, the view does not.
#guard !same (viaPlan 1 2 [some 2]) (viaCtor 1 2 [some 2])
#guard (viaPlan 1 2 [some 2]).pos[2] = u1.pos[2] ∧ (viaCtor 1 2 [some 2]).pos[2] = 0
#guard view (viaPlan 1 2 [some 2]) = view (viaCtor 1 2 [some 2])

/-! ## `pop` -/

-- An empty stack: the assertion, and no change.
#guard viewR (pop (mk [] [x] [])) = (.assertionExit, view (mk [] [x] []))
#guard (pop (mk [] [x] [])).2.size = 0
-- A bound top: the target offset `0` loses its position. The pending count stays.
#guard viewR (pop (mk [x, y] [y, x] [some 1, some 0]))
  = (.done, [x], words [1], [NONE, 0], 0, [Op.pop])
-- A top with no destination: no position changes.
#guard viewR (pop (mk [x, y] [x] [some 0, none])) = (.done, [x], words [0], words [0], 0, [Op.pop])
-- `pop` does not write `m_destinationOf` and `m_stack.m_data`.
#guard (pop (mk [x, y] [y, x] [some 1, some 0])).2.dest = (mk [x, y] [y, x] [some 1, some 0]).dest
#guard (pop (mk [x, y] [y, x] [some 1, some 0])).2.data = (mk [x, y] [y, x] [some 1, some 0]).data
-- The destination of the top is read at `size - 1`, not at `size`.
#guard (pop (mk [x, y] [x, y] [some 0, none])).2.pos = (mk [x, y] [x, y] [some 0, none]).pos

/-! ## `popLoop` -/

def s3 : St := mk [x, y, var 4] [var 4, y, x] [some 2, some 1, some 0]

#guard viewR (popLoop s3 0) = (.done, view s3)
#guard viewR (popLoop s3 2) = (.done, [x], words [2], [NONE, NONE, 0], 0, [Op.pop, Op.pop])
#guard viewR (popLoop s3 3) = (.done, [], [], [NONE, NONE, NONE], 0, [Op.pop, Op.pop, Op.pop])
-- One more than the size: the fourth pop fails, after three pops.
#guard (popLoop s3 4).1 = .assertionExit
#guard (popLoop s3 4).2.trace.length = 3
#guard (popLoop s3 100).1 = .assertionExit

/-! ## `emission_pop` -/

def ep (m n count : Word) : Word × Option St :=
  emission_pop m n (vec [x, y, x]) (vec [y, x, y]) (destWords [some 1, none, some 0]) (fun _ => 0)
    count u1 up1

#guard (ep 3 3 2).1 = 2
#guard ((ep 3 3 2).2.map view) = some ([x], words [1], [NONE, 0, NONE], 1, [Op.pop, Op.pop])
#guard (ep 3 3 0).1 = 0
#guard (ep 3 3 3).1 = 3
-- A pop of an empty stack fails.
#guard (ep 3 3 4).1 = -2
#guard (ep 0 0 1).1 = -2
#guard (ep 0 0 0).1 = 0
-- The bounds: `m, n ≤ maxStackSize`, with no state.
#guard (ep (.ofNat 64 (maxStackSize + 1)) 3 0).1 = -2 ∧ (ep (.ofNat 64 (maxStackSize + 1)) 3 0).2.isNone
#guard (ep 3 (.ofNat 64 (maxStackSize + 1)) 0).1 = -2 ∧ (ep 3 (.ofNat 64 (maxStackSize + 1)) 0).2.isNone
#guard (ep (-1) 3 0).1 = -2
#guard (ep (.ofNat 64 maxStackSize) (.ofNat 64 maxStackSize) 1).1 = 1
#guard (ep (.ofNat 64 maxStackSize) 0 (.ofNat 64 maxStackSize)).1 = .ofNat 64 maxStackSize
#guard (ep (.ofNat 64 maxStackSize) 0 (.ofNat 64 (maxStackSize + 1))).1 = -2

/-! ## The list model -/

#guard Map.plan 2 3 [some 2, none] = ⟨[some 2, none], [none, none, some 0]⟩
#guard Map.plan 0 0 [] = ⟨[], []⟩
#guard (Map.State.init [x, y] (Map.plan 2 2 [some 1, some 0])).pend = 0
#guard (Map.State.init [x] (Map.plan 1 3 [some 1])).pend = 2
#guard res ((Map.State.init [x, y] (Map.plan 2 2 [some 1, some 0])).pops 1)
  = .inr ⟨Map.plan 2 2 [some 1, some 0], [x], [Op.pop], ⟨[some 1], [none, some 0]⟩, 0⟩
#guard res ((Map.State.init [x, y] (Map.plan 2 2 [some 1, none])).pops 1)
  = .inr ⟨Map.plan 2 2 [some 1, none], [x], [Op.pop], ⟨[some 1], [none, some 0]⟩, 1⟩
#guard res ((Map.State.init [x] (Map.plan 1 1 [none])).pops 2) = .inl .assertion
#guard res ((Map.State.init [] (Map.plan 0 0 [])).pops 0) = .inr (Map.State.init [] (Map.plan 0 0 []))

/-! ## The flat model and the list model agree (`ctorP_abs`, `plan_abs`, `popLoop_abs`) -/

-- Each partial injection of `m` stack offsets into `n` target offsets.
def injections : Nat → Nat → List (List (Option Nat))
  | 0, _ => [[]]
  | m + 1, n => (injections m n).flatMap fun ds =>
      (none :: ((List.range n).filter (fun d => !ds.contains (some d))).map some).map (ds ++ [·])

def source (m : Nat) : List StackSlot := (List.range m).map var

-- The pop cases with `m, n ≤ k` and `count ≤ m + 1`.
def cases (k : Nat) : List (Nat × Nat × List (Option Nat) × Nat) :=
  (List.range (k + 1)).flatMap fun m => (List.range (k + 1)).flatMap fun n =>
    (injections m n).flatMap fun ds => (List.range (m + 2)).map fun c => (m, n, ds, c)

-- The list model, and the list state of the flat model.
def listRun (m n : Nat) (ds : List (Option Nat)) (c : Nat) : M Map.State :=
  (Map.State.init (source m) (Map.plan m n ds)).pops c

def flatRun (m n : Nat) (ds : List (Option Nat)) (c : Nat) : M Map.State :=
  let st := mk (source m) ((List.range n).map var) ds
  absRes (Map.plan m n ds) (popLoop st c)

#guard (cases 3).length = 394
#guard (cases 3).all fun (m, n, ds, c) => res (listRun m n ds c) = res (flatRun m n ds c)
-- The cases that fail are the cases with `c = m + 1`.
#guard (cases 3).all fun (m, n, ds, c) => (res (listRun m n ds c)).isRight = decide (c ≤ m)
-- Negative: a pop that does not clear the position of the top differs on a bound top.
def popKeep (s : Map.State) : M Map.State :=
  if s.stack = [] then .error .assertion
  else .ok { s with stack := s.stack.dropLast, trace := s.trace ++ [Op.pop],
                    mapping := ⟨s.mapping.dest.dropLast, s.mapping.pos⟩ }
def init (m n : Nat) (ds : List (Option Nat)) : Map.State := Map.State.init (source m) (Map.plan m n ds)
#guard res (init 1 1 [some 0]).pop ≠ res (popKeep (init 1 1 [some 0]))
#guard res (init 1 1 [none]).pop = res (popKeep (init 1 1 [none]))

end FlatShuffler.Flat.PopTest
