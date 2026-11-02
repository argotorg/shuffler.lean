module

public import FlatShuffler.Model
import all FlatShuffler.Model

@[expose] public section

/-!
A model of the stack and mapping operations of `c/shuffler/test_wrappers.cpp` with lists, in core Lean.
Both projects compile it: `FlatPop.lean` (Kraken) shows that the flat model is an instance of
it, and `ShufflerBridge/Emission/Pop.lean` (root) shows that it is an instance of the PR31 model
(`Shuffler.Mapping`, `Shuffler.Emission.State.pop`).

- A `Mapping` is the two arrays of the C++ `Mapping`: `dest[i]` is the target offset of the slot
  at `i`, and `pos[d]` is the position of the slot bound for the target offset `d`. `none` is
  the empty `Optional<StackOffset>`. `dest` has one entry for each slot of the stack, and `pos`
  one entry for each target offset.
- A `State` is the members of `Emission` that the operations read or write: the planned
  mapping, the stack, the trace, the working mapping and `m_pendingGenerations`.

`FlatSurplusRel.lean` (Kraken) and `ShufflerBridge/Emission/RemoveSurplus.lean` (root) relate
`State.removeSurplus` to `Flat.removeSurplus` and to `Shuffler.Emission.removeSurplus`.
-/

namespace FlatShuffler

-- `ShuffleOp::Kind::Pop`
def Pop : BitVec 8 := 2

-- `ShuffleOp::pop()`: a pop has depth 0 and a junk slot.
def Op.pop : Op := ⟨Pop, 0, .junk⟩

namespace Map

structure Mapping where
  dest : List (Option Nat)
  pos : List (Option Nat)
  deriving DecidableEq, Repr

-- `Mapping(sourceSize, targetSize)`: no binding.
def Mapping.empty (m n : Nat) : Mapping := ⟨List.replicate m none, List.replicate n none⟩

-- `Mapping::bind`
def Mapping.bind (M : Mapping) (p d : Nat) : Mapping :=
  ⟨M.dest.set p (some d), M.pos.set d (some p)⟩

-- `Mapping::pop` of the top: the stack loses its top, and the target offset of the top, if
-- any, loses its position.
def Mapping.pop (M : Mapping) : Mapping :=
  match M.dest.getLast? with
  | some (some d) => ⟨M.dest.dropLast, M.pos.set d none⟩
  | _ => ⟨M.dest.dropLast, M.pos⟩

-- `Mapping::bind` of the new top after `Stack::push` or `Stack::dup`.
def Mapping.push (M : Mapping) (d : Nat) : Mapping :=
  ⟨M.dest ++ [some d], M.pos.set d (some M.dest.length)⟩

-- The planned mapping of `emission_pop` and `build_bottom_up`: the slot at `p < m` is bound for
-- `ds[p]`, if it is not none.
def plan (m n : Nat) (ds : List (Option Nat)) : Mapping :=
  (List.range m).foldl
    (fun M p => match ds.getD p none with
      | some d => M.bind p d
      | none => M)
    (Mapping.empty m n)

structure State where
  planned : Mapping
  stack : List StackSlot
  trace : List Op
  mapping : Mapping
  pend : Nat
  deriving DecidableEq, Repr

-- The constructor of `Emission`: the working mapping is a copy of the planned mapping, and
-- `m_pendingGenerations` is the number of target offsets with no position.
def State.init (stack : List StackSlot) (planned : Mapping) : State :=
  ⟨planned, stack, [], planned, planned.pos.count none⟩

-- `Emission::pop`: `Stack::pop`, then `Mapping::pop`. It does not change
-- `m_pendingGenerations`.
def State.pop (s : State) : M State :=
  if s.stack = [] then .error .assertion
  else .ok { s with stack := s.stack.dropLast, trace := s.trace ++ [Op.pop],
                    mapping := s.mapping.pop }

-- `count` pops, up to the first that fails: the loop of `emission_pop`.
def State.pops (s : State) : Nat → M State
  | 0 => .ok s
  | count + 1 => s.pop.bind (·.pops count)

-- `Mapping::swapDestinations`: the slots at `a` and `b` exchange their target offsets, then each
-- of the two target offsets, if any, gets its new position.
def Mapping.swapDestinations (M : Mapping) (a b : Nat) : Mapping :=
  let dest := (M.dest.set a (M.dest.getD b none)).set b (M.dest.getD a none)
  let pos := match dest.getD a none with
    | some d => M.pos.set d (some a)
    | none => M.pos
  let pos := match dest.getD b none with
    | some d => pos.set d (some b)
    | none => pos
  ⟨dest, pos⟩

-- `swapWith`: the top and the slot at `pos` exchange their places and their target offsets.
def State.swapWith (s : State) (pos : Nat) : M State :=
  let top := s.stack.length - 1
  if s.stack.length ≤ pos ∨ s.mapping.dest.getD pos none = some pos then .error .assertion
  else if ¬(1 ≤ top - pos ∧ top - pos ≤ MAX_SWAP_DEPTH) then .error .assertion
  else .ok { s with
    stack := (s.stack.set pos (s.stack.getD top default)).set top (s.stack.getD pos default),
    trace := s.trace ++ [Op.swap (top - pos)],
    mapping := s.mapping.swapDestinations pos top }

-- The scan of `removeSurplus` below `p`, from the top down: the first slot with no target
-- offset is the shallowest, the last one in swap reach the deepest.
def State.surplusScan (s : State) : Nat → Option Nat → Option Nat → Option Nat × Option Nat
  | 0, sh, dp => (sh, dp)
  | p + 1, sh, dp =>
    if s.mapping.dest.getD p none = none then
      s.surplusScan p (if sh = none then some p else sh)
        (if s.stack.length - 1 - p ≤ MAX_SWAP_DEPTH then some p else dp)
    else s.surplusScan p sh dp

-- The first slot below `p`, from the top down, with no target offset and equal to the slot at
-- `top`.
def State.equalBelow (s : State) (top : Nat) : Nat → Option Nat
  | 0 => none
  | p + 1 =>
    if s.mapping.dest.getD p none = none ∧ s.stack.getD p default = s.stack.getD top default then
      some p
    else s.equalBelow top p

-- The loop of `removeSurplus`, with at most `fuel` passes. The result has the offset and the
-- excess of a slot out of swap reach, if any.
def State.surplusLoop (s : State) : Nat → M (Option (Nat × Nat) × State)
  | 0 => .ok (none, s)
  | fuel + 1 =>
    if s.stack = [] then .ok (none, s)
    else match s.surplusScan s.stack.length none none with
      | (none, _) => .ok (none, s)
      | (some sh, none) =>
        let excess := s.stack.length - 1 - sh - MAX_SWAP_DEPTH
        if excess = 0 then .error .assertion else .ok (some (sh, excess), s)
      | (some sh, some dp) =>
        let top := s.stack.length - 1
        let s1 : M State :=
          if sh = top then .ok s
          else match s.equalBelow top top with
            | some e => .ok { s with mapping := s.mapping.swapDestinations e top }
            | none => s.swapWith dp
        (s1.bind State.pop).bind (·.surplusLoop fuel)

-- `removeSurplus`: each pass pops a slot, so the size bounds the number of passes.
def State.removeSurplus (s : State) : M (Option (Nat × Nat) × State) :=
  s.surplusLoop s.stack.length

end Map

end FlatShuffler
