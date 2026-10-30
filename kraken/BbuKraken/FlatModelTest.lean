import BbuKraken.FlatModel

/-!
Tests of `FlatModel.lean`: each unit on small states, the paths that fail
(`Status.assertionFailed` and `Status.blocked`), the size_t wraps, the bounds of
`build_bottom_up` (`n = 0`, `m = n`, `n = MAX_N`, `m > n`, `n > MAX_N`), and the
agreement with the list model `Bbu.buildBottomUp` on 15 deep stacks. The agreement on all
inputs with `n ≤ 3` (32229) is off: the list model has the old `finish`, not the solc `permute`,
which regroups equal slots. On the 9056 inputs where the two differ,
`build_bottom_up`, the PR31 model and the C++ agree. The members that the constructor
does not initialize get two contents, for `n ≤ 2`, and the results are the same.
`test/bbu_diff.sh` compares `build_bottom_up` with the PR31 model and the C++ on more
states.
-/

namespace Bbu.Flat.Test

open Bbu

/-! ## Inputs -/

-- Literals (`Const`), variables (`Phi`) and junk.
def x : StackSlot := ⟨1, Value, Const⟩
def y : StackSlot := ⟨2, Value, Const⟩
def var (i : Nat) : StackSlot := ⟨.ofNat 32 i, Value, 1⟩
def J : StackSlot := .junk

-- A buffer that holds `l` from offset 0, and `default` above it.
def vec {α : Type} [Inhabited α] (l : List α) : Vector α MAX_N :=
  Vector.ofFn fun i => l[i.val]?.getD default

-- Content of memory that the C++ does not write before it reads it.
def junkWords (k : Nat) : Vector Word MAX_N := Vector.ofFn fun i => .ofNat 64 (i.val * k + 5)
def junkSlots : Vector StackSlot MAX_N := Vector.ofFn fun i => var (i.val + 100)
def u1 : Uninit := ⟨junkWords 7, junkWords 13, 77, 99⟩
def u2 : Uninit := ⟨vec [], vec [], 0, 0⟩

-- `spills id` is `1` for the ids in `ids`.
def spillsOf (ids : List Nat) (i : BitVec 32) : BitVec 8 := if ids.contains i.toNat then 1 else 0

-- The state of the constructor.
def mk (source target : List StackSlot) (dests : List Nat) (spilled : List Nat := []) : St :=
  ctor (vec source) (.ofNat 64 source.length) (vec target) (.ofNat 64 target.length)
    (vec (dests.map (BitVec.ofNat 64))) (spillsOf spilled) u1

def words (l : List Nat) : List Word := l.map (BitVec.ofNat 64)

/-! ## Views -/

def below (k : Word) : List Word := (List.range k.toNat).map (BitVec.ofNat 64)
def slots (st : St) : List StackSlot := (below st.size).map (get st.data)
def dests (st : St) : List Word := (below st.size).map (get st.dest)
def positions (st : St) : List Word := (below st.targetSize).map (get st.pos)

-- The members that the units write.
def view (st : St) : List StackSlot × List Word × List Word × Word × List Op :=
  (slots st, dests st, positions st, st.pend, st.trace)

def viewR (r : Status × St) := (r.1, view r.2)

/-! ## The constructor -/

-- Two slots bound for `2` and `0`: only offset `1` is unbound.
#guard view (mk [x, y] [x, y, x] [2, 0]) = ([x, y], words [2, 0], [1, NONE, 0], 1, [])
#guard view (mk [] [] []) = ([], [], [], 0, [])
#guard view (mk [] [x, y] []) = ([], [], [NONE, NONE], 2, [])
-- The constructor writes no member above the size and `n`.
#guard (mk [x] [x] [0]).dest[1] = u1.dest[1]
#guard (mk [x] [x] [0]).pos[1] = u1.pos[1]
#guard (mk [x] [x] [0]).blockedOffset = 77

/-! ## `Stack` -/

#guard view (stackSwap (mk [x, y, J] [x, y, J] [0, 1, 2]) 0)
  = ([J, y, x], words [0, 1, 2], words [0, 1, 2], 0, [⟨Swap, 2, .junk⟩])
-- `m_destinationOf` above the size is not initialized: `u1.dest[1] = 12`.
#guard view (stackPush (mk [x] [x, y] [0]) y) = ([x, y], words [0, 12], [0, NONE], 1, [.push y])
-- A pushed variable is a load.
#guard (stackPush (mk [] [x] []) (var 3)).trace = [⟨Load, 0, var 3⟩]
#guard view (stackDup (mk [x, y] [x, y, x] [0, 1]) 0)
  = ([x, y, x], words [0, 1, 19], [0, 1, NONE], 1, [⟨Dup, 2, .junk⟩])

/-! ## `Mapping` -/

#guard view (bind (mk [x, y] [x, y] [0, 1]) 0 1) = ([x, y], words [1, 1], words [0, 0], 0, [])
#guard view (swapDestinations (mk [x, y] [x, y] [1, 0]) 0 1)
  = ([x, y], words [0, 1], words [0, 1], 0, [])
-- A slot without a destination: only the other one binds its destination.
#guard view (swapDestinations
    { mk [x, y] [x, y] [0, 1] with dest := put (mk [x, y] [x, y] [0, 1]).dest 0 NONE } 0 1)
  = ([x, y], [1, NONE], words [0, 0], 0, [])

/-! ## Queries -/

#guard isSpilled (mk [] [] [] [3]) (var 3)
#guard !isSpilled (mk [] [] [] [3]) (var 4)
-- A literal or a non-value is never spilled.
#guard !isSpilled (mk [] [] [] [1]) x
#guard !isSpilled (mk [] [] [] [0]) ⟨0, FunctionReturnLabel, Unreachable⟩
#guard shallowestCopyPosition (mk [] [] []) x = NONE
#guard shallowestCopyPosition (mk [x, y, x] [x, y, x] [0, 1, 2]) x = 2
#guard shallowestCopyPosition (mk [x, y, x] [x, y, x] [0, 1, 2]) y = 1
#guard shallowestCopyPosition (mk [x, y] [x, y] [0, 1]) (var 0) = NONE
-- Only the slots below the size count.
#guard shallowestCopyPosition { mk [x, y] [x, y] [0, 1] with size := 1 } y = NONE

/-! ## `swapWith`, `push`, `dup`, `block` -/

def s3 : St := mk [x, y, J] [x, y, J] [2, 0, 1]

#guard viewR (swapWith s3 0)
  = (.done, [J, y, x], words [1, 0, 2], words [1, 0, 2], 0, [⟨Swap, 2, .junk⟩])
-- The C++ checks: the offset exists, it is not final, and a swap reaches it.
#guard (swapWith s3 3).1 = .assertionFailed
#guard (swapWith (mk [x, y] [x, y] [0, 1]) 0).1 = .assertionFailed
#guard (swapWith s3 2).1 = .assertionFailed
def deep (k : Nat) : St :=
  mk ((List.range k).map var) ((List.range k).map var) ((List.range k).reverse)
#guard (swapWith (deep 18) 0).1 = .assertionFailed
#guard (swapWith (deep 18) 1).1 = .done
#guard ((swapWith (deep 18) 1).2.trace) = [⟨Swap, 16, .junk⟩]
-- A failed check keeps the state.
#guard view (swapWith s3 3).2 = view s3

#guard viewR (push (mk [x] [x, y] [0]) y 1) = (.done, [x, y], words [0, 1], words [0, 1], 1, [.push y])
-- The C++ pushes before the check: the state keeps the slot and the operation.
#guard viewR (push (mk [x] [x, y] [0]) y 0)
  = (.assertionFailed, [x, y], words [0, 12], [0, NONE], 1, [.push y])
#guard viewR (dup (mk [x] [x, x] [0]) 0 1)
  = (.done, [x, x], words [0, 1], words [0, 1], 1, [⟨Dup, 1, .junk⟩])
#guard (dup (mk [x] [x, x] [0]) 0 0).1 = .assertionFailed
-- A function return label is not DUPed, and the failed check keeps the state.
def frl : StackSlot := ⟨0, FunctionReturnLabel, Unreachable⟩
#guard viewR (dup (mk [frl] [frl, frl] [0]) 0 1)
  = (.assertionFailed, [frl], words [0], [0, NONE], 1, [])

#guard (block s3 1 0).1 = .assertionFailed
#guard (block s3 1 3).1 = .blocked
#guard ((block s3 1 3).2.blockedOffset, (block s3 1 3).2.blockedExcess) = (1, 3)
#guard ((blockSwapUnreachable (deep 18) 0).2.blockedExcess) = 1
#guard ((blockDupUnreachable (deep 18) 0).2.blockedExcess) = 2
-- A slot in reach gives `excess = 0`.
#guard (blockSwapUnreachable (deep 18) 1).1 = .assertionFailed

/-! ## `produce` and `generate` -/

-- Junk is pushed, a copy in reach is DUPed, a spilled variable is loaded.
#guard viewR (produce (mk [x] [x, J] [0]) 1) = (.done, [x, J], words [0, 1], words [0, 1], 0, [.push J])
#guard viewR (produce (mk [var 0] [var 0, var 0] [0]) 1)
  = (.done, [var 0, var 0], words [0, 1], words [0, 1], 0, [⟨Dup, 1, .junk⟩])
#guard viewR (produce (mk [x] [x, var 4] [0] [4]) 1)
  = (.done, [x, var 4], words [0, 1], words [0, 1], 0, [⟨Load, 0, var 4⟩])
-- A literal without a copy is pushed.
#guard (produce (mk [] [x] []) 0).2.trace = [⟨Push, 0, x⟩]
-- A copy at depth 16 is out of dup reach by 1.
def far : St :=
  mk ((List.range 17).map var) ((List.range 17).map var ++ [var 0]) (List.range 17)
#guard (produce far 17).1 = .blocked
#guard ((produce far 17).2.blockedOffset, (produce far 17).2.blockedExcess) = (0, 1)
-- A variable with no copy that is not spilled.
#guard (produce (mk [] [var 0] []) 0).1 = .assertionFailed
-- An offset that a slot is bound for already.
#guard (produce (mk [x] [x] [0]) 0).1 = .assertionFailed
-- `--m_pendingGenerations` wraps at 0.
#guard (produce { mk [] [x] [] with pend := 0 } 0).2.pend = -1

#guard (generate (mk [] [x] []) 1).1 = .assertionFailed
-- The produced slot goes down to its offset at once.
#guard viewR (generate (mk [x, y] [J, x, y] [1, 2]) 0)
  = (.done, [J, y, x], words [0, 2, 1], words [0, 2, 1], 0, [.push J, ⟨Swap, 2, .junk⟩])
-- An equal slot at the offset takes over the destination.
#guard viewR (generate (mk [x, y] [x, x, y] [1, 2]) 0)
  = (.done, [x, y, x], words [0, 2, 1], words [0, 2, 1], 0, [⟨Dup, 2, .junk⟩])

/-! ## `permute` -/

-- An empty stack, and slots in place.
#guard viewR (permute (mk [] [] [])) = (.done, [], [], [], 0, [])
#guard viewR (permute (mk [x] [x] [0])) = (.done, [x], words [0], words [0], 0, [])
#guard viewR (permute (mk [x, y] [x, y] [0, 1]))
  = (.done, [x, y], words [0, 1], words [0, 1], 0, [])
-- Two slots that change places.
#guard viewR (permute (mk [x, y] [x, y] [1, 0]))
  = (.done, [y, x], words [0, 1], words [0, 1], 0, [⟨Swap, 1, .junk⟩])
-- Equal slots are interchangeable: they keep their offsets and their destinations.
#guard viewR (permute (mk [x, x] [x, x] [1, 0]))
  = (.done, [x, x], words [1, 0], words [1, 0], 0, [])
-- After two swaps the slot at 1 is equal to the top and takes over its destination:
-- no third swap.
#guard viewR (permute (mk [x, y, x] [x, y, x] [1, 0, 2]))
  = (.done, [y, x, x], words [0, 1, 2], words [0, 1, 2], 0, [⟨Swap, 1, .junk⟩, ⟨Swap, 2, .junk⟩])
-- A slot with no destination.
#guard (permute
    { mk [x, y] [x, y] [0, 1] with dest := put (mk [x, y] [x, y] [0, 1]).dest 1 NONE }).1
  = .assertionFailed
-- Not a permutation: the C++ loop does not end, and the model fails when the fuel ends.
#guard (permute
    { mk [x, y] [x, y] [0, 1] with dest := put (mk [x, y] [x, y] [0, 1]).dest 1 0 }).1
  = .assertionFailed
-- Not a permutation: the group of `x` has two slots and one desired offset.
#guard (permute
    { mk [x, x] [x, x] [0, 1] with dest := put (mk [x, x] [x, x] [0, 1]).dest 0 1 }).1
  = .assertionFailed
-- The slot at 0 is bound for 17: out of swap reach by 1.
def wideDests : List Nat := [17] ++ (List.range 17).drop 1 ++ [0]
def wide : St := mk ((List.range 18).map var) ((List.range 18).map var) wideDests
#guard (permute wide).1 = .blocked
#guard ((permute wide).2.blockedOffset, (permute wide).2.blockedExcess) = (0, 1)
#guard (permute wide).2.trace = []
-- One swap, then the slot at 0 is out of reach: the trace keeps the swap.
def lateDests : List Nat := [17, 0] ++ (List.range 17).drop 2 ++ [1]
def late : St := mk ((List.range 18).map var) ((List.range 18).map var) lateDests
#guard (permute late).1 = .blocked
#guard ((permute late).2.blockedOffset, (permute late).2.blockedExcess) = (0, 1)
#guard (permute late).2.trace = [⟨Swap, 16, .junk⟩]

/-! ## The scans of `buildBottomUp` -/

-- No offset from 0 on needs a copy: the result is `NONE`.
#guard (urgentFrom (mk [x] [x, J] [0]) 0 0 NONE).toOption = some NONE
-- `var 0` is at depth 15 and the target needs a second copy at 16.
def urgentSt : St :=
  mk ((List.range 16).map var) ((List.range 16).map var ++ [var 0]) (List.range 16)
#guard (urgentFrom urgentSt 1 1 NONE).toOption = some 16
-- At `targetOffset = 0` the copy floats to the top: no hurry.
#guard (urgentFrom urgentSt 0 0 NONE).toOption = some NONE
-- A copy at depth 16 blocks.
#guard match urgentFrom far 0 0 NONE with
  | .error r => r.1 = .blocked ∧ r.2.blockedExcess = 1
  | .ok _ => False
-- The shallowest movable copy above `src`, or `src`.
#guard candidateFrom (mk [x, y, x] [y, x, x] [1, 0, 2]) x 0 2 = 0
#guard candidateFrom (mk [x, y, x] [y, x, x] [1, 0, 1]) x 0 2 = 2

/-! ## `build_bottom_up` -/

-- The size checks.
#guard (build_bottom_up 2 1 (vec [x, y]) (vec [x]) (vec (words [0, 1])) (spillsOf []) u1).1 = -2
#guard (build_bottom_up 2 1 (vec [x, y]) (vec [x]) (vec (words [0, 1])) (spillsOf []) u1).2.isNone
#guard (build_bottom_up 0 1025 (vec []) (vec []) (vec []) (spillsOf []) u1).1 = -2
#guard (build_bottom_up 0 0 (vec []) (vec []) (vec []) (spillsOf []) u1).1 = 0
-- A result that is not blocked writes 0 and 0 to `blocked`, over the 77 and 99 of `u1`.
#guard match build_bottom_up 0 0 (vec []) (vec []) (vec []) (spillsOf []) u1 with
  | (_, some st) => st.blockedOffset = 0 ∧ st.blockedExcess = 0
  | (_, none) => False
-- `n = MAX_N`, all slots in place.
#guard (build_bottom_up 1024 1024 (vec ((List.range 1024).map var)) (vec ((List.range 1024).map var))
  (vec (words (List.range 1024))) (spillsOf []) u1).1 = 0
-- A result that is not blocked is the number of operations.
#guard (build_bottom_up 2 2 (vec [x, y]) (vec [x, y]) (vec (words [1, 0])) (spillsOf []) u1).1 = 1
-- A blocked result writes `blocked` and returns the number of operations.
def bbuOf (dests : List Nat) : Word × Option St :=
  build_bottom_up 18 18 (vec ((List.range 18).map var)) (vec ((List.range 18).map var))
    (vec (words dests)) (spillsOf []) u1
#guard match bbuOf wideDests with
  | (r, some st) => r = 0 ∧ st.blockedOffset = 0 ∧ st.blockedExcess = 1
  | (_, none) => False
#guard match bbuOf lateDests with
  | (r, some st) => r = 1 ∧ st.blockedOffset = 0 ∧ st.blockedExcess = 1
  | (_, none) => False
-- A variable that is neither on the stack nor spilled.
#guard (build_bottom_up 0 1 (vec []) (vec [var 0]) (vec []) (spillsOf []) u1).1 = -2
-- A second copy of a function return label.
#guard (build_bottom_up 1 2 (vec [frl]) (vec [frl, frl]) (vec (words [0])) (spillsOf []) u1).1 = -2

/-! ## Agreement with the list model -/

-- The result of the list model, or of `build_bottom_up`: the final stack and the
-- operations, or the error.
def listOut (source target : List StackSlot) (dests spilled : List Nat) :
    Except Err (List StackSlot × List Op) :=
  match Bbu.buildBottomUp ⟨target, fun i => if spilled.contains i then 1 else 0⟩ source dests with
  | .ok st => .ok (st.slots.map Slot.val, st.trace)
  | .error err => .error err

def flatOut (u : Uninit) (garbage : Vector StackSlot MAX_N) (source target : List StackSlot)
    (dests spilled : List Nat) : Except Err (List StackSlot × List Op) :=
  let data := Vector.ofFn fun i => source[i.val]?.getD garbage[i]
  match build_bottom_up (.ofNat 64 source.length) (.ofNat 64 target.length) data (vec target)
      (vec (words dests)) (spillsOf spilled) u with
  | (r, some st) =>
    if r = -2 then .error .assertion
    else if r ≠ .ofNat 64 st.trace.length then .error (.blocked 9999 9999)
    else if st.blockedExcess ≠ 0 then .error (.blocked st.blockedOffset.toNat st.blockedExcess.toNat)
    else if st.size = .ofNat 64 target.length then .ok ((below st.size).map (get st.data), st.trace)
    else .error (.blocked 9999 9999)
  | (_, none) => .error .assertion

-- `Except` has no `DecidableEq`.
def same (a b : Except Err (List StackSlot × List Op)) : Bool :=
  match a, b with
  | .ok p, .ok q => decide (p = q)
  | .error e, .error f => decide (e = f)
  | _, _ => false

-- The injective maps of `m` sources into `n` offsets.
def injections : Nat → Nat → List (List Nat)
  | 0, _ => [[]]
  | m + 1, n => (injections m n).flatMap fun l =>
    ((List.range n).filter (· ∉ l)).map (l ++ [·])

def choices {α : Type} (vals : List α) : Nat → List (List α)
  | 0 => [[]]
  | k + 1 => (choices vals k).flatMap fun l => vals.map (l ++ [·])

-- All inputs with `m ≤ n ≤ 3` and the slots junk, a literal, or a variable
-- that is spilled (`var 1`) or not (`var 0`).
def cases : List (List StackSlot × List StackSlot × List Nat) :=
  (List.range 4).flatMap fun n => (List.range (n + 1)).flatMap fun m =>
    (choices [J, x, var 0, var 1] n).flatMap fun target =>
      (choices [J, x, var 0, var 1] m).flatMap fun source =>
        (injections m n).map fun dests => (source, target, dests)

#guard cases.length = 32229
-- The cases reach both results of the list model.
#guard cases.any fun (s, t, d) => listOut s t d [1] matches .ok _
#guard cases.any fun (s, t, d) => listOut s t d [1] matches .error .assertion
-- wf: enable after List
-- #guard cases.all fun (s, t, d) => same (flatOut u1 junkSlots s t d [1]) (listOut s t d [1])
-- The other content of the uninitialized members.
-- wf: enable after List
-- #guard (cases.filter (·.2.1.length ≤ 2)).all fun (s, t, d) =>
--   same (flatOut u2 (vec []) s t d [1]) (listOut s t d [1])
-- The result does not depend on the other content, for `n ≤ 2` only (time).
#guard (cases.filter (·.2.1.length ≤ 2)).all fun (s, t, d) =>
  same (flatOut u2 (vec []) s t d [1]) (flatOut u1 junkSlots s t d [1])

-- Deep stacks: the swap reach, the dup reach and the urgent copies.
def deepCases : List (List StackSlot × List StackSlot × List Nat) :=
  [17, 18, 20].flatMap fun k =>
    let vs := (List.range k).map var
    [(vs, vs, (List.range k).reverse),
     (vs, vs ++ [var 0], List.range k),
     (vs, vs ++ [var 0, var 1], (List.range k).map (· + 2)),
     (vs.drop 1, vs, (List.range (k - 1)).map (· + 1)),
     (vs, vs ++ [x, var 0], List.range k)]

#guard deepCases.any fun (s, t, d) => listOut s t d [] matches .ok _
#guard deepCases.any fun (s, t, d) => listOut s t d [] matches .error (.blocked _ _)
#guard deepCases.all fun (s, t, d) => same (flatOut u1 junkSlots s t d []) (listOut s t d [])

end Bbu.Flat.Test
