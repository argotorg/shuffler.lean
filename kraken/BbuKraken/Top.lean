module

public import BbuKraken.Layout
import all BbuKraken.Layout
public import BbuKraken.FlatRel
import all BbuKraken.FlatRel

@[expose] public section

/-!
The spec of `build_bottom_up(m, n, data, target, dest, spilled, ops, blocked)`.
`s` is the state at the call: the first six arguments are in registers, `ops`
and `blocked` are the words at `rsp`. The model inputs are functions of `s`. The
source stack is the first `m` slots of `data`; at the return `data` holds the
result stack.

If `m > n` or `n > MAX_N`, `build_bottom_up` returns `-2` and reads no memory.
Else it makes the struct in its frame and calls `buildBottomUp`. It maps the `Status`
of `buildBottomUp` to the result: `Done` writes `0` and `0` to `blocked` and gives the trace size,
`Blocked` copies `m_blocked` to `blocked` and gives the trace size, `AssertionFailed` gives `-2`.

`TopFlatPost` is the result of the flat model `Flat.build_bottom_up` (the unit `Unit/Top.lean`).
`TopPost` is the result of the list model `buildBottomUp` (`Final.lean`). `Final.lean` gets
`TopPost` from `TopFlatPost` with the bridge `Flat.build_bottom_up_rel` (`FlatBridge.lean`).
-/

open Std.WP Lean.Order
open scoped Program.WP

namespace Bbu

section
variable (s : MachineData)

abbrev mArg : Nat := (rdi s).toNat
abbrev nArg : Nat := (rsi s).toNat
abbrev dataArg : Addr := rdx s
abbrev tgtArg : Addr := rcx s
abbrev dstArg : Addr := r8 s
abbrev splArg : Addr := s.regs.get64 .r9
abbrev opsArg : Addr := rd s.dmem (rsp s)
abbrev blkArg : Addr := rd s.dmem (rsp s + 8#64)

-- The guard of `build_bottom_up`: `m ≤ n ≤ MAX_N`.
abbrev TopGuard : Prop := mArg s ≤ nArg s ∧ nArg s ≤ MAX_N

/-! ## The inputs of the flat model

The arrays of `MAX_N` elements that the flat model reads: the first `n` words of `data` and of
`target` (the words that the struct view holds), and the first `m` words of `dest`. The
elements above are `default` and `0`; the flat model does not read them. -/

def flatData : Vector StackSlot MAX_N := Vector.ofFn fun i =>
  if i.val < nArg s then StackSlot.ofWord (rd s.dmem (wordAt (dataArg s) i)) else default

def flatTgt : Vector StackSlot MAX_N := Vector.ofFn fun i =>
  if i.val < nArg s then StackSlot.ofWord (rd s.dmem (wordAt (tgtArg s) i)) else default

def flatDest : Vector Word MAX_N := Vector.ofFn fun i =>
  if i.val < mArg s then rd s.dmem (wordAt (dstArg s) i) else 0

-- `m_spills[i]`: the byte at `spilled + i`. The asm adds the id zero-extended to 64 bits.
def topSpill (i : BitVec 32) : BitVec 8 := rdb s.dmem (splArg s + i.setWidth 64)

/-! ## The inputs of the list model -/

def topEnv : Env := Flat.listEnv (nArg s) (flatTgt s) (topSpill s)
def topSource : List StackSlot := Flat.listSource (mArg s) (flatData s)
def topDests : List Nat := Flat.listDests (mArg s) (flatDest s)

/-! ## The memory -/

-- The target slot `d`.
def topTgt (d : Nat) : StackSlot := StackSlot.ofWord (rd s.dmem (wordAt (tgtArg s) d))

-- The spilled bytes of the variables in the target.
def topSpl : List (Addr × Nat) :=
  (List.range (nArg s)).filterMap fun d =>
    (spillId (topTgt s d)).map fun i => (splArg s + BitVec.ofNat 64 i, 1)
-- The locals of `build_bottom_up` after `subq`: the struct (`8 * WORDS` bytes and the word
-- `m_plannedMapping`), 8 bytes of padding, the two arrays of the planned mapping (`MAX_N` words
-- each) and 8 bytes of padding.
def topLocals : Nat := 8 * WORDS + 8 + 8 + 2 * (8 * MAX_N) + 8
-- The frame: the return address, the locals, and the return address and the 2068 free words
-- of `buildBottomUp` (`Unit.loop_unit`).
def topF : Nat := 8 + topLocals + 8 * (1 + 2068)
theorem topF_eq : topF = 49432 := rfl

-- The memory that `build_bottom_up` writes: the working stack, the ops buffer and `blocked`.
def topOut : List (Addr × Nat) :=
  [(dataArg s, 8 * nArg s), (opsArg s, 72 * nArg s), (blkArg s, 16)]
-- The inputs that the callees read: the target and the spilled bytes.
def topRd : List (Addr × Nat) := (tgtArg s, 8 * nArg s) :: topSpl s
def topIn : List (Addr × Nat) := (rsp s, 16) :: (dstArg s, 8 * mArg s) :: topRd s

-- The memory facts for the call of `buildBottomUp`, when the guard holds.
-- The callees write the working stack and the ops buffer, and read the target and the spilled
-- bytes. The frame holds the struct. These regions are disjoint, but the target and the spilled
-- bytes can overlap (`disj_frame`, `disj_data`, `disj_ops`; `Sep.splOut`).
-- `build_bottom_up` reads `dest` and the word `ops` at `rsp` before the call: no store before
-- these reads goes out of the frame. It reads the word `blocked` at `rsp + 8` after the call, so
-- this word is disjoint from the regions that the call writes (`disj_blkp`). It writes `blocked`
-- after the call, and the result is the content of `data` and of the ops buffer after that, so
-- `blocked` is disjoint from them (`disj_blk`).
-- `TopMem` is the `TopMem` of 12cb0e8 with `disj_blk` and `disj_blkp` (`TopTest.lean`).
-- `(topDests s).length = (topSource s).length` follows (`length_topDests_eq`).
structure TopMem : Prop where
  dests : Dests (nArg s) (topDests s)
  mapped : Mem.Mapped (topOut s ++ topIn s) s.dmem
  data_lt : (dataArg s).toNat + 8 * nArg s ≤ 2 ^ 64
  tgt_lt : (tgtArg s).toNat + 8 * nArg s ≤ 2 ^ 64
  ops_lt : (opsArg s).toNat + 72 * nArg s ≤ 2 ^ 64
  blk_lt : (blkArg s).toNat + 16 ≤ 2 ^ 64
  disj_frame : Mem.Blocks.Disjoint [frame topF s] (topOut s ++ (dstArg s, 8 * mArg s) :: topRd s)
  disj_data : Mem.Blocks.Disjoint [(dataArg s, 8 * nArg s)] ((opsArg s, 72 * nArg s) :: topRd s)
  disj_ops : Mem.Blocks.Disjoint [(opsArg s, 72 * nArg s)] (topRd s)
  disj_blk : Mem.Blocks.Disjoint [(blkArg s, 16)] [(dataArg s, 8 * nArg s), (opsArg s, 72 * nArg s)]
  disj_blkp : Mem.Blocks.Disjoint [(rsp s + 8#64, 8)] [(dataArg s, 8 * nArg s), (opsArg s, 72 * nArg s)]

-- The frame holds the return address, so it is mapped also when the guard fails.
structure TopPre : Prop where
  frame : Mem.Mapped [frame topF s] s.dmem
  rsp_le : topF ≤ (rsp s).toNat
  mem : TopGuard s → TopMem s

def topMod : Modifies :=
  ⟨[.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11], frame topF s :: topOut s⟩

-- Operation `i` in the ops buffer of `t`: 12 bytes at `12i`.
def topOp (t : MachineData) (i : Nat) : Op :=
  let a := opsArg s + BitVec.ofNat 64 (12 * i)
  ⟨rdb t.dmem a, rdb t.dmem (a + 1#64), StackSlot.ofWord (rd t.dmem (a + 4#64))⟩

-- Slot `i` of `data` in `t`.
def topData (t : MachineData) (i : Nat) : StackSlot :=
  StackSlot.ofWord (rd t.dmem (wordAt (dataArg s) i))

/-! ## The result of the flat model -/

-- The memory of `t` holds the flat state `fs`: the operations in the ops buffer, the stack in
-- `data`, and the two words of `blocked`.
structure FlatMem (t : MachineData) (fs : Flat.St) : Prop where
  ops : (List.range fs.trace.length).map (topOp s t) = fs.trace
  data : (List.range fs.size.toNat).map (topData s t) = Flat.slotsOf fs
  blk0 : rd t.dmem (blkArg s) = fs.blockedOffset
  blk1 : rd t.dmem (wordAt (blkArg s) 1) = fs.blockedExcess

-- `rax` is the result word of `r`. If it is the trace size, the memory holds the state of `r`.
def FlatOut (t : MachineData) (r : Word × Option Flat.St) : Prop :=
  rax t = r.1 ∧ ∀ fs, r.2 = some fs → r.1 = BitVec.ofNat 64 fs.trace.length → FlatMem s t fs

-- The postcondition of the unit `Unit.buildBottomUp_unit`: the result of the flat model on the
-- inputs in `s`. `u` is the content of the members that the constructor does not initialize.
def TopFlatPost (t : MachineData) : Prop :=
  Mem.Mapped [frame topF s] t.dmem ∧
    ∃ u, FlatOut s t
      (Flat.build_bottom_up (rdi s) (rsi s) (flatData s) (flatTgt s) (flatDest s) (topSpill s) u)

-- At an assertion exit, the buffers hold the stores made before the assertion.
-- The caller's blocked output is written only after a normal return from the loop.
def TopFlatExit (t : MachineData) : Prop :=
  TopGuard s ∧ Mem.Mapped [frame topF s] t.dmem ∧
    Mem.UnchangedOutside (frame topF s :: topOut s) s.dmem t.dmem ∧
    ∃ u fs,
      Flat.build_bottom_up (rdi s) (rsi s) (flatData s) (flatTgt s) (flatDest s)
        (topSpill s) u = (-2, some fs) ∧
      fs.trace.length ≤ 6 * nArg s ∧
      (List.range fs.trace.length).map (topOp s t) = fs.trace ∧
      (List.range fs.size.toNat).map (topData s t) = Flat.slotsOf fs

/-! ## The result of the list model -/

-- The memory of `t` holds the list state `st`, the blocked slot `pos` and the excess `excess`.
structure OutMem (t : MachineData) (st : St) (pos excess : Nat) : Prop where
  ops : (List.range st.trace.length).map (topOp s t) = st.trace
  data : (List.range st.len).map (topData s t) = st.slots.map Slot.val
  blk0 : rd t.dmem (blkArg s) = BitVec.ofNat 64 pos
  blk1 : rd t.dmem (wordAt (blkArg s) 1) = BitVec.ofNat 64 excess

-- The result `res` of the model in `t`. A done result has the blocked words `0`.
def TopOut (t : MachineData) : M St → Prop
  | .ok st => rax t = BitVec.ofNat 64 st.trace.length ∧ OutMem s t st 0 0
  | .error (.blocked pos excess st) =>
    rax t = BitVec.ofNat 64 st.trace.length ∧ OutMem s t st pos excess
  | .error .assertion => rax t = -2#64

-- The result of `build_bottom_up` in `t`. If the guard holds, it is the result of the
-- model: the operations in the ops buffer, the final stack in `data`, and `blocked`.
def TopPost (t : MachineData) : Prop :=
  Mem.Mapped [frame topF s] t.dmem ∧
  if TopGuard s then TopOut s t (buildBottomUp (topEnv s) (topSource s) (topDests s))
  else rax t = -2#64

def TopModelExit (t : MachineData) : Prop :=
  TopFlatExit s t ∧ buildBottomUp (topEnv s) (topSource s) (topDests s) = .error .assertion

end

/-! ## The model inputs from `TopGuard` and `TopMem` -/

section
variable {s : MachineData}

theorem length_topSource (hg : TopGuard s) : (topSource s).length = mArg s := by
  have ⟨h1, h2⟩ := hg
  simp only [topSource, Flat.listSource, List.length_take, Vector.length_toList]; omega

theorem length_topDests (hg : TopGuard s) : (topDests s).length = mArg s := by
  have ⟨h1, h2⟩ := hg
  simp only [topDests, Flat.listDests, List.length_map, List.length_take, Vector.length_toList]
  omega

theorem length_topEnv (hg : TopGuard s) : (topEnv s).n = nArg s := by
  have ⟨h1, h2⟩ := hg
  simp only [topEnv, Flat.listEnv, Env.n, List.length_take, Vector.length_toList]; omega

theorem length_topDests_eq : (topDests s).length = (topSource s).length := by
  simp only [topDests, topSource, Flat.listDests, Flat.listSource, List.length_map,
    List.length_take, Vector.length_toList]

theorem TopGuard.source_le (hg : TopGuard s) : (topSource s).length ≤ (topEnv s).n := by
  rw [length_topSource hg, length_topEnv hg]; exact hg.1

theorem TopMem.env_dests (hg : TopGuard s) (hm : TopMem s) : Dests (topEnv s).n (topDests s) := by
  rw [length_topEnv hg]; exact hm.dests

theorem TopGuard.n_le_max (hg : TopGuard s) : (topEnv s).n ≤ MAX_N := by
  rw [length_topEnv hg]; exact hg.2

theorem TopPre.rsp_ge (hp : TopPre s) : 49432 ≤ (rsp s).toNat := by
  have := hp.rsp_le; simp only [topF_eq] at this; omega

-- The guard with the value of `MAX_N`, for `omega`.
theorem TopGuard.n_le' (hg : TopGuard s) : nArg s ≤ 1024 := hg.2

end

end Bbu
