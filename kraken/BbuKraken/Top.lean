import BbuKraken.Contracts
import BbuKraken.ModelLemmas
import BbuKraken.Kit

/-!
The spec of `build_bottom_up(m, n, data, target, dest, spilled, ops, blocked)`.
`s` is the state at the call: the first six arguments are in registers, `ops`
and `blocked` are the words at `rsp`. The model inputs are functions of `s`. The
source stack is the first `m` slots of `data`; at the return `data` holds the
result stack.

If `m > n` or `n > MAX_N`, `build_bottom_up` returns `-2` and reads no memory.
Else it makes the struct in its frame and calls `buildBottomUp`. It maps the `Status`
of `buildBottomUp` to the result: `Done` gives the trace size, `Blocked` copies
`m_blocked` to `blocked` and gives `-1`, `AssertionFailed` gives `-2`.
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

-- The target slot `d`.
def topTgt (d : Nat) : StackSlot := StackSlot.ofWord (rd s.dmem (wordAt (tgtArg s) d))

def topEnv : Env where
  target := (List.range (nArg s)).map (topTgt s)
  spills := fun i => UInt8.ofBitVec (rdb s.dmem (splArg s + BitVec.ofNat 64 i))

def topSource : List StackSlot :=
  (List.range (mArg s)).map fun i => StackSlot.ofWord (rd s.dmem (wordAt (dataArg s) i))

def topDests : List Nat :=
  (List.range (mArg s)).map fun i => (rd s.dmem (wordAt (dstArg s) i)).toNat

-- The spilled bytes of the variables in the target.
def topSpl : List (Addr × Nat) :=
  (List.range (nArg s)).filterMap fun d =>
    (spillId (topTgt s d)).map fun i => (splArg s + BitVec.ofNat 64 i, 1)

-- The locals of `build_bottom_up` after `subq`: the struct and 8 bytes of padding.
def topLocals : Nat := 8 * WORDS + 8
-- The frame: the return address, the locals and the frame of `buildBottomUp`.
def topF : Nat := 8 + topLocals + loopF
theorem topF_eq : topF = 20720 := rfl

-- The memory that `build_bottom_up` writes: the working stack, the ops buffer and `blocked`.
def topOut : List (Addr × Nat) :=
  [(dataArg s, 8 * nArg s), (opsArg s, 72 * nArg s), (blkArg s, 16)]
-- The inputs that the callees read: the target and the spilled bytes.
def topRd : List (Addr × Nat) := (tgtArg s, 8 * nArg s) :: topSpl s
def topIn : List (Addr × Nat) := (rsp s, 16) :: (dstArg s, 8 * mArg s) :: topRd s

-- The memory facts for the call of `buildBottomUp`, when the guard holds.
-- The arguments at `rsp` and `dest` are read before the first store to `data`,
-- the ops buffer or `blocked`, so these may overlap them. The arguments at `rsp`
-- lie above the frame. `blocked` is written after the last read of the inputs and
-- of `data` and the ops buffer, so it may overlap them.
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

-- The result of `build_bottom_up` in `t`. If the guard holds, it is the result of the
-- model: the operations in the ops buffer and the final stack in `data`.
def TopPost (t : MachineData) : Prop :=
  Mem.Mapped [frame topF s] t.dmem ∧
  if TopGuard s then
    match buildBottomUpC (topEnv s) (topSource s) (topDests s) with
    | .ok st =>
      rax t = BitVec.ofNat 64 st.trace.length ∧ (List.range st.trace.length).map (topOp s t) = st.trace
        ∧ (List.range st.len).map (topData s t) = st.slots.map Slot.val
    | .error (.blocked pos excess _) =>
      rax t = -1#64 ∧ rd t.dmem (blkArg s) = BitVec.ofNat 64 pos
        ∧ rd t.dmem (wordAt (blkArg s) 1) = BitVec.ofNat 64 excess
    | .error .assertion => rax t = -2#64
  else rax t = -2#64

end

/-! ## The model inputs from `TopGuard` and `TopMem` -/

section
variable {s : MachineData}

theorem length_topSource : (topSource s).length = mArg s := by simp [topSource]
theorem length_topDests : (topDests s).length = mArg s := by simp [topDests]
theorem length_topEnv : (topEnv s).n = nArg s := by simp [topEnv, Env.n]

theorem length_topDests_eq : (topDests s).length = (topSource s).length := by
  rw [length_topSource, length_topDests]

-- A list of distinct offsets below `n` has at most `n` entries.
theorem Dests.length_le {n : Nat} {l : List Nat} (h : Dests n l) : l.length ≤ n := by
  have hnd : l.Nodup := List.pairwise_iff_getElem.mpr fun i j hi hj hij he => by
    have := h.2 i hi j hj he; omega
  have := hnd.length_le_of_subset (l₂ := List.range n) fun x hx => by
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
    exact List.mem_range.mpr (h.1 i hi)
  simpa using this

theorem TopGuard.source_le (hg : TopGuard s) : (topSource s).length ≤ (topEnv s).n := by
  rw [length_topSource, length_topEnv]; exact hg.1

theorem TopMem.env_dests (hm : TopMem s) : Dests (topEnv s).n (topDests s) := by
  rw [length_topEnv]; exact hm.dests

theorem TopGuard.n_le_max (hg : TopGuard s) : (topEnv s).n ≤ MAX_N := by
  rw [length_topEnv]; exact hg.2

theorem TopPre.rsp_ge (hp : TopPre s) : 20720 ≤ (rsp s).toNat := by
  have := hp.rsp_le; simp only [topF_eq] at this; omega

-- The guard with the value of `MAX_N`, for `omega`.
theorem TopGuard.n_le' (hg : TopGuard s) : nArg s ≤ 1024 := hg.2

end

end Bbu

/-! # The proof of `buildBottomUp_body` -/

namespace Bbu
namespace TopProof

section
variable (s : MachineData)

-- The struct: at the bottom of the locals (`8 + topLocals` bytes below `rsp`).
abbrev bS : Addr := rsp s - 16480#64

def topRes : M St := buildBottomUpC (topEnv s) (topSource s) (topDests s)

def st0 : St := init (topEnv s) (topSource s) (topDests s)
end

section
variable {s : MachineData}

-- The struct lies in the frame.
theorem struct_in_frame (hp : TopPre s) :
    ∀ x, Mem.Blocks.Inside x 1 [(bS s, 8 * WORDS)] → Mem.Blocks.Inside x 1 [frame topF s] := by
  intro x hx
  have := hp.rsp_ge
  simp only [Mem.Blocks.Inside, or_false, WORDS_eq, topF_eq, bS, rsp] at *
  bv_omega

theorem topRd_in {x : Addr} (h : Mem.Blocks.Inside x 1 (topRd s)) : Mem.Blocks.Inside x 1 (topIn s) :=
  h.tail.tail

end

/-! ## The header and the inputs -/

section
variable (s : MachineData)

-- The memory `m` keeps the header words 3 to 8 and the bytes outside the
-- frame and the outputs.
structure Hd (m : Mem 64) : Prop where
  n : rd m (wordAt (bS s) 3) = rsi s
  tgt : rd m (wordAt (bS s) 4) = tgtArg s
  spl : rd m (wordAt (bS s) 5) = splArg s
  ops : rd m (wordAt (bS s) 6) = opsArg s
  blk : rd m (wordAt (bS s) 7) = blkArg s
  dat : rd m (wordAt (bS s) 8) = dataArg s
  un : Mem.UnchangedOutside (frame topF s :: topOut s) s.dmem m
end

section
variable {s : MachineData} {m : Mem 64}

end

/-! ## The memory at the call -/

section
variable (s : MachineData) (ra : Int64)

-- The memory `m` at the call of `buildBottomUp`: the return address, the struct
-- and the frame.
structure Fm (m : Mem 64) : Prop where
  hd : Hd s m
  ra : rd m (rsp s - 8#64) = ra.toBitVec
  map : Mem.Mapped (frame topF s :: topOut s) m
  wf : Wf m (bS s)
end

section
variable {s : MachineData} {ra : Int64} {m m' : Mem 64} {i : Nat}

/-! ## The model at the start -/

end

end TopProof
end Bbu

namespace Bbu
namespace TopProof

/-! ## The memory before the call -/

section
variable (s : MachineData) (ra : Int64)

-- The memory `m` before the call: only the frame changed, and the return
-- address and the header words 0, 3, 4, 5 and 8 are set.
structure Ent (m : Mem 64) : Prop where
  un : Mem.UnchangedOutside [frame topF s] s.dmem m
  map : Mem.Mapped [frame topF s] m
  ra : rd m (rsp s - 8#64) = ra.toBitVec
  w0 : rd m (wordAt (bS s) 0) = rdi s
  w3 : rd m (wordAt (bS s) 3) = rsi s
  w4 : rd m (wordAt (bS s) 4) = tgtArg s
  w5 : rd m (wordAt (bS s) 5) = splArg s
  w8 : rd m (wordAt (bS s) 8) = dataArg s

-- The first `k` words of `m_positionOf` are `SIZE_MAX`.
def Cleared (m : Mem 64) (k : Nat) : Prop :=
  ∀ d < k, rd m (wordAt (bS s) (POS + d)) = -1#64

-- `m_positionOf` after the first `i` binds.
def posAfter (i : Nat) : List (Option Nat) :=
  (List.range i).foldl (fun p j => p.set (topDests s)[j]! (some j)) (List.replicate (nArg s) none)

-- The first `i` slots are bound.
structure Bound (m : Mem 64) (i : Nat) : Prop where
  dest : ∀ j < i, rd m (wordAt (bS s) (DEST + j)) = rd s.dmem (wordAt (dstArg s) j)
  pos : (List.range (nArg s)).map (fun d => optOf (rd m (wordAt (bS s) (POS + d)))) = posAfter s i

-- The registers at the labels after the entry block.
structure Rg (t : MachineData) : Prop where
  rsp : t.regs.rsp.toBitVec = bS s
  rbx : t.regs.rbx = s.regs.rbx
  rbp : t.regs.rbp = s.regs.rbp
  r12 : t.regs.r12 = s.regs.r12
  r13 : t.regs.r13 = s.regs.r13
  r14 : t.regs.r14 = s.regs.r14
  r15 : t.regs.r15 = s.regs.r15

-- `.LB112`: the first `k` words of `m_positionOf` are set, `rax` points to word `k`.
def At112 (t : MachineData) : Prop :=
  ∃ k < nArg s, t.regs.rax.toBitVec = bS s + BitVec.ofNat 64 (8 * k) ∧ Ent s ra t.dmem
    ∧ Cleared s t.dmem k ∧ Rg s t ∧ t.regs.rdi.toBitVec = rdi s ∧ t.regs.rsi.toBitVec = rsi s
    ∧ t.regs.r8.toBitVec = dstArg s ∧ t.regs.rdx.toBitVec = bS s + BitVec.ofNat 64 (8 * nArg s)

-- `.LB111`: `m_positionOf` is set.
def At111 (t : MachineData) : Prop :=
  Ent s ra t.dmem ∧ Cleared s t.dmem (nArg s) ∧ Rg s t ∧ t.regs.rdi.toBitVec = rdi s
    ∧ t.regs.rsi.toBitVec = rsi s ∧ t.regs.r8.toBitVec = dstArg s

-- `.LB114`: the bind loop at the index `i` in `rax`.
def At114 (t : MachineData) : Prop :=
  Ent s ra t.dmem ∧ Bound s t.dmem t.regs.rax.toNat ∧ Rg s t ∧ t.regs.rdi.toBitVec = rdi s
    ∧ t.regs.rsi.toBitVec = rsi s ∧ t.regs.r8.toBitVec = dstArg s ∧ t.regs.rax.toNat < mArg s

-- `.LB113`: all the slots are bound.
def At113 (t : MachineData) : Prop :=
  Ent s ra t.dmem ∧ Bound s t.dmem (mArg s) ∧ Rg s t ∧ t.regs.rdi.toBitVec = rdi s
    ∧ t.regs.rsi.toBitVec = rsi s

-- The variant.
def V : Label → MachineData → Nat
  | "build_bottom_up", _ => 2 ^ 14
  | ".LB112", t => 2 ^ 12 + (8 * nArg s - (t.regs.rax.toBitVec - bS s).toNat)
  | ".LB111", _ => 2 ^ 11
  | ".LB114", t => 2 + (mArg s - t.regs.rax.toNat)
  | ".LB113", _ => 1
  | _, _ => 0

end

end TopProof
end Bbu

namespace Bbu
namespace TopProof

-- The registers and the arguments as `s.regs.r.toBitVec`.
macro "top_nrm" loc:(Lean.Parser.Tactic.location)? : tactic => `(tactic| simp only [bS, rsp, rdi,
  rsi, rdx, rcx, r8, rax, dataArg, dstArg, tgtArg, splArg, mArg, nArg, wordAt, DEST_eq, POS_eq,
  WORDS_eq, MAX_N, Reg64s.get64_rsp, Reg64s.get64_rdi, Reg64s.get64_rsi, Reg64s.get64_rdx,
  Reg64s.get64_rcx, Reg64s.get64_r8, Reg64s.get64_r9, Reg64s.get64_rax, Nat.reduceMul,
  Nat.reduceAdd] $(loc)?)

/-! ## The entry block and the loops -/

section
variable {s : MachineData} {ra : Int64} {m : Mem 64} {i k : Nat}

-- A struct word lies in the frame.
theorem word_in_frame (hp : TopPre s) (hk : k < WORDS) :
    Mem.Blocks.Inside (wordAt (bS s) k) 8 [frame topF s] := by
  have hge := hp.rsp_ge
  simp only [Mem.Blocks.Inside, or_false, topF_eq] at *; top_nrm at *; bv_omega

-- A store to a struct word after the header keeps `Ent`.
theorem Ent.store (hp : TopPre s) (h : Ent s ra m) (hk9 : 9 ≤ k) (hk : k < WORDS) (v : Int) :
    Ent s ra (m.storeInt (wordAt (bS s) k) 8 v) := by
  have hge := hp.rsp_ge
  obtain ⟨hu, hmap, cra, c0, c3, c4, c5, c8⟩ := h
  refine ⟨hu.storeInt (word_in_frame hp hk) v, hmap.storeInt _ _ _, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals top_nrm at *; bbu_rd; assumption

theorem posAfter_succ (i : Nat) :
    posAfter s (i + 1) = (posAfter s i).set (topDests s)[i]! (some i) := by
  simp only [posAfter, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

-- `m_positionOf` cleared: no slot is bound.
theorem Cleared.bound (h : Cleared s m (nArg s)) : Bound s m 0 := by
  refine ⟨fun j hj => absurd hj (Nat.not_lt_zero j), ?_⟩
  apply List.ext_getElem (by simp [posAfter])
  intro d h1 h2
  simp only [List.length_map, List.length_range] at h1
  simp [posAfter, h d h1, optOf]

-- The memory after one round of the bind loop, in the form of the `kvcgen64` goals.
def bM (m : Mem 64) (R R8 A : Addr) : Mem 64 :=
  (m.storeInt (R + A * 8#64 + 72#64) 8 (rd m (R8 + A * 8#64)).toInt).storeInt
    (R + rd m (R8 + A * 8#64) * 8#64 + 8264#64) 8 A.toInt

set_option maxHeartbeats 1000000 in
end

end TopProof
end Bbu

namespace Bbu
namespace TopProof

section
variable {s : MachineData} {ra : Int64} {m : Mem 64} {i : Nat} {t c u : MachineData}

-- The words at `rsp` are outside the frame.
theorem Ent.arg (hp : TopPre s) (h : Ent s ra m) {k : Nat} (hk : k ≤ 8) :
    rd m (rsp s + BitVec.ofNat 64 k) = rd s.dmem (rsp s + BitVec.ofNat 64 k) := by
  have hge := hp.rsp_ge
  refine rd_congr h.un fun y hy hf => ?_
  simp only [Mem.Blocks.Inside, or_false, topF_eq, rsp] at *; bv_omega

-- `m_positionOf` after all the binds.
theorem posAfter_m : posAfter s (mArg s) = initPositionOf (topEnv s).n (topDests s) := by
  rw [length_topEnv]; unfold initPositionOf posAfter; rw [length_topDests]

end

/-! ## The block `.LB113` -/

-- The memory at the call, in the form of the `kvcgen64` goals.
def cM2 (m : Mem 64) (R SI DI : Addr) : Mem 64 :=
  (m.storeInt (R + 8#64) 8 (SI - DI).toInt).storeInt (R + 16#64) 8 0

def cM3 (m : Mem 64) (R SI DI : Addr) : Mem 64 :=
  (cM2 m R SI DI).storeInt (R + 48#64) 8 (BitVec.toInt (rd (cM2 m R SI DI) (R + 16480#64)))

def cM (m : Mem 64) (R SI DI : Addr) : Mem 64 :=
  (cM3 m R SI DI).storeInt (R + 56#64) 8 (BitVec.toInt (rd (cM3 m R SI DI) (R + 16488#64)))

section
variable {s : MachineData} {ra : Int64} {m : Mem 64} {i : Nat} {t c u : MachineData}

set_option maxHeartbeats 1000000 in
end

end TopProof
end Bbu

namespace Bbu
namespace TopProof

section
variable {s : MachineData} {ra : Int64} {m : Mem 64} {i : Nat} {t c u : MachineData}

-- A callee keeps `Rg`.
theorem Rg.call {F : Nat} (h : Rg s c) (hag : (mod F c).Agree c u) : Rg s u := by
  have hreg : ∀ q, q ∉ [Reg64.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11] →
      u.regs.get64 q = c.regs.get64 q := fun q hq => hag.1 q hq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := hreg .rsp (by simp); simp only [Reg64s.get64_rsp] at this; rw [this]; exact h.rsp
  · have := hreg .rbx (by simp); simp only [Reg64s.get64_rbx] at this
    exact (UInt64.toBitVec_inj.mp this).trans h.rbx
  · have := hreg .rbp (by simp); simp only [Reg64s.get64_rbp] at this
    exact (UInt64.toBitVec_inj.mp this).trans h.rbp
  · have := hreg .r12 (by simp); simp only [Reg64s.get64_r12] at this
    exact (UInt64.toBitVec_inj.mp this).trans h.r12
  · have := hreg .r13 (by simp); simp only [Reg64s.get64_r13] at this
    exact (UInt64.toBitVec_inj.mp this).trans h.r13
  · have := hreg .r14 (by simp); simp only [Reg64s.get64_r14] at this
    exact (UInt64.toBitVec_inj.mp this).trans h.r14
  · have := hreg .r15 (by simp); simp only [Reg64s.get64_r15] at this
    exact (UInt64.toBitVec_inj.mp this).trans h.r15

-- The return address is at `rsp s - 8`.
theorem fm_retAddr (hp : TopPre s) (h : Fm s ra t.dmem)
    (hsp : t.regs.rsp.toBitVec = rsp s - 8#64) : t.retAddr = some ra := by
  have hge := hp.rsp_ge
  simp only [rsp, Reg64s.get64_rsp] at hge
  have hs : (t.dmem.loadInt (rsp s - 8#64) 8).isSome = true :=
    h.map.loadInt_isSome (Or.inl (by simp only [topF_eq, rsp, Reg64s.get64_rsp]; bv_omega))
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hs
  have hra := h.ra
  rw [rd, hv, Option.get!_some] at hra
  rw [MachineData.retAddr, show t.regs.get64 .rsp = rsp s - 8#64 from hsp, hv, Option.map_some, hra,
    Int64.ofBitVec_toBitVec]

theorem fm_retAddr_isSome (hp : TopPre s) (h : Fm s ra t.dmem)
    (hsp : t.regs.rsp.toBitVec = rsp s - 8#64) : t.retAddr.isSome = true := by
  rw [fm_retAddr hp h hsp]; rfl

/-! ## The entry block and the loop loads -/

-- The memory after the entry block.
def eM (s : MachineData) (ra : Int64) : Mem 64 :=
  (((((s.dmem.storeInt (s.regs.rsp.toBitVec - 8#64) 8 ra.toBitVec.toInt).storeInt
    (s.regs.rsp.toBitVec - 8#64 - 16472#64 + 32#64) 8 s.regs.rcx.toBitVec.toInt).storeInt
    (s.regs.rsp.toBitVec - 8#64 - 16472#64 + 24#64) 8 s.regs.rsi.toBitVec.toInt).storeInt
    (s.regs.rsp.toBitVec - 8#64 - 16472#64 + 40#64) 8 s.regs.r9.toBitVec.toInt).storeInt
    (s.regs.rsp.toBitVec - 8#64 - 16472#64 + 64#64) 8 s.regs.rdx.toBitVec.toInt).storeInt
    (s.regs.rsp.toBitVec - 8#64 - 16472#64) 8 s.regs.rdi.toBitVec.toInt

set_option maxHeartbeats 1000000 in
end

end TopProof
end Bbu

set_option experimental.vcgen true

namespace Bbu

-- The asm of `build_bottom_up` changed with the C++ build (`c/build_bottom_up.cpp`): the
-- guard `m > n || n > MAX_N`, the struct layout, the `Status` of `buildBottomUp` and the
-- copy of `m_blocked`. The proof for the C build is in git at 6f580e5.
-- The constructor counts the target offsets with no slot into `m_pendingGenerations`;
-- Model.lean `init` counts the same way. `init_pending` gives `n - m` for `Dests`.
theorem buildBottomUp_body [Host] [FunDecls]
    (hloop : Spec Names.buildBottomUp loopF loopA loopR) :
    ∀ s ra, ⦃ fun t => t = s.pushRa ra ∧ TopPre s ⦄ buildBottomUpAsm
      ⦃ (fun _ _ => False); fun a t => a = ra ∧ TopPost s t ∧ (topMod s).Agree s t ⦄ := by
  sorry -- wf:todo

end Bbu
