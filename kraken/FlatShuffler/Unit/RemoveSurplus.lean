module

public import FlatShuffler.Unit.Defs
import all FlatShuffler.Unit.Defs
public import FlatShuffler.Unit.Pop
import all FlatShuffler.Unit.Pop
public import FlatShuffler.Unit.PermuteSpecs
import all FlatShuffler.Unit.PermuteSpecs
public import FlatShuffler.Unit.RemoveSurplusLemmas
import all FlatShuffler.Unit.RemoveSurplusLemmas
public import FlatShuffler.Unit.ShallowestCopy
import all FlatShuffler.Unit.ShallowestCopy
public import FlatShuffler.FlatSurplus
import all FlatShuffler.FlatSurplus
public import FlatShuffler.Sep.Stores
import all FlatShuffler.Sep.Stores
public import ProofKit.Cfg
import all ProofKit.Cfg
public import ProofKit.CfgBlock
import all ProofKit.CfgBlock
public import ProofKit.Idioms
import all ProofKit.Idioms

@[expose] public section

/-!
# `removeSurplus`

`Names.removeSurplus` in `build/kraken/c/build_bottom_up.S`: 1 `pushq`, so 4 free words (1, a return slot, and 2 for the calls of
`swapWith` and `pop`). Each turn of the loop at
`.LB.Emission.removeSurplus.0` is one pass of `Flat.surplusPass`: the scan at
`.LB.Emission.removeSurplus.2`, the loop of `equalBelow` at `.LB.Emission.removeSurplus.4`, the
inline `swapDestinations`, the call of `swapWith`, and the call of `pop`.

The preconditions of the callees: each pass adds at most 2 records (a swap and a pop) and pops one
slot, so `nops + 2 * len ≤ 6n` holds at each pass (`surplusA`). `swapDestinations`, `swapWith` and
`pop` keep `DestOk`.

The invariant of each block gives the rest of `Flat.removeSurplus (flat g)` from the state of the
block (`afterR`, `afterPop`, `eqStep` in `RemoveSurplusLemmas.lean`). The variant is
`m_size * 2^67` plus a term below `2^67` for the position in a pass: each pass pops one slot.
-/

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

set_option experimental.vcgen true

namespace FlatShuffler.Unit

open FlatShuffler.Sep

-- `removeSurplus()`: room for a swap and a pop for each slot, and destinations below `n`.
def surplusA (g : G) (_s : MachineData) : Prop :=
  g.h.nops.toNat + 2 * g.h.len.toNat ≤ 6 * g.h.n.toNat + g.xo ∧ DestOk (flat g)
def surplusQ (g g' : G) (_s t : MachineData) : Prop := NormalResult Flat.removeSurplus g g' t

namespace Surplus

open Generate

/-! ## The invariants -/

-- The parts of each invariant: the frame, and the ghost `g1` after the passes so far.
structure Run (S : Addr) (g : G) (F : MProp 64) (s : MachineData) (ra : Int64) (g1 : G) (w : Word)
    (t : MachineData) : Prop where
  bx : Bx S g1 F s ra w t
  ok : g1.Ok
  keep : Keep g g1
  dok : DestOk (flat g1)

-- Room for a swap and a pop for each slot.
def Budget (g : G) : Prop := g.h.nops.toNat + 2 * g.h.len.toNat ≤ 6 * g.h.n.toNat + g.xo

section
variable (S : Addr) (g : G) (F : MProp 64) (s : MachineData) (ra : Int64) (t : MachineData)

-- `.LB.Emission.removeSurplus.0`: the start of a pass.
def At276 : Prop :=
  ∃ g1 w, Run S g F s ra g1 w t ∧ Budget g1
    ∧ Flat.removeSurplus (flat g) = Flat.removeSurplus (flat g1)

-- The parts of the invariants of the scan.
def Scan (g1 : G) (t : MachineData) : Prop :=
  Budget g1 ∧ Flat.removeSurplus (flat g) = Flat.removeSurplus (flat g1)
    ∧ t.regs.r8.toBitVec = g1.h.len ∧ t.regs.rdi.toBitVec = g1.h.len - 1#64

-- `.LB.Emission.removeSurplus.2`: the scan checks slot `rax`.
def At279 : Prop :=
  ∃ g1 w, Run S g F s ra g1 w t ∧ Scan g g1 t ∧ t.regs.rax.toBitVec < g1.h.len
    ∧ Flat.surplusScan (flat g1) (t.regs.rax.toBitVec + 1#64) t.regs.rdx.toBitVec
        t.regs.rsi.toBitVec
      = Flat.surplusScan (flat g1) (flat g1).size Flat.NONE Flat.NONE

-- `.LB.Emission.removeSurplus.1`: the scan checked slot `rax`.
def At277 : Prop :=
  ∃ g1 w, Run S g F s ra g1 w t ∧ Scan g g1 t ∧ t.regs.rax.toBitVec < g1.h.len
    ∧ Flat.surplusScan (flat g1) t.regs.rax.toBitVec t.regs.rdx.toBitVec t.regs.rsi.toBitVec
      = Flat.surplusScan (flat g1) (flat g1).size Flat.NONE Flat.NONE

-- `.LB.Emission.removeSurplus.3`: the end of the scan.
def At300 : Prop :=
  ∃ g1 w, Run S g F s ra g1 w t ∧ Scan g g1 t ∧ g1.h.len ≠ 0#64
    ∧ Flat.surplusScan (flat g1) (flat g1).size Flat.NONE Flat.NONE
      = (t.regs.rdx.toBitVec, t.regs.rsi.toBitVec)

-- `.LB.Emission.removeSurplus.4`: the loop of `equalBelow` checks slot `rax - 1`.
def At283 : Prop :=
  ∃ g1 w, Run S g F s ra g1 w t ∧ Budget g1 ∧ g1.h.len ≠ 0#64
    ∧ t.regs.rdi.toBitVec = g1.h.len - 1#64 ∧ t.regs.r8.toBitVec = t.regs.rdi.toBitVec * 8#64
    ∧ t.regs.rax.toBitVec ≤ t.regs.rdi.toBitVec
    ∧ Flat.removeSurplus (flat g)
      = afterR (eqStep (flat g1) t.regs.rax.toBitVec (g1.h.len - 1#64) t.regs.rsi.toBitVec)

-- `.LB.Emission.removeSurplus.5`: the destinations are swapped, and `positionOf` is written for
-- `rax`.
def At289 : Prop :=
  ∃ g2 w, Run S g F s ra g2 w t ∧ Budget g2 ∧ t.regs.rdi.toBitVec.toNat < maxStackSize
    ∧ (Flat.get g2.h.dest t.regs.rdi.toBitVec = Flat.NONE
      ∨ (Flat.get g2.h.dest t.regs.rdi.toBitVec).toNat < maxStackSize)
    ∧ Flat.removeSurplus (flat g) = afterPop (posAt (flat g2) t.regs.rdi.toBitVec)

-- `.LB.Emission.removeSurplus.11`: the call of `swapWith`.
def At301 : Prop :=
  ∃ g1 w, Run S g F s ra g1 w t ∧ Budget g1 ∧ g1.h.len ≠ 0#64
    ∧ Flat.removeSurplus (flat g) = afterR (Flat.swapWith (flat g1) t.regs.rsi.toBitVec)

-- `.LB.Emission.removeSurplus.12`: the call of `pop`. A swap is done, so the budget has one more
-- record.
def At282 : Prop :=
  ∃ g2 w, Run S g F s ra g2 w t
    ∧ g2.h.nops.toNat + 2 * g2.h.len.toNat ≤ 6 * g2.h.n.toNat + g2.xo + 1
    ∧ Flat.removeSurplus (flat g) = afterPop (flat g2)

-- `.LB.Emission.removeSurplus.6`: no surplus slot is reachable.
def At281 : Prop :=
  ∃ g1 w, Run S g F s ra g1 w t ∧ t.regs.r8.toBitVec = g1.h.len
    ∧ Flat.removeSurplus (flat g) = Flat.blockSwapUnreachable (flat g1) t.regs.rdx.toBitVec

-- `.LB.Emission.removeSurplus.8` and `.LB.Emission.removeSurplus.10`: no surplus slot.
def AtDone : Prop :=
  ∃ g1 w, Run S g F s ra g1 w t ∧ Flat.removeSurplus (flat g) = (.done, flat g1)

-- `.LB.Emission.removeSurplus.9`: the result.
def At275 : Prop :=
  ∃ g1 w, Bx S g1 F s ra w t ∧ g1.Ok ∧ surplusQ g g1 s t


-- `.LB.Emission.removeSurplus.7`: the block excess is zero.
def AtFail : Prop :=
  ∃ g1 w, Bx S g1 F s ra w t ∧ g1.Ok ∧ surplusX g g1 s t

end

-- The weights of the variant.
abbrev wB : Nat := 147573952589676412928
abbrev wH : Nat := 36893488147419103232

theorem wB_eq : wB = 2 ^ 67 := rfl
theorem wH_eq : wH = 2 ^ 65 := rfl

/-! Small facts for the blocks. Each one has its own proof, so that a tactic such as `bv_omega`
does not see the large context of the block. -/

theorem pred_lt {r : Word} (h : r ≠ 0#64) : r + BitVec.ofInt 64 (-1) < r := by
  rw [Generate.add_neg_one]; bv_omega

theorem pred_succ (r : Word) : r + BitVec.ofInt 64 (-1) + 1#64 = r := by
  rw [Generate.add_neg_one]; bv_omega

theorem none_lit : (18446744073709551615#64 : Word) = Flat.NONE := rfl

-- `cmpq $-1, %rdx; cmove %rax, %rdx`: the shallowest surplus slot.
theorem if_none (a r : Word) :
    (if (a - 18446744073709551615#64 == BitVec.zero 64) = true then r else a)
      = (if a = Flat.NONE then r else a) := by
  cases h : (a - 18446744073709551615#64 == BitVec.zero 64)
  · rw [ite_eq_right Bool.false_ne_true, ite_eq_right (ne_none_of_z h)]
  · rw [ite_eq_left rfl, ite_eq_left (none_of_z h)]

-- `subq %rax, %rcx; cmpq $16, %rcx; cmovbe %rax, %rsi`: the deepest reachable surplus slot.
theorem if_reach {g1 : G} {c r b : Word} (hc : c = g1.h.len - 1#64) :
    (if ((((c - r - 16#64).toNat : Int) != ((c - r).toNat : Int) - 16)
        || (c - r - 16#64 == BitVec.zero 64)) = true then r else b)
      = (if Flat.isSwapReachable (flat g1) r then r else b) := by
  have e : (flat g1).size - r - 1#64 = c - r := by
    show g1.h.len - r - 1#64 = c - r
    subst hc; bv_omega
  cases h : ((((c - r - 16#64).toNat : Int) != ((c - r).toNat : Int) - 16)
      || (c - r - 16#64 == BitVec.zero 64))
  · have h1 := not_le_of_be h
    have h2 : Flat.isSwapReachable (flat g1) r = false := by
      cases h3 : Flat.isSwapReachable (flat g1) r
      · rfl
      · have h4 := (reach_iff _ _).mp h3
        rw [e] at h4
        exact absurd h4 h1
    rw [h2]
  · have h1 := le_of_be h
    have h2 : Flat.isSwapReachable (flat g1) r = true := by
      rw [reach_iff, e]; exact h1
    rw [h2]

-- `.LB.Emission.removeSurplus.2`, `jne` taken: slot `r` is not surplus.
theorem scan279_ne {g1 : G} {r a b : Word} {T : Word × Word} (hlt : r < g1.h.len)
    (hd : (!Flat.get g1.h.dest r - 18446744073709551615#64 == BitVec.zero 64) = true)
    (hs : Flat.surplusScan (flat g1) (r + 1#64) a b = T) :
    Flat.surplusScan (flat g1) r a b = T := by
  have h1 : r + 1#64 ≠ 0#64 := by bv_omega
  have hn : Flat.isSurplus (flat g1) r = false := by
    have h2 := ne_none_of_z (by rwa [Bool.not_eq_true'] at hd)
    show (Flat.get g1.h.dest r == Flat.NONE) = false
    simpa using h2
  rw [scan_succ _ h1, hn, ite_eq_right Bool.false_ne_true] at hs
  exact hs

-- `.LB.Emission.removeSurplus.2`, `jne` not taken: slot `r` is surplus.
theorem scan279_hit {g1 : G} {r a b c : Word} {T : Word × Word} (hlt : r < g1.h.len)
    (hc : c = g1.h.len - 1#64)
    (hd : (!Flat.get g1.h.dest r - 18446744073709551615#64 == BitVec.zero 64) = false)
    (hs : Flat.surplusScan (flat g1) (r + 1#64) a b = T) :
    Flat.surplusScan (flat g1) r
      (if (a - 18446744073709551615#64 == BitVec.zero 64) = true then r else a)
      (if ((((c - r - 16#64).toNat : Int) != ((c - r).toNat : Int) - 16)
        || (c - r - 16#64 == BitVec.zero 64)) = true then r else b) = T := by
  have h1 : r + 1#64 ≠ 0#64 := by bv_omega
  have hn : Flat.isSurplus (flat g1) r = true := by
    have h2 := none_of_z (by rwa [Bool.not_eq_false'] at hd)
    show (Flat.get g1.h.dest r == Flat.NONE) = true
    simpa using h2
  rw [scan_succ _ h1, hn, ite_eq_left rfl] at hs
  rw [if_none, if_reach hc]
  exact hs

-- `subq $1, %rax; cmpq $-1, %rax; je .LB.Emission.removeSurplus.3`: the jump is taken.
theorem sub1_none {r : Word} (h : (r - 1#64 - 18446744073709551615#64 == BitVec.zero 64) = true) :
    r = 0#64 := by
  have := eq_of_z h; bv_omega

-- `subq $1, %rax; cmpq $-1, %rax; je .LB.Emission.removeSurplus.3`: the jump is not taken.
theorem sub1_ne {r : Word} (h : (r - 1#64 - 18446744073709551615#64 == BitVec.zero 64) = false) :
    r ≠ 0#64 := by
  have := ne_of_z h; bv_omega

theorem sub1_lt {r n : Word} (h0 : r ≠ 0#64) (h : r < n) : r - 1#64 < n := by bv_omega

theorem ne_zero_of_lt {r n : Word} (h : r < n) : n ≠ 0#64 := by bv_omega

-- The end of the scan.
theorem scan_end {st : Flat.St} {r a b : Word} {T : Word × Word} (h0 : r = 0#64)
    (hs : Flat.surplusScan st r a b = T) : T = (a, b) := by
  subst h0; rw [scan_zero] at hs; exact hs.symm

-- The scan from `r - 1 + 1`.
theorem scan_pred {st : Flat.St} {r a b : Word} {T : Word × Word}
    (hs : Flat.surplusScan st r a b = T) : Flat.surplusScan st (r - 1#64 + 1#64) a b = T := by
  rwa [show r - 1#64 + 1#64 = r by bv_omega]


/-! The end of the scan at `.LB.Emission.removeSurplus.3`: `sh` is `rdx`, `dp` is `rsi` and `c`
is `rdi`. -/

section
variable {g g1 : G} {sh dp : Word}

theorem rs300_none (hrs : Flat.removeSurplus (flat g) = Flat.removeSurplus (flat g1))
    (h0 : g1.h.len ≠ 0#64)
    (hs : Flat.surplusScan (flat g1) (flat g1).size Flat.NONE Flat.NONE = (sh, dp))
    (hz : (sh - 18446744073709551615#64 == BitVec.zero 64) = true) :
    Flat.removeSurplus (flat g) = (.done, flat g1) := by
  rw [hrs, rs_step (st := flat g1) h0 hs, ite_eq_left (none_of_z hz)]

theorem rs300_block (hrs : Flat.removeSurplus (flat g) = Flat.removeSurplus (flat g1))
    (h0 : g1.h.len ≠ 0#64)
    (hs : Flat.surplusScan (flat g1) (flat g1).size Flat.NONE Flat.NONE = (sh, dp))
    (hz1 : (sh - 18446744073709551615#64 == BitVec.zero 64) = false)
    (hz2 : (dp - 18446744073709551615#64 == BitVec.zero 64) = true) :
    Flat.removeSurplus (flat g) = Flat.blockSwapUnreachable (flat g1) sh := by
  rw [hrs, rs_step (st := flat g1) h0 hs, ite_eq_right (ne_none_of_z hz1),
    ite_eq_left (none_of_z hz2)]

theorem rs300_top {c : Word} (hrs : Flat.removeSurplus (flat g) = Flat.removeSurplus (flat g1))
    (h0 : g1.h.len ≠ 0#64)
    (hs : Flat.surplusScan (flat g1) (flat g1).size Flat.NONE Flat.NONE = (sh, dp))
    (hz1 : (sh - 18446744073709551615#64 == BitVec.zero 64) = false)
    (hz2 : (dp - 18446744073709551615#64 == BitVec.zero 64) = false)
    (he : (c - sh == BitVec.zero 64) = true) (hc : c = g1.h.len - 1#64) :
    Flat.removeSurplus (flat g) = afterPop (flat g1) := by
  rw [hrs, rs_step (st := flat g1) h0 hs, ite_eq_right (ne_none_of_z hz1),
    ite_eq_right (ne_none_of_z hz2)]
  have e : sh = (flat g1).size - 1 := (eq_of_z he).symm.trans hc
  unfold inner
  rw [ite_eq_left e]; exact afterR_done rfl

theorem rs300_eq {c : Word} (hrs : Flat.removeSurplus (flat g) = Flat.removeSurplus (flat g1))
    (h0 : g1.h.len ≠ 0#64)
    (hs : Flat.surplusScan (flat g1) (flat g1).size Flat.NONE Flat.NONE = (sh, dp))
    (hz1 : (sh - 18446744073709551615#64 == BitVec.zero 64) = false)
    (hz2 : (dp - 18446744073709551615#64 == BitVec.zero 64) = false)
    (he : (c - sh == BitVec.zero 64) = false) (hc : c = g1.h.len - 1#64) :
    Flat.removeSurplus (flat g) = afterR (eqStep (flat g1) c (g1.h.len - 1#64) dp) := by
  rw [hrs, rs_step (st := flat g1) h0 hs, ite_eq_right (ne_none_of_z hz1),
    ite_eq_right (ne_none_of_z hz2)]
  have e : ¬sh = (flat g1).size - 1 := fun e => ne_of_z he (hc.trans e.symm)
  subst hc
  unfold inner
  rw [ite_eq_right e] <;> rfl

end
section
variable {S : Addr} {g : G} {F : MProp 64} {s : MachineData} {ra : Int64} {g1 : G} {w : Word}

theorem Run.next {t P : MachineData} (h : Run S g F s ra g1 w t) (hm : P.dmem = t.dmem)
    (hsp : P.regs.rsp = t.regs.rsp) (hbx : P.regs.rbx = t.regs.rbx)
    (hbp : P.regs.rbp = t.regs.rbp) (h12 : P.regs.r12 = t.regs.r12)
    (h13 : P.regs.r13 = t.regs.r13) (h14 : P.regs.r14 = t.regs.r14)
    (h15 : P.regs.r15 = t.regs.r15) : Run S g F s ra g1 w P :=
  ⟨h.bx.next hm hsp hbx hbp h12 h13 h14 h15, h.ok, h.keep, h.dok⟩

/-! The state after a step that keeps `rbx`, `rsp`, `rbp` and `r12`-`r15`. The lemmas state the
next state in the form of the goals of `kvcgen64`, with the kept registers of `t`. Thus the kernel
does not compare the next state with `t`: such a check can unfold `x + BitVec.ofInt 64 (-1)` into a
deep recursion. -/

theorem Bx.upd {t : MachineData} {vax vcx vdx vsi vdi v8 v9 v10 v11 : UInt64} {z : RegZmms}
    {f : StatusFlags} (h : Bx S g1 F s ra w t) :
    Bx S g1 F s ra w (MachineData.mk (Reg64s.mk vax t.regs.rbx vcx vdx vsi vdi t.regs.rsp
      t.regs.rbp v8 v9 v10 v11 t.regs.r12 t.regs.r13 t.regs.r14 t.regs.r15) z f t.dmem) :=
  h.next rfl rfl rfl rfl rfl rfl rfl rfl

theorem Bx.updm {t : MachineData} {g' : G} {m : DataMem}
    {vax vcx vdx vsi vdi v8 v9 v10 v11 : UInt64} {z : RegZmms} {f : StatusFlags}
    (h : Bx S g1 F s ra w t) (hm : (View S g' ∗ Stk (rsp s - 16#64) [] w ∗ Fr s ra F).get m) :
    Bx S g' F s ra w (MachineData.mk (Reg64s.mk vax t.regs.rbx vcx vdx vsi vdi t.regs.rsp
      t.regs.rbp v8 v9 v10 v11 t.regs.r12 t.regs.r13 t.regs.r14 t.regs.r15) z f m) :=
  h.step hm rfl rfl rfl rfl rfl rfl rfl

theorem Run.upd {t : MachineData} {vax vcx vdx vsi vdi v8 v9 v10 v11 : UInt64} {z : RegZmms}
    {f : StatusFlags} (h : Run S g F s ra g1 w t) :
    Run S g F s ra g1 w (MachineData.mk (Reg64s.mk vax t.regs.rbx vcx vdx vsi vdi t.regs.rsp
      t.regs.rbp v8 v9 v10 v11 t.regs.r12 t.regs.r13 t.regs.r14 t.regs.r15) z f t.dmem) :=
  ⟨h.bx.upd, h.ok, h.keep, h.dok⟩

theorem lenAt_mk (S : Addr) (t : MachineData) (r : Reg64s) (z : RegZmms) (f : StatusFlags) :
    lenAt S (MachineData.mk r z f t.dmem) = lenAt S t := rfl

theorem Bx.flags {t : MachineData} {z : RegZmms} {f : StatusFlags} (h : Bx S g1 F s ra w t) :
    Bx S g1 F s ra w (MachineData.mk t.regs z f t.dmem) :=
  h.next rfl rfl rfl rfl rfl rfl rfl rfl

theorem Run.flags {t : MachineData} {z : RegZmms} {f : StatusFlags} (h : Run S g F s ra g1 w t) :
    Run S g F s ra g1 w (MachineData.mk t.regs z f t.dmem) :=
  ⟨h.bx.flags, h.ok, h.keep, h.dok⟩

/-! The invariants of the next block, in the form of the goals of `kvcgen64`. -/

theorem at277_flags {t : MachineData} {z : RegZmms} {f : StatusFlags}
    (hr : Run S g F s ra g1 w t) (hsc : Scan g g1 t) (hlt : t.regs.rax.toBitVec < g1.h.len)
    (hs : Flat.surplusScan (flat g1) t.regs.rax.toBitVec t.regs.rdx.toBitVec t.regs.rsi.toBitVec
      = Flat.surplusScan (flat g1) (flat g1).size Flat.NONE Flat.NONE) :
    At277 S g F s ra (MachineData.mk t.regs z f t.dmem) :=
  ⟨g1, w, hr.flags, hsc, hlt, hs⟩

theorem at277_mk {t : MachineData} {vcx v9 v10 v11 : UInt64} {a b : Word} {z : RegZmms}
    {f : StatusFlags} (hr : Run S g F s ra g1 w t) (hsc : Scan g g1 t)
    (hlt : t.regs.rax.toBitVec < g1.h.len)
    (hs : Flat.surplusScan (flat g1) t.regs.rax.toBitVec a b
      = Flat.surplusScan (flat g1) (flat g1).size Flat.NONE Flat.NONE) :
    At277 S g F s ra (MachineData.mk (Reg64s.mk t.regs.rax t.regs.rbx vcx (UInt64.ofBitVec a)
      (UInt64.ofBitVec b) t.regs.rdi t.regs.rsp t.regs.rbp t.regs.r8 v9 v10 v11 t.regs.r12
      t.regs.r13 t.regs.r14 t.regs.r15) z f t.dmem) :=
  ⟨g1, w, hr.upd, hsc, hlt, hs⟩

theorem at300_mk {t : MachineData} {vax : UInt64} {z : RegZmms} {f : StatusFlags}
    (hr : Run S g F s ra g1 w t) (hsc : Scan g g1 t) (h0 : g1.h.len ≠ 0#64)
    (hs : Flat.surplusScan (flat g1) (flat g1).size Flat.NONE Flat.NONE
      = (t.regs.rdx.toBitVec, t.regs.rsi.toBitVec)) :
    At300 S g F s ra (MachineData.mk (Reg64s.mk vax t.regs.rbx t.regs.rcx t.regs.rdx t.regs.rsi
      t.regs.rdi t.regs.rsp t.regs.rbp t.regs.r8 t.regs.r9 t.regs.r10 t.regs.r11 t.regs.r12
      t.regs.r13 t.regs.r14 t.regs.r15) z f t.dmem) :=
  ⟨g1, w, hr.upd, hsc, h0, hs⟩

theorem at279_mk {t : MachineData} {a : Word} {z : RegZmms} {f : StatusFlags}
    (hr : Run S g F s ra g1 w t) (hsc : Scan g g1 t) (hlt : a < g1.h.len)
    (hs : Flat.surplusScan (flat g1) (a + 1#64) t.regs.rdx.toBitVec t.regs.rsi.toBitVec
      = Flat.surplusScan (flat g1) (flat g1).size Flat.NONE Flat.NONE) :
    At279 S g F s ra (MachineData.mk (Reg64s.mk (UInt64.ofBitVec a) t.regs.rbx t.regs.rcx
      t.regs.rdx t.regs.rsi t.regs.rdi t.regs.rsp t.regs.rbp t.regs.r8 t.regs.r9 t.regs.r10
      t.regs.r11 t.regs.r12 t.regs.r13 t.regs.r14 t.regs.r15) z f t.dmem) :=
  ⟨g1, w, hr.upd, hsc, hlt, hs⟩


-- The precondition of `pop` at `.LB.Emission.removeSurplus.12`.
theorem popA_of {g2 : G} {c : MachineData}
    (hb : g2.h.nops.toNat + 2 * g2.h.len.toNat ≤ 6 * g2.h.n.toNat + g2.xo + 1)
    (hd : DestOk (flat g2)) : popA g2 c :=
  ⟨fun h0 => by bv_omega, hd⟩

-- A `pop` that is done keeps the budget of the next pass.
theorem budget_pop {g2 g3 : G} (hok2 : g2.Ok) (hok3 : g3.Ok) (hK : Keep g2 g3)
    (hf : flat g3 = (Flat.pop (flat g2)).2) (hd : (Flat.pop (flat g2)).1 = .done)
    (hb : g2.h.nops.toNat + 2 * g2.h.len.toNat ≤ 6 * g2.h.n.toNat + g2.xo + 1) : Budget g3 := by
  obtain ⟨h0, hs, -, -, ht⟩ := pop_done hd
  have e1 := trace_len hok3
  rw [hf, ht, List.length_append, trace_len hok2] at e1
  have e3 : g3.h.len = g2.h.len - 1 := (congrArg Flat.St.size hf).trans hs
  change g2.h.len ≠ 0 at h0
  unfold Budget
  rw [hK.n, hK.xo, e3]
  simp only [List.length_singleton] at e1
  bv_omega

-- A `pop` that is done removes one slot.
theorem len_pop {g2 g3 : G} (hf : flat g3 = (Flat.pop (flat g2)).2)
    (hd : (Flat.pop (flat g2)).1 = .done) : g3.h.len.toNat + 1 = g2.h.len.toNat := by
  obtain ⟨h0, hs, -⟩ := pop_done hd
  have e3 : g3.h.len = g2.h.len - 1 := (congrArg Flat.St.size hf).trans hs
  change g2.h.len ≠ 0 at h0
  rw [e3]; bv_omega

-- The precondition of `swapWith` at `.LB.Emission.removeSurplus.11`.
theorem swapA_of {g1 : G} {c : MachineData} (hb : Budget g1) (h0 : g1.h.len ≠ 0#64)
    (hd : DestOk (flat g1)) : swapWithA g1 c :=
  ⟨by unfold Budget at hb; bv_omega, hd⟩

-- A `swapWith` that is done adds one record and keeps the size.
theorem swap_rec {g1 g3 : G} {p : Word} (hok1 : g1.Ok) (hok3 : g3.Ok) (hK : Keep g1 g3)
    (hf : flat g3 = (Flat.swapWith (flat g1) p).2) (hd : (Flat.swapWith (flat g1) p).1 = .done) :
    g3.h.nops.toNat = g1.h.nops.toNat + 1 ∧ g3.h.len = g1.h.len ∧ g3.h.n = g1.h.n := by
  obtain ⟨-, e⟩ := swap_done hd
  have e1 := trace_len hok3
  rw [hf, e] at e1
  simp only [Flat.swapDestinations, Flat.stackSwap, List.length_append, List.length_singleton,
    trace_len hok1] at e1
  exact ⟨e1.symm, (congrArg Flat.St.size hf).trans (Flat.swapWith_size _ _), hK.n⟩

theorem at283_mk {t : MachineData} {vax vcx vdx vsi vdi v8 v9 v10 v11 : UInt64} {z : RegZmms}
    {f : StatusFlags} (hr : Run S g F s ra g1 w t) (hbud : Budget g1) (h0 : g1.h.len ≠ 0#64)
    (hdi : vdi.toBitVec = g1.h.len - 1#64) (h8 : v8.toBitVec = vdi.toBitVec * 8#64)
    (hax : vax.toBitVec ≤ vdi.toBitVec)
    (hrs : Flat.removeSurplus (flat g)
      = afterR (eqStep (flat g1) vax.toBitVec (g1.h.len - 1#64) vsi.toBitVec)) :
    At283 S g F s ra (MachineData.mk (Reg64s.mk vax t.regs.rbx vcx vdx vsi vdi t.regs.rsp
      t.regs.rbp v8 v9 v10 v11 t.regs.r12 t.regs.r13 t.regs.r14 t.regs.r15) z f t.dmem) :=
  ⟨g1, w, hr.upd, hbud, h0, hdi, h8, hax, hrs⟩
end

-- The facts of `.LB.Emission.removeSurplus.4` for `rax ≠ 0`: `q` is `rax`, `d` is `rdi`.
theorem at283_facts {g1 : G} {q d : Word} (hok : g1.Ok) (h0 : g1.h.len ≠ 0#64) (hq : q ≠ 0#64)
    (hax : q ≤ d) (hdi : d = g1.h.len - 1#64) :
    (q - 1#64).toNat < maxStackSize ∧ (q - 1#64).toNat < g1.h.n.toNat + g1.xs ∧ d.toNat < maxStackSize
      ∧ d.toNat < g1.h.n.toNat + g1.xs ∧ q - 1#64 + 1#64 < g1.h.len ∧ q.toNat ≤ maxStackSize
      ∧ q - 1#64 < (flat g1).size ∧ d < (flat g1).size ∧ (flat g1).size.toNat ≤ maxStackSize := by
  have hl := hok.len
  have hn := hok.n
  have hx := hok.xs
  show _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ q - 1#64 < g1.h.len ∧ d < g1.h.len ∧ g1.h.len.toNat ≤ maxStackSize
  subst hdi
  simp only [maxStackSize] at *
  bv_omega

theorem nb {b : Bool} (h : (!b) = true) : b = false := by simpa using h
theorem nb' {b : Bool} (h : (!b) = false) : b = true := by simpa using h

section
variable {r : Flat.Status × Flat.St} {g1 : G} {q d dp : Word}

-- `jne .LB.Emission.removeSurplus.4` after `cmpq $-1`: slot `q - 1` is not surplus.
theorem rs283_dest (hrs : r = afterR (eqStep (flat g1) q (g1.h.len - 1#64) dp)) (hq : q ≠ 0#64)
    (hne : Flat.get g1.h.dest (q - 1#64) ≠ Flat.NONE) :
    r = afterR (eqStep (flat g1) (q - 1#64) (g1.h.len - 1#64) dp) := by
  have hn : ¬(Flat.isSurplus (flat g1) (q - 1#64) = true
      ∧ Flat.get (flat g1).data (q - 1#64) = Flat.get (flat g1).data ((flat g1).size - 1#64)) :=
    fun h => hne (beq_iff_eq.mp h.1)
  rw [hrs, eqStep_skip hq hn]

-- `jne .LB.Emission.removeSurplus.4` after `salq $16`: the slots `q - 1` and `d` differ.
theorem rs283_data (hrs : r = afterR (eqStep (flat g1) q (g1.h.len - 1#64) dp)) (hq : q ≠ 0#64)
    (hdi : d = g1.h.len - 1#64)
    (hne : Flat.get (flat g1).data d ≠ Flat.get (flat g1).data (q - 1#64)) :
    r = afterR (eqStep (flat g1) (q - 1#64) (g1.h.len - 1#64) dp) := by
  subst hdi
  rw [hrs, eqStep_skip hq (fun h => hne h.2.symm)]

-- No jump: slot `q - 1` is surplus and equal to slot `d`.
theorem rs283_hit (hrs : r = afterR (eqStep (flat g1) q (g1.h.len - 1#64) dp)) (hq : q ≠ 0#64)
    (hqN : q.toNat ≤ maxStackSize) (hdi : d = g1.h.len - 1#64)
    (hs : Flat.get g1.h.dest (q - 1#64) = Flat.NONE)
    (he : Flat.get (flat g1).data d = Flat.get (flat g1).data (q - 1#64)) :
    r = afterPop (Flat.swapDestinations (flat g1) (q - 1#64) d) := by
  subst hdi
  rw [hrs, eqStep_hit hq hqN ⟨beq_iff_eq.mpr hs, he.symm⟩, afterR_done rfl]

theorem sd_none {a b : Word} (hz : Flat.get (dsw (flat g1) a b).dest a = Flat.NONE) :
    Flat.swapDestinations (flat g1) a b = posAt (flat (withDest g1 (dsw (flat g1) a b).dest)) b := by
  rw [swapDestinations_eq, posAt_none hz]; rfl

theorem sd_some {a b : Word} (hz : Flat.get (dsw (flat g1) a b).dest a ≠ Flat.NONE) :
    Flat.swapDestinations (flat g1) a b = posAt (flat (withPos (withDest g1 (dsw (flat g1) a b).dest)
      (Flat.put g1.h.pos (Flat.get (dsw (flat g1) a b).dest a) a))) b := by
  rw [swapDestinations_eq, posAt_some hz]; rfl

end

end Surplus

/-- `Run.next` with a reducible `rfl` for each equation, as `mid_next%` in `Generate.lean`. -/
local macro "run_next% " h:term:max : term =>
  `(Surplus.Run.next $h (by with_reducible rfl) (by with_reducible rfl) (by with_reducible rfl)
    (by with_reducible rfl) (by with_reducible rfl) (by with_reducible rfl)
    (by with_reducible rfl) (by with_reducible rfl))

/-- `Bx.next` with a reducible `rfl` for each equation. -/
local macro "bx_next% " h:term:max : term =>
  `(Surplus.Bx.next $h (by with_reducible rfl) (by with_reducible rfl) (by with_reducible rfl)
    (by with_reducible rfl) (by with_reducible rfl) (by with_reducible rfl)
    (by with_reducible rfl) (by with_reducible rfl))

/-- `Bx.step` with a reducible `rfl` for each register equation. -/
local macro "bx_step% " h:term:max hm:term:max : term =>
  `(Surplus.Bx.step $h $hm (by with_reducible rfl) (by with_reducible rfl)
    (by with_reducible rfl) (by with_reducible rfl) (by with_reducible rfl) (by with_reducible rfl)
    (by with_reducible rfl))

namespace Surplus
open Generate

def Inv (S : Addr) (g : G) (F : MProp 64) (s : MachineData) (ra : Int64) :
    CfgLabel → MachineData → Prop
  | .entry, t => t = s.pushRa ra
  | .label "_ZN12_GLOBAL__N_18Emission13removeSurplusEv", t => t = s.pushRa ra
  | .label ".LB.Emission.removeSurplus.0", t => At276 S g (Extras s F) s ra t
  | .label ".LB.Emission.removeSurplus.1", t => At277 S g (Extras s F) s ra t
  | .label ".LB.Emission.removeSurplus.2", t => At279 S g (Extras s F) s ra t
  | .label ".LB.Emission.removeSurplus.3", t => At300 S g (Extras s F) s ra t
  | .label ".LB.Emission.removeSurplus.4", t => At283 S g (Extras s F) s ra t
  | .label ".LB.Emission.removeSurplus.5", t => At289 S g (Extras s F) s ra t
  | .label ".LB.Emission.removeSurplus.6", t => At281 S g (Extras s F) s ra t
  | .label ".LB.Emission.removeSurplus.7", t => AtFail S g (Extras s F) s ra t
  | .label ".LB.Emission.removeSurplus.8", t => AtDone S g (Extras s F) s ra t
  | .label ".LB.Emission.removeSurplus.9", t => At275 S g (Extras s F) s ra t
  | .label ".LB.Emission.removeSurplus.10", t => AtDone S g (Extras s F) s ra t
  | .label ".LB.Emission.removeSurplus.11", t => At301 S g (Extras s F) s ra t
  | .label ".LB.Emission.removeSurplus.12", t => At282 S g (Extras s F) s ra t
  | _, _ => False

def V (S : Addr) (l : Label) (t : MachineData) : Nat :=
  match l with
  | "_ZN12_GLOBAL__N_18Emission13removeSurplusEv" => 2 ^ 200
  | ".LB.Emission.removeSurplus.0" => lenAt S t * wB + (wB - 1)
  | ".LB.Emission.removeSurplus.1" => lenAt S t * wB + wH + 2 * t.regs.rax.toBitVec.toNat + 2
  | ".LB.Emission.removeSurplus.2" => lenAt S t * wB + wH + 2 * t.regs.rax.toBitVec.toNat + 3
  | ".LB.Emission.removeSurplus.3" => lenAt S t * wB + wH
  | ".LB.Emission.removeSurplus.4" => lenAt S t * wB + t.regs.rax.toBitVec.toNat + 2
  | ".LB.Emission.removeSurplus.5" => lenAt S t * wB + 2
  | ".LB.Emission.removeSurplus.6" => 1
  | ".LB.Emission.removeSurplus.7" => 0
  | ".LB.Emission.removeSurplus.8" => 1
  | ".LB.Emission.removeSurplus.9" => 0
  | ".LB.Emission.removeSurplus.10" => 1
  | ".LB.Emission.removeSurplus.11" => lenAt S t * wB + 1
  | ".LB.Emission.removeSurplus.12" => lenAt S t * wB + 1
  | _ => 0

def E [Host] (S : Addr) (g : G) (F : MProp 64) (s : MachineData) (ra : Int64)
    (a : Int64) (t : MachineData) : Prop :=
  (a = ra ∧ Sep.Post S F 4 (fun g' t => surplusQ g g' s t) s t ∧ Sep.mod.Agree s t) ∨
    (a = label "exit" ∧ t.regs.get64 .rdi = 1#64 ∧
      Sep.Post S F 4 (fun g' t => surplusX g g' s t) s t)

def Obl [Host] [FunDecls] (S : Addr) (g : G) (F : MProp 64) (s : MachineData) (ra : Int64)
    (blk : Program.Block) : Prop :=
  ∀ t, Inv S g F s ra blk.label t →
    let I' (c : CfgLabel) (j : Nat) (_ : Unit) (u : MachineData) :=
      Inv S g F s ra c u ∧ Program.Decreases (V S) blk.label blk.idx t c j u
    WP.wp blk.body (I' blk.next (blk.idx + 1))
      (Program.Intercept (Program.labels removeSurplusAsm) (s.pushRa ra) I' (E S g F s ra)) t

section
variable [Host] [FunDecls] (S : Addr) (g : G) (F : MProp 64) (s : MachineData) (ra : Int64)


theorem b_entry
    : removeSurplusAsm.ForallBlocks fun blk =>
      blk.label = .entry → Obl S g F s ra blk := by
  cfg_block [Obl, Inv, V, Names.removeSurplus]
  intro t ht
  subst ht; kvcgen64

theorem b_fn
    (hpre : Sep.Pre S g F surplusA 4 s)
    : removeSurplusAsm.ForallBlocks fun blk =>
      blk.label = .label Names.removeSurplus → Obl S g F s ra blk := by
  cfg_block [Obl, Inv, V, Names.removeSurplus]
  intro t ht
  have hpre2 := extras_pre hpre
  obtain ⟨fr, v, hfr, hm⟩ := hpre2.mem
  obtain ⟨w, x, rfl⟩ := split2 hfr
  have hk0 : Kp S g (Extras s F) s ra [w, x] (s.pushRa ra) := Kp.init hm
  subst ht
  have hS : (s.pushRa ra).regs.rdi.toBitVec = S := by simpa [MachineData.pushRa] using hpre.rdi
  have hsp : (s.pushRa ra).regs.rsp.toBitVec = rsp s - 8#64 := by simp [MachineData.pushRa]
  kvcgen64
  all_goals try symexec_norm
  vc_by_shape
  | load => exact push_isSome hk0.mem hsp
  | other =>
    first
    | exact ⟨g, w, ⟨Bx.push hk0.mem hsp (by rw [hk0.bx]) rfl hS hk0.bp hk0.r12 hk0.r13 hk0.r14
        hk0.r15, hpre.ok, Keep.refl g, hpre.args.2⟩, hpre.args.1, rfl⟩
    | (left; simp only [V, wB]; unfold lenAt; omega)

theorem b_0
    : removeSurplusAsm.ForallBlocks fun blk =>
      blk.label = .label ".LB.Emission.removeSurplus.0" → Obl S g F s ra blk := by
  cfg_block [Obl, Inv, V, Names.removeSurplus]
  intro t ht
  obtain ⟨g1, w1, hr, hbud, hrs⟩ := ht
  have hm1 := hr.bx.mem
  have hl1 : lenAt S t = g1.h.len.toNat := hr.bx.lenAt
  kvcgen64
  all_goals try symexec_norm
  all_goals simp only [hr.bx.bx, rd_len' hm1] at *
  vc_by_shape
  | load => exact isSome_len' hm1
  | goto ".LB.Emission.removeSurplus.10" =>
    have h0 := ShallowestCopy.zf_true (by with_reducible assumption)
    cfg_goto
    · exact hr.bx.upd.stack
    · simp only
      exact ⟨g1, w1, hr.upd, hrs.trans (rs_zero (st := flat g1) h0)⟩
    · simp only [V, wB]
      left; omega
  | goto ".LB.Emission.removeSurplus.2" =>
    have h0 := ShallowestCopy.zf_false (by with_reducible assumption)
    cfg_goto
    · exact hr.bx.upd.stack
    · simp only
      refine ⟨g1, w1, hr.upd, ⟨hbud, hrs, rfl, Generate.add_neg_one _⟩, ?_, ?_⟩
      · exact pred_lt h0
      · show Flat.surplusScan (flat g1) (g1.h.len + BitVec.ofInt 64 (-1) + 1#64)
          18446744073709551615#64 18446744073709551615#64 = _
        rw [pred_succ, none_lit]; rfl
    · simp only [V, wB, wH]
      rw [lenAt_mk]
      left
      have := (g1.h.len + BitVec.ofInt 64 (-1)).isLt
      omega

theorem b_1
    : removeSurplusAsm.ForallBlocks fun blk =>
      blk.label = .label ".LB.Emission.removeSurplus.1" → Obl S g F s ra blk := by
  cfg_block [Obl, Inv, V, Names.removeSurplus]
  intro t ht
  obtain ⟨g1, w1, hr, hsc, hlt, hs⟩ := ht
  kvcgen64
  all_goals try symexec_norm
  vc_by_shape
  | goto ".LB.Emission.removeSurplus.3" =>
    rename_i hz
    have h0 := sub1_none hz
    cfg_goto
    · exact hr.bx.upd.stack
    · simp only
      exact at300_mk hr hsc (ne_zero_of_lt hlt) (scan_end h0 hs)
    · simp only [V, wB, wH]
      rw [lenAt_mk]
      left; omega
  | other =>
    rename_i hz
    have h0 := sub1_ne hz
    first
    | exact at279_mk hr hsc (sub1_lt h0 hlt) (scan_pred hs)
    | (left; simp only [V, wB, wH]; rw [lenAt_mk]; have := ShallowestCopy.pred_toNat h0; omega)

theorem b_2
    : removeSurplusAsm.ForallBlocks fun blk =>
      blk.label = .label ".LB.Emission.removeSurplus.2" → Obl S g F s ra blk := by
  cfg_block [Obl, Inv, V, Names.removeSurplus]
  intro t ht
  obtain ⟨g1, w1, hr, ⟨hbud, hrs, hr8, hdi⟩, hlt, hsc⟩ := ht
  have hm1 := hr.bx.mem
  have hl1 : lenAt S t = g1.h.len.toNat := hr.bx.lenAt
  have hax : t.regs.rax.toBitVec.toNat < maxStackSize := by
    have := hr.ok.len; have := hr.ok.n; have := hr.ok.xs; have := BitVec.lt_def.mp hlt; omega
  kvcgen64
  all_goals try symexec_norm
  all_goals simp only [hr.bx.bx, rd_dest_get hm1 hax] at *
  vc_by_shape
  | load => exact isSome_dest' hm1 hax
  | goto ".LB.Emission.removeSurplus.1" =>
    rename_i hd
    cfg_goto
    · first | exact hr.bx.flags.stack | exact hr.bx.upd.stack
    · simp only
      first
      | exact at277_flags hr ⟨hbud, hrs, hr8, hdi⟩ hlt
          (scan279_ne hlt hd hsc)
      | exact at277_mk hr ⟨hbud, hrs, hr8, hdi⟩ hlt
          (scan279_hit hlt hdi hd hsc)
    · simp only [V, wB, wH]
      rw [lenAt_mk]
      left
      omega

theorem b_3
    : removeSurplusAsm.ForallBlocks fun blk =>
      blk.label = .label ".LB.Emission.removeSurplus.3" → Obl S g F s ra blk := by
  cfg_block [Obl, Inv, V, Names.removeSurplus]
  intro t ht
  obtain ⟨g1, w1, hr, ⟨hbud, hrs, hr8, hdi⟩, h0, hs⟩ := ht
  kvcgen64
  all_goals try symexec_norm
  vc_by_shape
  | goto ".LB.Emission.removeSurplus.8" =>
    have hz : (t.regs.rdx.toBitVec - 18446744073709551615#64 == BitVec.zero 64) = true := by
      assumption
    cfg_goto
    · exact hr.bx.flags.stack
    · simp only
      exact ⟨g1, w1, hr.flags, rs300_none hrs h0 hs hz⟩
    · simp only [V, wB, wH]
      left; omega
  | goto ".LB.Emission.removeSurplus.6" =>
    have hz1 : (t.regs.rdx.toBitVec - 18446744073709551615#64 == BitVec.zero 64) = false := by
      assumption
    have hz2 : (t.regs.rsi.toBitVec - 18446744073709551615#64 == BitVec.zero 64) = true := by
      assumption
    cfg_goto
    · exact hr.bx.flags.stack
    · simp only
      exact ⟨g1, w1, hr.flags, hr8, rs300_block hrs h0 hs hz1 hz2⟩
    · simp only [V, wB, wH]
      left; omega
  | goto ".LB.Emission.removeSurplus.12" =>
    have hz1 : (t.regs.rdx.toBitVec - 18446744073709551615#64 == BitVec.zero 64) = false := by
      assumption
    have hz2 : (t.regs.rsi.toBitVec - 18446744073709551615#64 == BitVec.zero 64) = false := by
      assumption
    have he : (t.regs.rdi.toBitVec - t.regs.rdx.toBitVec == BitVec.zero 64) = true := by
      have hz : (t.regs.rdx.toBitVec - t.regs.rdi.toBitVec == BitVec.zero 64) = true := by
        assumption
      rw [BitVec.zero_eq, Idioms.sub_beq_zero, beq_iff_eq]
      exact (eq_of_z hz).symm
    cfg_goto
    · exact hr.bx.flags.stack
    · simp only
      exact ⟨g1, w1, hr.flags, Nat.le_succ_of_le hbud, rs300_top hrs h0 hs hz1 hz2 he hdi⟩
    · simp only [V, wB, wH]
      rw [lenAt_mk]
      left; omega
  | other =>
    have hz1 : (t.regs.rdx.toBitVec - 18446744073709551615#64 == BitVec.zero 64) = false := by
      assumption
    have hz2 : (t.regs.rsi.toBitVec - 18446744073709551615#64 == BitVec.zero 64) = false := by
      assumption
    have he : (t.regs.rdi.toBitVec - t.regs.rdx.toBitVec == BitVec.zero 64) = false := by
      have hz : (t.regs.rdx.toBitVec - t.regs.rdi.toBitVec == BitVec.zero 64) = false := by
        assumption
      rw [BitVec.zero_eq, Idioms.sub_beq_zero, beq_eq_false_iff_ne]
      exact (ne_of_z hz).symm
    first
    | exact at283_mk hr hbud h0 hdi rfl (BitVec.le_refl _) (rs300_eq hrs h0 hs hz1 hz2 he hdi)
    | (left; simp only [V, wB, wH]; rw [lenAt_mk]; have := t.regs.rdi.toBitVec.isLt; omega)

theorem b_4
    : removeSurplusAsm.ForallBlocks fun blk =>
      blk.label = .label ".LB.Emission.removeSurplus.4" → Obl S g F s ra blk := by
  cfg_block [Obl, Inv, V, Names.removeSurplus]
  intro t ht
  obtain ⟨g1, w1, hr, hbud, h0, hdi, hr8, hax, hrs⟩ := ht
  have hm1 := hr.bx.mem
  kvcgen64
  all_goals try symexec_norm
  all_goals try simp only [hr.bx.bx, rd_data' hm1] at *
  all_goals try (
    have hq : t.regs.rax.toBitVec ≠ 0#64 := ShallowestCopy.zf_false (by with_reducible assumption)
    obtain ⟨ha, han, hb, hbn, h1, hqN, hal, hbl, hN⟩ := at283_facts hr.ok h0 hq hax hdi
    obtain ⟨-, -, hda, hdb⟩ := lb52_facts hr.ok ha h1 hdi hr.dok
    have h1' := store_dest_put hm1 ha (Flat.get g1.h.dest t.regs.rdi.toBitVec)
    have h2' : (View S (withDest g1
        (dsw (flat g1) (t.regs.rax.toBitVec - 1#64) t.regs.rdi.toBitVec).dest) ∗ _).get _ :=
      store_dest_put h1' hb (Flat.get g1.h.dest (t.regs.rax.toBitVec - 1#64)))
  all_goals try simp only [rd_dest_get hm1 ha, rd_dest_get hm1 hb] at *
  all_goals try simp only [rd_dest_get h2' ha, withDest_dest] at *
  vc_by_shape
  | load =>
    first
    | with_reducible exact isSome_dest' hm1 ha
    | with_reducible exact isSome_data' hm1
    | with_reducible exact isSome_slot' hm1 han
    | (rw [hr8]; with_reducible exact isSome_slot' hm1 hbn)
    | with_reducible exact isSome_dest' hm1 hb
    | with_reducible exact isSome_dest' h1' hb
    | with_reducible exact isSome_dest' h2' ha
    | with_reducible exact isSome_pos' h2' (hda.resolve_left (ne_none_of_z (by with_reducible assumption)))
  | goto ".LB.Emission.removeSurplus.11" =>
    have hq0 := ShallowestCopy.zf_true (by with_reducible assumption)
    cfg_goto
    · exact hr.bx.flags.stack
    · simp only
      exact ⟨g1, w1, hr.flags, hbud, h0, by rw [hrs, hq0, eqStep_zero]⟩
    · simp only [V, wB]
      left; rw [lenAt_mk]; omega
  | goto ".LB.Emission.removeSurplus.4" =>
    first
    | have hne := ne_none_of_z (nb (by with_reducible assumption))
      cfg_goto
      · exact hr.bx.upd.stack
      · simp only
        exact at283_mk hr hbud h0 hdi hr8 (by bv_omega) (rs283_dest hrs hq hne)
      · simp only [V, wB]
        left; rw [lenAt_mk]; have := ShallowestCopy.pred_toNat hq; omega
    | have hne := data_ne hm1 hr.ok hbn han (nb (by rw [← hr8]; with_reducible assumption))
      cfg_goto
      · exact hr.bx.upd.stack
      · simp only
        exact at283_mk hr hbud h0 hdi hr8 (by bv_omega) (rs283_data hrs hq hdi hne)
      · simp only [V, wB]
        left; rw [lenAt_mk]; have := ShallowestCopy.pred_toNat hq; omega
  | goto ".LB.Emission.removeSurplus.5" =>
    have hs := none_of_z (nb' (by with_reducible assumption))
    have he := data_eq hm1 hr.ok hbn han (nb' (by rw [← hr8]; with_reducible assumption))
    have hz := none_of_z (by with_reducible assumption)
    have hh := rs283_hit hrs hq hqN hdi hs he
    cfg_goto
    · exact (hr.bx.updm h2').stack
    · simp only
      exact ⟨_, w1, ⟨hr.bx.updm h2', Ok.withDest hr.ok _,
        ProduceProof.Keep.trans hr.keep (Keep.withDest _),
        destOk_withDest (destOk_dsw hr.dok hN hal hbl)⟩,
        hbud, hb, hdb, by rw [hh, sd_none hz]⟩
    · simp only [V, wB]
      left
      rw [(hr.bx.updm h2').lenAt, hr.bx.lenAt]
      have := ShallowestCopy.pred_toNat hq
      show g1.h.len.toNat * wB + 2 < g1.h.len.toNat * wB + t.regs.rax.toBitVec.toNat + 2
      omega
  | closed => simp
  | other =>
    first
    | decide
    | have hs := none_of_z (nb' (by with_reducible assumption))
      have he := data_eq hm1 hr.ok hbn han (nb' (by rw [← hr8]; with_reducible assumption))
      have hz := ne_none_of_z (by with_reducible assumption)
      have hh := rs283_hit hrs hq hqN hdi hs he
      have h3' : (View S (withPos (withDest g1
          (dsw (flat g1) (t.regs.rax.toBitVec - 1#64) t.regs.rdi.toBitVec).dest)
          (Flat.put g1.h.pos (Flat.get (dsw (flat g1) (t.regs.rax.toBitVec - 1#64)
            t.regs.rdi.toBitVec).dest (t.regs.rax.toBitVec - 1#64)) (t.regs.rax.toBitVec - 1#64)))
          ∗ _).get _ :=
        store_pos_put h2' (hda.resolve_left hz) (t.regs.rax.toBitVec - 1#64)
      first
      | exact ⟨_, w1, ⟨hr.bx.updm h3', Ok.withPos (Ok.withDest hr.ok _) _,
          ProduceProof.Keep.trans hr.keep (ProduceProof.Keep.trans (Keep.withDest _) (Keep.withPos _)),
          destOk_withPos (destOk_withDest (destOk_dsw hr.dok hN hal hbl))⟩, hbud, hb, hdb, by rw [hh, sd_some hz]⟩
      | (left
         simp only [V, wB]
         rw [(hr.bx.updm h3').lenAt, hr.bx.lenAt]
         have := ShallowestCopy.pred_toNat hq
         show g1.h.len.toNat * wB + 2 < g1.h.len.toNat * wB + t.regs.rax.toBitVec.toNat + 2
         omega)

theorem b_5
    : removeSurplusAsm.ForallBlocks fun blk =>
      blk.label = .label ".LB.Emission.removeSurplus.5" → Obl S g F s ra blk := by
  cfg_block [Obl, Inv, V, Names.removeSurplus]
  intro t ht
  obtain ⟨g2, w2, hr, hbud, hi, hd, hrs⟩ := ht
  have hm2 := hr.bx.mem
  have hl2 : lenAt S t = g2.h.len.toNat := hr.bx.lenAt
  unfold Budget at hbud
  kvcgen64
  all_goals try symexec_norm
  all_goals simp only [hr.bx.bx, rd_dest_get hm2 hi] at *
  vc_by_shape
  | load =>
    first
    | with_reducible exact isSome_dest' hm2 hi
    | with_reducible exact isSome_pos' hm2 (hd.resolve_left (ne_none_of_z (by with_reducible assumption)))
  | goto ".LB.Emission.removeSurplus.12" =>
    first
    | have hz := none_of_z (by with_reducible assumption)
      cfg_goto
      · exact (bx_next% hr.bx).stack
      · simp only
        exact ⟨g2, w2, run_next% hr, Nat.le_succ_of_le hbud, by rw [hrs, posAt_none hz]⟩
      · simp only [V, wB]
        left
        rw [lenAt_mk, hl2]
        omega
    | have hz := ne_none_of_z (by with_reducible assumption)
      have hdn := hd.resolve_left hz
      have hm3 := store_pos_put hm2 hdn t.regs.rdi.toBitVec
      cfg_goto
      · exact (hr.bx.updm hm3).stack
      · simp only
        exact ⟨_, w2, ⟨hr.bx.updm hm3, Ok.withPos hr.ok _, ProduceProof.Keep.trans hr.keep (Keep.withPos _),
          hr.dok⟩, Nat.le_succ_of_le hbud, by rw [hrs, posAt_some hz]; rfl⟩
      · simp only [V, wB]
        left
        rw [(hr.bx.updm hm3).lenAt, hr.bx.lenAt]
        exact Nat.add_lt_add_left (by decide) _

theorem b_6
    : removeSurplusAsm.ForallBlocks fun blk =>
      blk.label = .label ".LB.Emission.removeSurplus.6" → Obl S g F s ra blk := by
  cfg_block [Obl, Inv, V, Names.removeSurplus]
  intro t ht
  obtain ⟨g1, w1, hr, hr8, hrs⟩ := ht
  have hm1 := hr.bx.mem
  kvcgen64
  all_goals try symexec_norm
  all_goals try simp only [hr.bx.bx] at ⊢
  vc_by_shape
  | goto ".LB.Emission.removeSurplus.7" =>
    have hz : (t.regs.r8.toBitVec - 17#64 - t.regs.rdx.toBitVec == BitVec.zero 64) = true := by
      assumption
    rw [hr8] at hz
    have hz0 : Flat.depthOf (flat g1) t.regs.rdx.toBitVec - Flat.maxSwapDepth = 0 :=
      (Surplus.exc_eq (flat g1) _).symm.trans (beq_iff_eq.mp hz)
    have hb : Flat.removeSurplus (flat g) = (.assertionFailed, flat g1) := by
      rw [hrs, Flat.blockSwapUnreachable, ProduceProof.block_zero hz0]
    cfg_goto
    · exact hr.bx.upd.stack
    · simp only
      refine ⟨g1, w1, hr.bx.upd, hr.ok, hr.keep, ?_, ?_⟩
      · rw [hb]
      · rw [hb]
    · simp only [V]
      left; omega
  | goto ".LB.Emission.removeSurplus.9" =>
    have hz : (t.regs.r8.toBitVec - 17#64 - t.regs.rdx.toBitVec == BitVec.zero 64) = false := by
      assumption
    rw [hr8] at hz
    have hne : Flat.depthOf (flat g1) t.regs.rdx.toBitVec - Flat.maxSwapDepth ≠ 0 := by
      rw [← Surplus.exc_eq]; exact beq_eq_false_iff_ne.mp hz
    have hm3 := ProduceProof.store_exc' (ProduceProof.store_off' hm1 t.regs.rdx.toBitVec)
      (g1.h.len - 17#64 - t.regs.rdx.toBitVec)
    have hb : Flat.removeSurplus (flat g) = (.blocked, flat (ProduceProof.withExc
        (ProduceProof.withOff g1 t.regs.rdx.toBitVec) (g1.h.len - 17#64 - t.regs.rdx.toBitVec))) := by
      rw [hrs, Flat.blockSwapUnreachable, ProduceProof.block_ne hne, ProduceProof.flat_withBlk,
        ← Surplus.exc_eq]
      rfl
    simp only [hr8]
    cfg_goto
    · exact (hr.bx.updm hm3).stack
    · simp only
      exact ⟨_, w1, hr.bx.updm hm3, ProduceProof.Ok.withBlk hr.ok _ _,
        ⟨ProduceProof.Keep.trans hr.keep (ProduceProof.Keep.withBlk _ _),
          by rw [hb], by rw [hb]; rfl⟩, by change 1#8 ≠ 2#8; decide⟩
    · simp only [V]
      left; omega
  | load =>
    first
    | with_reducible exact ProduceProof.isSome_off' hm1
    | with_reducible exact ProduceProof.isSome_exc' (ProduceProof.store_off' hm1 _)

theorem b_7
    (hexit : FunDecls.at (label "exit") = none)
    (hout : ∀ l ∈ Program.labels removeSurplusAsm, label l ≠ label "exit")
    : removeSurplusAsm.ForallBlocks fun blk =>
      blk.label = .label ".LB.Emission.removeSurplus.7" → Obl S g F s ra blk := by
  have he := ProofKit.external_call_spec "exit" hexit
  cfg_block [Obl, Inv, V, Names.removeSurplus]
  intro t ht
  obtain ⟨g1, w1, hb, hok1, hx⟩ := ht
  kvcgen64 [he]
  all_goals symexec_norm
  vc_by_shape
  | load =>
    rw [hb.sp]
    exact isSome_of_eq w1 hb.mem (by unfold Stk; ecancel)
  | jumpOut =>
    rename_i exitra
    apply ProofKit.intercept_exit (E := E S g F s ra) hout
    refine Or.inr ⟨rfl, rfl, hb.exitPost hok1 exitra rfl ?_⟩
    exact hx

theorem b_8
    : removeSurplusAsm.ForallBlocks fun blk =>
      blk.label = .label ".LB.Emission.removeSurplus.8" → Obl S g F s ra blk := by
  cfg_block [Obl, Inv, V, Names.removeSurplus]
  intro t ht
  obtain ⟨g1, w1, hr, hrs⟩ := ht
  kvcgen64
  all_goals try symexec_norm
  vc_by_shape
  | other =>
    first
    | exact ⟨g1, w1, hr.bx.upd, hr.ok, ⟨hr.keep, by rw [hrs], by rw [hrs]; rfl⟩,
        by change 0#8 ≠ 2#8; decide⟩
    | (left; simp only [V]; omega)
  | closed => simp

theorem b_9
    : removeSurplusAsm.ForallBlocks fun blk =>
      blk.label = .label ".LB.Emission.removeSurplus.9" → Obl S g F s ra blk := by
  cfg_block [Obl, Inv, V, Names.removeSurplus]
  intro t ht
  obtain ⟨g1, w1, hb, hok1, hQ⟩ := ht
  kvcgen64
  vc_by_shape
  | load => exact hb.isSome_bx
  | retAddr =>
    refine (congrArg Option.isSome (hb.pop ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_).retAddr).trans rfl
    all_goals rfl
  | ret =>
    refine ProofKit.intercept_mono_exit
      (E := fun a t => a = ra ∧
        Sep.Post S (Extras s F) 2 (fun g' t => surplusQ g g' s t) s t ∧
          Sep.mod.Agree s t) ?_ ?_
    · refine Kp.ret (hb.pop ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) rfl hok1 fun t' _ hax =>
        NormalResult.of_returnRegister_eq hQ hax
      all_goals rfl
    · rintro ⟨ha, hp, hag⟩
      exact Or.inl ⟨ha, extras_post hp, hag⟩

theorem b_10
    : removeSurplusAsm.ForallBlocks fun blk =>
      blk.label = .label ".LB.Emission.removeSurplus.10" → Obl S g F s ra blk := by
  cfg_block [Obl, Inv, V, Names.removeSurplus]
  intro t ht
  obtain ⟨g1, w1, hr, hrs⟩ := ht
  kvcgen64
  all_goals try symexec_norm
  vc_by_shape
  | goto ".LB.Emission.removeSurplus.9" =>
    cfg_goto
    · exact hr.bx.upd.stack
    · simp only
      exact ⟨g1, w1, hr.bx.upd, hr.ok, ⟨hr.keep, by rw [hrs], by rw [hrs]; rfl⟩,
        by change 0#8 ≠ 2#8; decide⟩
    · simp only [V]
      left; omega

theorem b_11
    (hout : ∀ l ∈ Program.labels removeSurplusAsm, label l ≠ label "exit")
    (hswap : Sep.SpecWithExit Names.swapWith swapWithA 2 swapWithQ
      (fun g g' s _ => ExitRes (Flat.swapWith · (rsi s)) g g'))
    : removeSurplusAsm.ForallBlocks fun blk =>
      blk.label = .label ".LB.Emission.removeSurplus.11" → Obl S g F s ra blk := by
  simp only [Names.swapWith] at hswap
  cfg_block [Obl, Inv, V, Names.removeSurplus]
  intro t ht
  obtain ⟨g1, w1, hr, hbud, h0, hrs⟩ := ht
  kvcgen64 [hswap]
  all_goals try symexec_norm
  refine Bx.call2 (Q := swapWithQ)
    (X := fun g g' s _ => ExitRes (Flat.swapWith · (rsi s)) g g')
    (c := { t with regs := { t.regs with rdi := t.regs.rbx } })
    (bx_next% hr.bx) hr.bx.bx hr.ok (swapA_of hbud h0 hr.dok) ?_ (by
    intro tx hp harg
    apply ProofKit.intercept_exit (E := E S g F s ra) hout
    refine Or.inr ⟨rfl, harg, Post.imp hp ?_⟩
    intro g3 hx
    change ExitRes (Flat.swapWith · t.regs.rsi.toBitVec) g1 g3 at hx
    obtain ⟨hK3, hf3, hfail⟩ := hx
    dsimp only [surplusX, ExitRes]
    rw [hrs, afterR_ne (by rw [hfail]; decide)]
    exact ⟨Keep.trans hr.keep hK3, hf3, hfail⟩)
  intro t3 g3 w3 hb3 hQ3 hok3
  obtain ⟨hK3, hf3, hal3⟩ : Res (Flat.swapWith · t.regs.rsi.toBitVec) g1 g3 t3 := hQ3.1
  have hN : (flat g1).size.toNat ≤ maxStackSize := by
    show g1.h.len.toNat ≤ maxStackSize
    have := hr.ok.len; have := hr.ok.n; have := hr.ok.xs; omega
  kvcgen64
  all_goals try symexec_norm
  vc_by_shape
  | goto ".LB.Emission.removeSurplus.9" =>
    have hz : (!(BitVec.extractLsb' 0 8 t3.regs.rax.toBitVec &&& BitVec.extractLsb' 0 8
        t3.regs.rax.toBitVec == BitVec.zero 8)) = true := by assumption
    have hd : (Flat.swapWith (flat g1) t.regs.rsi.toBitVec).1 ≠ .done :=
      ProduceProof.code_ne_zero (fun e => ProduceProof.al_ne (t := t3) hz (hal3.trans e))
    cfg_goto
    · exact hb3.flags.stack
    · simp only
      exact ⟨g3, w3, hb3.flags, hok3, ⟨ProduceProof.Keep.trans hr.keep hK3,
        by rw [hrs, afterR_ne hd]; exact hf3,
        by rw [hrs, afterR_ne hd]; exact hal3⟩, hQ3.2⟩
    · simp only [V, wB]
      left; omega
  | other =>
    have hz : (!(BitVec.extractLsb' 0 8 t3.regs.rax.toBitVec &&& BitVec.extractLsb' 0 8
        t3.regs.rax.toBitVec == BitVec.zero 8)) = false := by assumption
    have hd : (Flat.swapWith (flat g1) t.regs.rsi.toBitVec).1 = .done :=
      ProduceProof.code_eq_zero (hal3.symm.trans (ProduceProof.al_zero (t := t3) hz))
    obtain ⟨e1, e2, e3⟩ := swap_rec hr.ok hok3 hK3 hf3 hd
    first
    | exact ⟨g3, w3, ⟨hb3.flags, hok3, ProduceProof.Keep.trans hr.keep hK3,
        by rw [hf3]; exact destOk_swapWith hr.dok hN _⟩,
        by unfold Budget at hbud; have := hK3.xo; rw [e1, e2, e3]; omega, by rw [hrs, afterR_done hd, ← hf3]⟩
    | (simp only [V, wB]
       right
       refine ⟨?_, by decide⟩
       rw [lenAt_mk, hb3.lenAt, hr.bx.lenAt, e2])

theorem b_12
    (hout : ∀ l ∈ Program.labels removeSurplusAsm, label l ≠ label "exit")
    (hpop : Sep.SpecWithExit Names.pop popA 2 popQ
      (fun g g' _s _t => ExitRes Flat.pop g g'))
    : removeSurplusAsm.ForallBlocks fun blk =>
      blk.label = .label ".LB.Emission.removeSurplus.12" → Obl S g F s ra blk := by
  simp only [Names.pop] at hpop
  cfg_block [Obl, Inv, V, Names.removeSurplus]
  intro t ht
  obtain ⟨g2, w2, hr, hbud, hrs⟩ := ht
  kvcgen64 [hpop]
  all_goals try symexec_norm
  refine Bx.call2 (Q := popQ) (X := fun g g' _s _t => ExitRes Flat.pop g g')
    (c := { t with regs := { t.regs with rdi := t.regs.rbx } })
    (bx_next% hr.bx) hr.bx.bx hr.ok (popA_of hbud hr.dok) ?_ (by
    intro tx hp harg
    apply ProofKit.intercept_exit (E := E S g F s ra) hout
    refine Or.inr ⟨rfl, harg, Post.imp hp ?_⟩
    intro g3 hx
    change ExitRes Flat.pop g2 g3 at hx
    obtain ⟨hK3, hf3, hfail⟩ := hx
    dsimp only [surplusX, ExitRes]
    rw [hrs, afterPop_ne (by rw [hfail]; decide)]
    exact ⟨Keep.trans hr.keep hK3, hf3, hfail⟩)
  intro t3 g3 w3 hb3 hQ3 hok3
  obtain ⟨hK3, hf3, hal3⟩ := hQ3.1
  kvcgen64
  all_goals try symexec_norm
  vc_by_shape
  | goto ".LB.Emission.removeSurplus.0" =>
    have hz : (BitVec.extractLsb' 0 8 t3.regs.rax.toBitVec &&& BitVec.extractLsb' 0 8
        t3.regs.rax.toBitVec == BitVec.zero 8) = true := by assumption
    have hd : (Flat.pop (flat g2)).1 = .done := ProduceProof.code_eq_zero
      (hal3.symm.trans (ProduceProof.al_zero (t := t3) (by rw [hz]; rfl)))
    cfg_goto
    · exact hb3.flags.stack
    · simp only
      exact ⟨g3, w3, ⟨hb3.flags, hok3, ProduceProof.Keep.trans hr.keep hK3,
        by rw [hf3]; exact destOk_pop hr.dok⟩, budget_pop hr.ok hok3 hK3 hf3 hd hbud,
        by rw [hrs, afterPop_done hd, ← hf3]⟩
    · simp only [V, wB]
      left
      rw [lenAt_mk, hb3.lenAt, hr.bx.lenAt, ← len_pop hf3 hd]
      omega
  | goto ".LB.Emission.removeSurplus.9" =>
    have hz : (BitVec.extractLsb' 0 8 t3.regs.rax.toBitVec &&& BitVec.extractLsb' 0 8
        t3.regs.rax.toBitVec == BitVec.zero 8) = false := by assumption
    have hd : (Flat.pop (flat g2)).1 ≠ .done := ProduceProof.code_ne_zero
      (fun e => ProduceProof.al_ne (t := t3) (by rw [hz]; rfl) (hal3.trans e))
    cfg_goto
    · exact hb3.flags.stack
    · simp only
      exact ⟨g3, w3, hb3.flags, hok3, ⟨ProduceProof.Keep.trans hr.keep hK3,
        by rw [hrs, afterPop_ne hd]; exact hf3,
        by rw [hrs, afterPop_ne hd]; exact hal3⟩, hQ3.2⟩
    · simp only [V, wB]
      left; omega

end
end Surplus

theorem removeSurplus_unit [Host] [FunDecls]
    (hexit : FunDecls.at (label "exit") = none)
    (hout : ∀ l ∈ Program.labels removeSurplusAsm, label l ≠ label "exit")
    (hswap : Sep.SpecWithExit Names.swapWith swapWithA 2 swapWithQ
      (fun g g' s _ => ExitRes (Flat.swapWith · (rsi s)) g g'))
    (hpop : Sep.SpecWithExit Names.pop popA 2 popQ
      (fun g g' _s _t => ExitRes Flat.pop g g')) :
    UnitThmWithExit removeSurplusAsm surplusA 4 surplusQ surplusX := by
  intro S g F s ra
  refine ⟨fun t ⟨ht, hp⟩ => ?_⟩
  subst ht
  refine Program.WP.cfg (Surplus.Inv S g F s ra) (Surplus.V S) ?_ rfl
  refine forallBlocks_cases [.entry, .label Names.removeSurplus,
    .label ".LB.Emission.removeSurplus.0", .label ".LB.Emission.removeSurplus.1",
    .label ".LB.Emission.removeSurplus.2", .label ".LB.Emission.removeSurplus.3",
    .label ".LB.Emission.removeSurplus.4", .label ".LB.Emission.removeSurplus.5",
    .label ".LB.Emission.removeSurplus.6", .label ".LB.Emission.removeSurplus.7",
    .label ".LB.Emission.removeSurplus.8", .label ".LB.Emission.removeSurplus.9",
    .label ".LB.Emission.removeSurplus.10", .label ".LB.Emission.removeSurplus.11",
    .label ".LB.Emission.removeSurplus.12"] (by simp only [Names.removeSurplus]; cfg_labels) ?_
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Surplus.b_entry S g F s ra
  · exact Surplus.b_fn S g F s ra hp
  · exact Surplus.b_0 S g F s ra
  · exact Surplus.b_1 S g F s ra
  · exact Surplus.b_2 S g F s ra
  · exact Surplus.b_3 S g F s ra
  · exact Surplus.b_4 S g F s ra
  · exact Surplus.b_5 S g F s ra
  · exact Surplus.b_6 S g F s ra
  · exact Surplus.b_7 S g F s ra hexit hout
  · exact Surplus.b_8 S g F s ra
  · exact Surplus.b_9 S g F s ra
  · exact Surplus.b_10 S g F s ra
  · exact Surplus.b_11 S g F s ra hout hswap
  · exact Surplus.b_12 S g F s ra hout hpop

end FlatShuffler.Unit
