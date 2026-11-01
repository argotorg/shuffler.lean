module

public import BbuKraken.Unit.Defs
import all BbuKraken.Unit.Defs
public import BbuKraken.Unit.Pop
import all BbuKraken.Unit.Pop
public import BbuKraken.Unit.PermuteSpecs
import all BbuKraken.Unit.PermuteSpecs
public import BbuKraken.Unit.RemoveSurplusLemmas
import all BbuKraken.Unit.RemoveSurplusLemmas
public import BbuKraken.Unit.ShallowestCopy
import all BbuKraken.Unit.ShallowestCopy
public import BbuKraken.FlatSurplus
import all BbuKraken.FlatSurplus
public import BbuKraken.Sep.Stores
import all BbuKraken.Sep.Stores
public import ProofKit.Cfg
import all ProofKit.Cfg
public import ProofKit.Idioms
import all ProofKit.Idioms

@[expose] public section

/-!
# `removeSurplus`

`c/bbu/<Names.removeSurplus>.S`: 1 `pushq`, so 2 free words (1, and 1 for the calls of
`swapWith` and `pop`, which have no free word). Each turn of the loop at
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

namespace Bbu.Unit

open Bbu.Sep

-- `removeSurplus()`: room for a swap and a pop for each slot, and destinations below `n`.
def surplusA (g : G) (_s : MachineData) : Prop :=
  g.h.nops.toNat + 2 * g.h.len.toNat ≤ 6 * g.h.n.toNat + g.xo ∧ DestOk (flat g)
def surplusQ (g g' : G) (_s t : MachineData) : Prop := Res Flat.removeSurplus g g' t

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
  ∃ g2 w, Run S g F s ra g2 w t ∧ Budget g2 ∧ t.regs.rdi.toBitVec.toNat < MAX_N
    ∧ (Flat.get g2.h.dest t.regs.rdi.toBitVec = Flat.NONE
      ∨ (Flat.get g2.h.dest t.regs.rdi.toBitVec).toNat < MAX_N)
    ∧ Flat.removeSurplus (flat g) = afterPop (posAt (flat g2) t.regs.rdi.toBitVec)

-- `.LB.Emission.removeSurplus.10`: the call of `swapWith`.
def At301 : Prop :=
  ∃ g1 w, Run S g F s ra g1 w t ∧ Budget g1 ∧ g1.h.len ≠ 0#64
    ∧ Flat.removeSurplus (flat g) = afterR (Flat.swapWith (flat g1) t.regs.rsi.toBitVec)

-- `.LB.Emission.removeSurplus.11`: the call of `pop`. A swap is done, so the budget has one more
-- record.
def At282 : Prop :=
  ∃ g2 w, Run S g F s ra g2 w t
    ∧ g2.h.nops.toNat + 2 * g2.h.len.toNat ≤ 6 * g2.h.n.toNat + g2.xo + 1
    ∧ Flat.removeSurplus (flat g) = afterPop (flat g2)

-- `.LB.Emission.removeSurplus.6`: no surplus slot is reachable.
def At281 : Prop :=
  ∃ g1 w, Run S g F s ra g1 w t ∧ t.regs.r8.toBitVec = g1.h.len
    ∧ Flat.removeSurplus (flat g) = Flat.blockSwapUnreachable (flat g1) t.regs.rdx.toBitVec

-- `.LB.Emission.removeSurplus.7` and `.LB.Emission.removeSurplus.9`: no surplus slot.
def AtDone : Prop :=
  ∃ g1 w, Run S g F s ra g1 w t ∧ Flat.removeSurplus (flat g) = (.done, flat g1)

-- `.LB.Emission.removeSurplus.8`: the result.
def At275 : Prop :=
  ∃ g1 w, Bx S g1 F s ra w t ∧ g1.Ok ∧ surplusQ g g1 s t

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


-- The precondition of `pop` at `.LB.Emission.removeSurplus.11`.
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

-- The precondition of `swapWith` at `.LB.Emission.removeSurplus.10`.
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
    (q - 1#64).toNat < MAX_N ∧ (q - 1#64).toNat < g1.h.n.toNat + g1.xs ∧ d.toNat < MAX_N
      ∧ d.toNat < g1.h.n.toNat + g1.xs ∧ q - 1#64 + 1#64 < g1.h.len ∧ q.toNat ≤ MAX_N
      ∧ q - 1#64 < (flat g1).size ∧ d < (flat g1).size ∧ (flat g1).size.toNat ≤ MAX_N := by
  have hl := hok.len
  have hn := hok.n
  have hx := hok.xs
  show _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ q - 1#64 < g1.h.len ∧ d < g1.h.len ∧ g1.h.len.toNat ≤ MAX_N
  subst hdi
  simp only [MAX_N] at *
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
    (hqN : q.toNat ≤ MAX_N) (hdi : d = g1.h.len - 1#64)
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

set_option maxRecDepth 100000 in
open Surplus Generate in
theorem removeSurplus_unit [Host] [FunDecls]
    (hswap : Sep.Spec Names.swapWith swapWithA 0 swapWithQ)
    (hpop : Sep.Spec Names.pop popA 0 popQ) :
    UnitThm removeSurplusAsm surplusA 2 surplusQ := by
  simp only [Names.swapWith, Names.pop] at hswap hpop
  intro S g F s ra
  refine ⟨fun s₀ ⟨h₀, hpre⟩ => ?_⟩
  subst h₀
  obtain ⟨fr, v, hfr, hm⟩ := hpre.mem
  obtain ⟨w, x, rfl⟩ := split2 hfr
  have hk0 : Kp S g F s ra [w, x] (s.pushRa ra) := Kp.init hm
  refine Program.WP.cfg (fun
      | .entry, t => t = s.pushRa ra
      | .label "_ZN12_GLOBAL__N_18Emission13removeSurplusEv", t => t = s.pushRa ra
      | .label ".LB.Emission.removeSurplus.0", t => At276 S g F s ra t
      | .label ".LB.Emission.removeSurplus.1", t => At277 S g F s ra t
      | .label ".LB.Emission.removeSurplus.2", t => At279 S g F s ra t
      | .label ".LB.Emission.removeSurplus.3", t => At300 S g F s ra t
      | .label ".LB.Emission.removeSurplus.4", t => At283 S g F s ra t
      | .label ".LB.Emission.removeSurplus.5", t => At289 S g F s ra t
      | .label ".LB.Emission.removeSurplus.6", t => At281 S g F s ra t
      | .label ".LB.Emission.removeSurplus.7", t => AtDone S g F s ra t
      | .label ".LB.Emission.removeSurplus.8", t => At275 S g F s ra t
      | .label ".LB.Emission.removeSurplus.9", t => AtDone S g F s ra t
      | .label ".LB.Emission.removeSurplus.10", t => At301 S g F s ra t
      | .label ".LB.Emission.removeSurplus.11", t => At282 S g F s ra t
      | _, _ => False)
    (fun
      | "_ZN12_GLOBAL__N_18Emission13removeSurplusEv", _ => 2 ^ 200
      | ".LB.Emission.removeSurplus.0", t => lenAt S t * wB + (wB - 1)
      | ".LB.Emission.removeSurplus.1", t => lenAt S t * wB + wH + 2 * t.regs.rax.toBitVec.toNat + 2
      | ".LB.Emission.removeSurplus.2", t => lenAt S t * wB + wH + 2 * t.regs.rax.toBitVec.toNat + 3
      | ".LB.Emission.removeSurplus.3", t => lenAt S t * wB + wH
      | ".LB.Emission.removeSurplus.4", t => lenAt S t * wB + t.regs.rax.toBitVec.toNat + 2
      | ".LB.Emission.removeSurplus.5", t => lenAt S t * wB + 2
      | ".LB.Emission.removeSurplus.6", _ => 1
      | ".LB.Emission.removeSurplus.7", _ => 1
      | ".LB.Emission.removeSurplus.8", _ => 0
      | ".LB.Emission.removeSurplus.9", _ => 1
      | ".LB.Emission.removeSurplus.10", t => lenAt S t * wB + 1
      | ".LB.Emission.removeSurplus.11", t => lenAt S t * wB + 1
      | _, _ => 0) ?_ rfl
  cfg_blocks
  case «entry» t ht =>
    subst ht; kvcgen64
  case «_ZN12_GLOBAL__N_18Emission13removeSurplusEv» t ht =>
    subst ht
    clear hswap hpop
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
      | (left; unfold lenAt; omega)
  case «.LB.Emission.removeSurplus.0» t ht =>
    clear hswap hpop hm hfr hk0
    obtain ⟨g1, w1, hr, hbud, hrs⟩ := ht
    have hm1 := hr.bx.mem
    have hl1 : lenAt S t = g1.h.len.toNat := hr.bx.lenAt
    kvcgen64
    all_goals try symexec_norm
    all_goals simp only [hr.bx.bx, rd_len' hm1] at *
    vc_by_shape
    | load => exact isSome_len' hm1
    | goto ".LB.Emission.removeSurplus.9" =>
      have h0 := ShallowestCopy.zf_true (by with_reducible assumption)
      cfg_goto
      · exact hr.bx.upd.stack
      · simp only
        exact ⟨g1, w1, hr.upd, hrs.trans (rs_zero (st := flat g1) h0)⟩
      · simp only
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
      · simp only
        rw [lenAt_mk]
        left
        have := (g1.h.len + BitVec.ofInt 64 (-1)).isLt
        omega
  case «.LB.Emission.removeSurplus.1» t ht =>
    clear hswap hpop hm hfr hk0
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
      · simp only
        rw [lenAt_mk]
        left; omega
    | other =>
      rename_i hz
      have h0 := sub1_ne hz
      first
      | exact at279_mk hr hsc (sub1_lt h0 hlt) (scan_pred hs)
      | (left; rw [lenAt_mk]; have := ShallowestCopy.pred_toNat h0; omega)
  case «.LB.Emission.removeSurplus.2» t ht =>
    clear hswap hpop hm hfr hk0
    obtain ⟨g1, w1, hr, ⟨hbud, hrs, hr8, hdi⟩, hlt, hsc⟩ := ht
    have hm1 := hr.bx.mem
    have hl1 : lenAt S t = g1.h.len.toNat := hr.bx.lenAt
    have hax : t.regs.rax.toBitVec.toNat < MAX_N := by
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
      · simp only
        rw [lenAt_mk]
        left
        omega
  case «.LB.Emission.removeSurplus.3» t ht =>
    clear hswap hpop hm hfr hk0
    obtain ⟨g1, w1, hr, ⟨hbud, hrs, hr8, hdi⟩, h0, hs⟩ := ht
    kvcgen64
    all_goals try symexec_norm
    vc_by_shape
    | goto ".LB.Emission.removeSurplus.7" =>
      have hz : (t.regs.rdx.toBitVec - 18446744073709551615#64 == BitVec.zero 64) = true := by
        assumption
      cfg_goto
      · exact hr.bx.flags.stack
      · simp only
        exact ⟨g1, w1, hr.flags, rs300_none hrs h0 hs hz⟩
      · simp only
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
      · simp only
        left; omega
    | goto ".LB.Emission.removeSurplus.11" =>
      have hz1 : (t.regs.rdx.toBitVec - 18446744073709551615#64 == BitVec.zero 64) = false := by
        assumption
      have hz2 : (t.regs.rsi.toBitVec - 18446744073709551615#64 == BitVec.zero 64) = false := by
        assumption
      have he : (t.regs.rdi.toBitVec - t.regs.rdx.toBitVec == BitVec.zero 64) = true := by
        assumption
      cfg_goto
      · exact hr.bx.flags.stack
      · simp only
        exact ⟨g1, w1, hr.flags, Nat.le_succ_of_le hbud, rs300_top hrs h0 hs hz1 hz2 he hdi⟩
      · simp only
        rw [lenAt_mk]
        left; omega
    | other =>
      have hz1 : (t.regs.rdx.toBitVec - 18446744073709551615#64 == BitVec.zero 64) = false := by
        assumption
      have hz2 : (t.regs.rsi.toBitVec - 18446744073709551615#64 == BitVec.zero 64) = false := by
        assumption
      have he : (t.regs.rdi.toBitVec - t.regs.rdx.toBitVec == BitVec.zero 64) = false := by
        assumption
      first
      | exact at283_mk hr hbud h0 hdi rfl (BitVec.le_refl _) (rs300_eq hrs h0 hs hz1 hz2 he hdi)
      | (left; rw [lenAt_mk]; have := t.regs.rdi.toBitVec.isLt; omega)
  case «.LB.Emission.removeSurplus.4» t ht =>
    clear hswap hpop hm hfr hk0
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
    | goto ".LB.Emission.removeSurplus.10" =>
      have hq0 := ShallowestCopy.zf_true (by with_reducible assumption)
      cfg_goto
      · exact hr.bx.flags.stack
      · simp only
        exact ⟨g1, w1, hr.flags, hbud, h0, by rw [hrs, hq0, eqStep_zero]⟩
      · simp only
        left; rw [lenAt_mk]; omega
    | goto ".LB.Emission.removeSurplus.4" =>
      first
      | have hne := ne_none_of_z (nb (by with_reducible assumption))
        cfg_goto
        · exact hr.bx.upd.stack
        · simp only
          exact at283_mk hr hbud h0 hdi hr8 (by bv_omega) (rs283_dest hrs hq hne)
        · simp only
          left; rw [lenAt_mk]; have := ShallowestCopy.pred_toNat hq; omega
      | have hne := data_ne hm1 hr.ok hbn han (nb (by rw [← hr8]; with_reducible assumption))
        cfg_goto
        · exact hr.bx.upd.stack
        · simp only
          exact at283_mk hr hbud h0 hdi hr8 (by bv_omega) (rs283_data hrs hq hdi hne)
        · simp only
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
      · simp only
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
           rw [(hr.bx.updm h3').lenAt, hr.bx.lenAt]
           have := ShallowestCopy.pred_toNat hq
           show g1.h.len.toNat * wB + 2 < g1.h.len.toNat * wB + t.regs.rax.toBitVec.toNat + 2
           omega)
  case «.LB.Emission.removeSurplus.5» t ht =>
    clear hswap hpop hm hfr hk0
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
    | goto ".LB.Emission.removeSurplus.11" =>
      first
      | have hz := none_of_z (by with_reducible assumption)
        cfg_goto
        · exact (bx_next% hr.bx).stack
        · simp only
          exact ⟨g2, w2, run_next% hr, Nat.le_succ_of_le hbud, by rw [hrs, posAt_none hz]⟩
        · simp only
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
        · simp only
          left
          rw [(hr.bx.updm hm3).lenAt, hr.bx.lenAt]
          exact Nat.add_lt_add_left (by decide) _
  case «.LB.Emission.removeSurplus.6» t ht =>
    clear hswap hpop hm hfr hk0
    obtain ⟨g1, w1, hr, hr8, hrs⟩ := ht
    have hm1 := hr.bx.mem
    kvcgen64
    all_goals try symexec_norm
    all_goals try simp only [hr.bx.bx] at ⊢
    vc_by_shape
    | goto ".LB.Emission.removeSurplus.8" =>
      first
      | have hz : (t.regs.r8.toBitVec - 17#64 - t.regs.rdx.toBitVec == BitVec.zero 64) = true := by
          assumption
        rw [hr8] at hz
        have hz0 : Flat.depthOf (flat g1) t.regs.rdx.toBitVec - Flat.maxSwapDepth = 0 :=
          (Surplus.exc_eq (flat g1) _).symm.trans (beq_iff_eq.mp hz)
        have hb : Flat.removeSurplus (flat g) = (.assertionFailed, flat g1) := by
          rw [hrs, Flat.blockSwapUnreachable, ProduceProof.block_zero hz0]
        cfg_goto
        · exact hr.bx.upd.stack
        · simp only
          exact ⟨g1, w1, hr.bx.upd, hr.ok, hr.keep, by rw [hb], by rw [hb]; rfl⟩
        · simp only
          left; omega
      | have hz : (t.regs.r8.toBitVec - 17#64 - t.regs.rdx.toBitVec == BitVec.zero 64) = false := by
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
            ProduceProof.Keep.trans hr.keep (ProduceProof.Keep.withBlk _ _), by rw [hb], by rw [hb]; rfl⟩
        · simp only
          left; omega
    | load =>
      first
      | with_reducible exact ProduceProof.isSome_off' hm1
      | with_reducible exact ProduceProof.isSome_exc' (ProduceProof.store_off' hm1 _)
  case «.LB.Emission.removeSurplus.7» t ht =>
    clear hswap hpop hm hfr hk0
    obtain ⟨g1, w1, hr, hrs⟩ := ht
    kvcgen64
    all_goals try symexec_norm
    vc_by_shape
    | other =>
      exact ⟨g1, w1, hr.bx.upd, hr.ok, hr.keep, by rw [hrs], by rw [hrs]; rfl⟩
    | closed => simp
  case «.LB.Emission.removeSurplus.8» t ht =>
    clear hswap hpop hm hk0
    obtain ⟨g1, w1, hb, hok1, hQ⟩ := ht
    kvcgen64
    vc_by_shape
    | load => exact hb.isSome_bx
    | retAddr =>
      refine (congrArg Option.isSome (hb.pop ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_).retAddr).trans rfl
      all_goals rfl
    | ret =>
      refine Kp.ret (hb.pop ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) rfl hok1 fun t' _ hax =>
        ⟨hQ.1, hQ.2.1, by show (rax t').setWidth 8 = _; rw [hax]; exact hQ.2.2⟩
      all_goals rfl
  case «.LB.Emission.removeSurplus.9» t ht =>
    clear hswap hpop hm hfr hk0
    obtain ⟨g1, w1, hr, hrs⟩ := ht
    kvcgen64
    all_goals try symexec_norm
    vc_by_shape
    | goto ".LB.Emission.removeSurplus.8" =>
      cfg_goto
      · exact hr.bx.upd.stack
      · simp only
        exact ⟨g1, w1, hr.bx.upd, hr.ok, hr.keep, by rw [hrs], by rw [hrs]; rfl⟩
      · simp only
        left; omega
  case «.LB.Emission.removeSurplus.10» t ht =>
    clear hpop hm hfr hk0
    obtain ⟨g1, w1, hr, hbud, h0, hrs⟩ := ht
    kvcgen64 [hswap]
    all_goals try symexec_norm
    refine Bx.call0 (bx_next% hr.bx) hr.bx.bx hr.ok (swapA_of hbud h0 hr.dok) ?_
    intro t3 g3 w3 hb3 hQ3 hok3
    obtain ⟨hK3, hf3, hal3⟩ : Res (Flat.swapWith · t.regs.rsi.toBitVec) g1 g3 t3 := hQ3
    have hN : (flat g1).size.toNat ≤ MAX_N := by
      show g1.h.len.toNat ≤ MAX_N
      have := hr.ok.len; have := hr.ok.n; have := hr.ok.xs; omega
    kvcgen64
    all_goals try symexec_norm
    vc_by_shape
    | goto ".LB.Emission.removeSurplus.8" =>
      have hz : (!(BitVec.extractLsb' 0 8 t3.regs.rax.toBitVec &&& BitVec.extractLsb' 0 8
          t3.regs.rax.toBitVec == BitVec.zero 8)) = true := by assumption
      have hd : (Flat.swapWith (flat g1) t.regs.rsi.toBitVec).1 ≠ .done :=
        ProduceProof.code_ne_zero (fun e => ProduceProof.al_ne (t := t3) hz (hal3.trans e))
      cfg_goto
      · exact hb3.flags.stack
      · simp only
        exact ⟨g3, w3, hb3.flags, hok3, ProduceProof.Keep.trans hr.keep hK3,
          by rw [hrs, afterR_ne hd]; exact hf3, by rw [hrs, afterR_ne hd]; exact hal3⟩
      · simp only
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
      | (try simp only
         right
         refine ⟨?_, by decide⟩
         rw [lenAt_mk, hb3.lenAt, hr.bx.lenAt, e2])
  case «.LB.Emission.removeSurplus.11» t ht =>
    clear hswap hm hfr hk0
    obtain ⟨g2, w2, hr, hbud, hrs⟩ := ht
    kvcgen64 [hpop]
    all_goals try symexec_norm
    refine Bx.call0 (bx_next% hr.bx) hr.bx.bx hr.ok (popA_of hbud hr.dok) ?_
    intro t3 g3 w3 hb3 hQ3 hok3
    obtain ⟨hK3, hf3, hal3⟩ := hQ3
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
      · simp only
        left
        rw [lenAt_mk, hb3.lenAt, hr.bx.lenAt, ← len_pop hf3 hd]
        omega
    | goto ".LB.Emission.removeSurplus.8" =>
      have hz : (BitVec.extractLsb' 0 8 t3.regs.rax.toBitVec &&& BitVec.extractLsb' 0 8
          t3.regs.rax.toBitVec == BitVec.zero 8) = false := by assumption
      have hd : (Flat.pop (flat g2)).1 ≠ .done := ProduceProof.code_ne_zero
        (fun e => ProduceProof.al_ne (t := t3) (by rw [hz]; rfl) (hal3.trans e))
      cfg_goto
      · exact hb3.flags.stack
      · simp only
        exact ⟨g3, w3, hb3.flags, hok3, ProduceProof.Keep.trans hr.keep hK3,
          by rw [hrs, afterPop_ne hd]; exact hf3, by rw [hrs, afterPop_ne hd]; exact hal3⟩
      · simp only
        left; omega

end Bbu.Unit
