module

public import BbuKraken.Unit.TopGhost
import all BbuKraken.Unit.TopGhost
public import BbuKraken.Unit.Permute.Cfg
import all BbuKraken.Unit.Permute.Cfg
public import ProofKit.Cfg
import all ProofKit.Cfg

@[expose] public section

set_option experimental.vcgen true

/-!
# `build_bottom_up`: the invariant and the variant of each block

`build/kraken/c/build_bottom_up.S`. `S = topS s` is `rsp` after `subq $32872`. `m = mArg s`,
`n = nArg s`, `H0 = hdr0 s ra` is the struct at the entry and `loc0 s ra` are the locals at the
entry (`Lc`: `m_plannedMapping`, a pad, the local planned mapping `PD` and `PP`).

* Fill (`.LB.build_bottom_up.0`, `.LB.build_bottom_up.2`): `PD[k] = -1` for `k < m`, then `PP[j] = -1` for `j < n`.
* Bind (`.LB.build_bottom_up.5`, `.LB.build_bottom_up.4`): `PD[k] = dest[k]`, `PP[dest[k]] = k` for `k < m` (`locK`).
* Header (`.LB.build_bottom_up.6`, `.LB.build_bottom_up.19`, `.LB.build_bottom_up.7`): the stores of the struct members, then
  `dest[i] = PD[i]` for `i < m`.
* Positions (`.LB.build_bottom_up.9`, `.LB.build_bottom_up.11`, `.LB.build_bottom_up.10`): `pos[j] = PP[j]` for `j < n`, then
  `m_plannedMapping = S + offPD`, then the count of `pos[j] = -1` in `pend`.
* Call (`.LB.build_bottom_up.16`) and return (`.LB.build_bottom_up.13`, `.LB.build_bottom_up.12`, `.LB.build_bottom_up.14`, `.LB.build_bottom_up.17`).

`Flat.bindDest v k d` with `v` a vector of the locals is the copy of `v[0..k)` into `d`.
The variant `V` decreases on each edge (the blocks after the call have `V ≤ 2`).
-/

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

namespace Bbu.Unit
open Bbu.Sep
namespace Top

-- The offset of `m_positionOf` in the struct (`Fld.mapping_positionOf`).
abbrev offPos : Nat := 8248

theorem offPos_eq (S : Addr) (i : Nat) :
    Fld.mapping_positionOf S i = S + BitVec.ofNat 64 offPos + BitVec.ofNat 64 (8 * i) := rfl

section
variable (s : MachineData) (ra : Int64)

-- The locals after `k` steps of the loop `.LB.build_bottom_up.0`.
def locA (k : Nat) : Loc := { loc0 s ra with pd := Flat.clearPos k (loc0 s ra).pd }

-- The locals after `j` steps of the loop `.LB.build_bottom_up.2`.
def locF (j : Nat) : Loc :=
  { loc0 s ra with
    pd := Flat.clearPos (mArg s) (loc0 s ra).pd
    pp := Flat.clearPos j (loc0 s ra).pp }

-- The locals after `k` steps of the loop `.LB.build_bottom_up.5`.
def locK (k : Nat) : Loc :=
  { loc0 s ra with
    pd := Flat.bindDest (flatDest s) k (Flat.clearPos (mArg s) (loc0 s ra).pd)
    pp := Flat.bindPos (flatDest s) k (Flat.clearPos (nArg s) (loc0 s ra).pp) }

theorem locK_m : locK s ra (mArg s) = locB s ra := rfl

variable (t : MachineData)

/-! ## The invariant of each label -/

-- `.LB.build_bottom_up.14`: the guard fails. The state is the one of the entry.
def I_14 : Prop :=
  t.dmem = (s.pushRa ra).dmem ∧ t.regs.rsp = (s.pushRa ra).regs.rsp ∧
    t.regs.rbx = s.regs.rbx ∧ t.regs.rbp = s.regs.rbp ∧ t.regs.r12 = s.regs.r12 ∧
    t.regs.r13 = s.regs.r13 ∧ t.regs.r14 = s.regs.r14 ∧ t.regs.r15 = s.regs.r15 ∧ ¬TopGuard s

-- `.LB.build_bottom_up.18`: `m = 0`.
def I_18 : Prop := mArg s = 0 ∧ TS s ra (hdr0 s ra) (loc0 s ra) t ∧ TA s t

-- `.LB.build_bottom_up.0`: `PD[0..k) = -1`, `rax = k`.
def I_0 : Prop := ∃ k < mArg s,
  TS s ra (hdr0 s ra) (locA s ra k) t ∧ TA s t ∧
    t.regs.rax.toBitVec = BitVec.ofNat 64 k

-- `.LB.build_bottom_up.1`: `PD[0..m) = -1`, `0 < n`.
def I_1 : Prop := 0 < nArg s ∧
  TS s ra (hdr0 s ra) (locA s ra (mArg s)) t ∧ TA s t

-- `.LB.build_bottom_up.2`: `PP[0..j) = -1`, `rax = S + offPD + 8j`, `rdx = S + offPD + 8n`.
def I_2 : Prop := ∃ j < nArg s,
  TS s ra (hdr0 s ra) (locF s ra j) t ∧ TA s t ∧
    t.regs.rax.toBitVec = topS s + BitVec.ofNat 64 offPD + BitVec.ofNat 64 (8 * j) ∧
    t.regs.rdx.toBitVec = topS s + BitVec.ofNat 64 offPD + BitVec.ofNat 64 (8 * nArg s)

-- `.LB.build_bottom_up.3`: the fill loops are done, `0 < m`.
def I_3 : Prop := 0 < mArg s ∧ TS s ra (hdr0 s ra) (locK s ra 0) t ∧ TA s t

-- `.LB.build_bottom_up.5`: `k` binds are done, `rax = k`.
def I_5 : Prop := ∃ k < mArg s, TS s ra (hdr0 s ra) (locK s ra k) t ∧ TA s t ∧
  t.regs.rax.toBitVec = BitVec.ofNat 64 k

-- `.LB.build_bottom_up.4`: `k + 1` binds are done, `rax = k`.
def I_4 : Prop := ∃ k < mArg s, TS s ra (hdr0 s ra) (locK s ra (k + 1)) t ∧ TA s t ∧
  t.regs.rax.toBitVec = BitVec.ofNat 64 k

-- `.LB.build_bottom_up.6`: all binds are done, `rax = m - 1`, `rdx = m`.
def I_6 : Prop := 0 < mArg s ∧ TS s ra (hdr0 s ra) (locB s ra) t ∧ TA s t ∧
  t.regs.rax.toBitVec = BitVec.ofNat 64 (mArg s - 1) ∧ t.regs.rdx.toBitVec = BitVec.ofNat 64 (mArg s)

-- `.LB.build_bottom_up.19`: `m = 0`, the fill loops are done.
def I_19 : Prop := mArg s = 0 ∧ TS s ra (hdr0 s ra) (locB s ra) t ∧ TA s t

-- `.LB.build_bottom_up.7`: the members are stored, `dest[0..i) = PD[0..i)`, `rax = m`, `rdx = i`.
def I_7 : Prop := ∃ i < mArg s,
  TS s ra (hdr s ra (Flat.bindDest (locB s ra).pd i (hdr0 s ra).dest) (hdr0 s ra).pos
    (hdr0 s ra).pend) (locB s ra) t ∧ t.regs.rsi = s.regs.rsi ∧
    t.regs.rax.toBitVec = BitVec.ofNat 64 (mArg s) ∧ t.regs.rdx.toBitVec = BitVec.ofNat 64 i

-- `.LB.build_bottom_up.8`: `dest` is `Dm`.
def I_8 : Prop :=
  TS s ra (hdr s ra (Dm s ra) (hdr0 s ra).pos (hdr0 s ra).pend) (locB s ra) t ∧
    t.regs.rsi = s.regs.rsi

-- `.LB.build_bottom_up.15`: `n = 0`.
def I_15 : Prop :=
  nArg s = 0 ∧ TS s ra (hdr s ra (Dm s ra) (hdr0 s ra).pos (hdr0 s ra).pend) (locB s ra) t

-- `.LB.build_bottom_up.9`: `pos[0..j) = PP[0..j)`, `rax = 8j`, `rdx = 8n`, `rdi = S + offPos`,
-- `rsi = S + offPP`.
def I_9 : Prop := ∃ j < nArg s,
  TS s ra (hdr s ra (Dm s ra) (Flat.bindDest (locB s ra).pp j (hdr0 s ra).pos) (hdr0 s ra).pend)
    (locB s ra) t ∧
    t.regs.rax.toBitVec = BitVec.ofNat 64 (8 * j) ∧
    t.regs.rdx.toBitVec = BitVec.ofNat 64 (8 * nArg s) ∧
    t.regs.rdi.toBitVec = topS s + BitVec.ofNat 64 offPos ∧
    t.regs.rsi.toBitVec = topS s + BitVec.ofNat 64 offPP

-- `.LB.build_bottom_up.11`: `pend` is the count of `NONE` in `Pm[0..j)`, `rax = S + 8j`, `rdx = S + 8n`.
def I_11 : Prop := ∃ j < nArg s,
  TS s ra (hdr s ra (Dm s ra) (Pm s ra) (Flat.countNone (Pm s ra) j 0)) (locP s ra) t ∧
    t.regs.rax.toBitVec = topS s + BitVec.ofNat 64 (8 * j) ∧
    t.regs.rdx.toBitVec = topS s + BitVec.ofNat 64 (8 * nArg s)

-- `.LB.build_bottom_up.10`: `pend` is the count of `NONE` in `Pm[0..j]`.
def I_10 : Prop := ∃ j < nArg s,
  TS s ra (hdr s ra (Dm s ra) (Pm s ra) (Flat.countNone (Pm s ra) (j + 1) 0)) (locP s ra) t ∧
    t.regs.rax.toBitVec = topS s + BitVec.ofNat 64 (8 * j) ∧
    t.regs.rdx.toBitVec = topS s + BitVec.ofNat 64 (8 * nArg s)

-- `.LB.build_bottom_up.16`: the struct of the call.
def I_16 : Prop :=
  ∃ L, TS s ra (hdr s ra (Dm s ra) (Pm s ra) (Flat.countNone (Pm s ra) (nArg s) 0)) L t

-- `.LB.build_bottom_up.13` and `.LB.build_bottom_up.12`: after the call.
def I_13 : Prop := ∃ fs, TQ s ra .blocked fs t
def I_12 : Prop := ∃ fs, TQ s ra .done fs t

-- `.LB.build_bottom_up.17`: the result is in `rdx`.
def I_17 : Prop := TR s ra (topS s) t.regs.rdx.toBitVec t

end

section
variable (s : MachineData) (ra : Int64)

def LInv : CfgLabel → MachineData → Prop
  | .entry, t => t = s.pushRa ra
  | .exit, _ => False
  | .label l, t =>
    if l = Names.build_bottom_up then t = s.pushRa ra
    else if l = ".LB.build_bottom_up.0" then I_0 s ra t
    else if l = ".LB.build_bottom_up.1" then I_1 s ra t
    else if l = ".LB.build_bottom_up.2" then I_2 s ra t
    else if l = ".LB.build_bottom_up.3" then I_3 s ra t
    else if l = ".LB.build_bottom_up.4" then I_4 s ra t
    else if l = ".LB.build_bottom_up.5" then I_5 s ra t
    else if l = ".LB.build_bottom_up.6" then I_6 s ra t
    else if l = ".LB.build_bottom_up.7" then I_7 s ra t
    else if l = ".LB.build_bottom_up.8" then I_8 s ra t
    else if l = ".LB.build_bottom_up.9" then I_9 s ra t
    else if l = ".LB.build_bottom_up.10" then I_10 s ra t
    else if l = ".LB.build_bottom_up.11" then I_11 s ra t
    else if l = ".LB.build_bottom_up.12" then I_12 s ra t
    else if l = ".LB.build_bottom_up.13" then I_13 s ra t
    else if l = ".LB.build_bottom_up.14" then I_14 s ra t
    else if l = ".LB.build_bottom_up.15" then I_15 s ra t
    else if l = ".LB.build_bottom_up.16" then I_16 s ra t
    else if l = ".LB.build_bottom_up.17" then I_17 s ra t
    else if l = ".LB.build_bottom_up.18" then I_18 s ra t
    else if l = ".LB.build_bottom_up.19" then I_19 s ra t
    else False

end

/-! ## The variant

`W = 2 ^ 66` is more than each loop term. The order of the phases: the entry, `.LB.build_bottom_up.18`, fill,
bind, header, positions, count, call, return. -/

def V (l : Label) (t : MachineData) : Nat :=
  if l = Names.build_bottom_up then 2 ^ 70
  else if l = ".LB.build_bottom_up.18" then 11 * 2 ^ 66
  else if l = ".LB.build_bottom_up.0" then 10 * 2 ^ 66 + (2 ^ 64 - t.regs.rax.toBitVec.toNat)
  else if l = ".LB.build_bottom_up.1" then 9 * 2 ^ 66
  else if l = ".LB.build_bottom_up.2" then 8 * 2 ^ 66 + (t.regs.rdx.toBitVec - t.regs.rax.toBitVec).toNat
  else if l = ".LB.build_bottom_up.19" ∨ l = ".LB.build_bottom_up.3" then 7 * 2 ^ 66
  else if l = ".LB.build_bottom_up.4" then 6 * 2 ^ 66 + 2 * (2 ^ 64 - t.regs.rax.toBitVec.toNat)
  else if l = ".LB.build_bottom_up.5" then 6 * 2 ^ 66 + 2 * (2 ^ 64 - t.regs.rax.toBitVec.toNat) + 1
  else if l = ".LB.build_bottom_up.6" then 5 * 2 ^ 66
  else if l = ".LB.build_bottom_up.7" then 4 * 2 ^ 66 + (2 ^ 64 - t.regs.rdx.toBitVec.toNat)
  else if l = ".LB.build_bottom_up.8" then 3 * 2 ^ 66
  else if l = ".LB.build_bottom_up.9" then 2 * 2 ^ 66 + (t.regs.rdx.toBitVec - t.regs.rax.toBitVec).toNat
  else if l = ".LB.build_bottom_up.15" then 2 ^ 66
  else if l = ".LB.build_bottom_up.11" then 2 ^ 66 + 4 + (t.regs.rdx.toBitVec - t.regs.rax.toBitVec).toNat
  else if l = ".LB.build_bottom_up.10" then 2 ^ 66 + 3 + (t.regs.rdx.toBitVec - t.regs.rax.toBitVec).toNat
  else if l = ".LB.build_bottom_up.16" then 2
  else if l = ".LB.build_bottom_up.13" ∨ l = ".LB.build_bottom_up.12" then 1
  else 0

/-! ## The obligation of a block -/

-- The exception continuation of the body triple.
def E (s : MachineData) (ra : Int64) : Int64 → MachineData → Prop :=
  fun a t => a = ra ∧ TopFlatPost s t ∧ (topMod s).Agree s t

-- The obligation of `Program.WP.cfg` for the block `blk`.
def Obl [Host] [FunDecls] (s : MachineData) (ra : Int64) (blk : Program.Block) : Prop :=
  ∀ t, LInv s ra blk.label t →
    let I' (b : CfgLabel) (j : Nat) (_ : Unit) (u : MachineData) :=
      LInv s ra b u ∧ Program.Decreases V blk.label blk.idx t b j u
    WP.wp blk.body (I' blk.next (blk.idx + 1))
      (Program.Intercept (Program.labels buildBottomUpAsm) (s.pushRa ra) I' (E s ra)) t

-- The labels of `buildBottomUpAsm`, in the order of the blocks.
def labels : List CfgLabel :=
  [.entry, .label "build_bottom_up", .label ".LB.build_bottom_up.0", .label ".LB.build_bottom_up.1", .label ".LB.build_bottom_up.2",
    .label ".LB.build_bottom_up.3", .label ".LB.build_bottom_up.4", .label ".LB.build_bottom_up.5", .label ".LB.build_bottom_up.6", .label ".LB.build_bottom_up.7",
    .label ".LB.build_bottom_up.8", .label ".LB.build_bottom_up.9", .label ".LB.build_bottom_up.10", .label ".LB.build_bottom_up.11", .label ".LB.build_bottom_up.12",
    .label ".LB.build_bottom_up.13", .label ".LB.build_bottom_up.14", .label ".LB.build_bottom_up.15", .label ".LB.build_bottom_up.16", .label ".LB.build_bottom_up.17",
    .label ".LB.build_bottom_up.18", .label ".LB.build_bottom_up.19"]

-- Each block of `buildBottomUpAsm` has a label in `labels`.
theorem labels_cover : buildBottomUpAsm.ForallBlocks fun blk => blk.label ∈ labels := by
  simp only [labels]
  pm_labels

theorem b_entry [Host] [FunDecls] (s ra) :
    Program.ForallBlocks buildBottomUpAsm fun blk => blk.label = .entry → Obl s ra blk := by
  pm_block [Obl]
  intro t ht
  kvcgen64
  simp only [LInv, Names.build_bottom_up, ↓reduceIte]
  exact ht

-- The goal of a decrease of `V`.
macro "top_dec" : tactic => `(tactic| (
  simp only [V, Names.build_bottom_up, String.reduceEq, ↓reduceIte, or_self, or_false, false_or,
    true_or, or_true, Nat.lt_irrefl, true_and, and_true]
  try omega))

section
variable {s : MachineData} {ra : Int64} {h : Hdr} {L : Loc} {t : MachineData} {k : Nat}

theorem TS.m_lt (hs : TS s ra h L t) (hk : k < mArg s) : k < MAX_N := by
  have := hs.g.1; have := hs.g.n_le'; simp only [MAX_N]; omega

-- `16480(%rsp,%rax,8)` with `rax = k`: `PD[k]`.
theorem TS.pdk_addr (hs : TS s ra h L t) (hax : t.regs.rax.toBitVec = BitVec.ofNat 64 k)
    (_hk : k < MAX_N) :
    t.regs.rsp.toBitVec + t.regs.rax.toBitVec * 8#64 + 16480#64
      = topS s + BitVec.ofNat 64 offPD + BitVec.ofNat 64 (8 * k) := by
  rw [hs.sp, hax]; simp only [MAX_N, offPD] at _hk ⊢; bv_omega

theorem TS.st_pdk (hs : TS s ra h L t) (hax : t.regs.rax.toBitVec = BitVec.ofNat 64 k)
    (hk : k < MAX_N) (w : Word) :
    (Em (topS s) h ∗ Lc (topS s) { L with pd := L.pd.set k w } ∗ R0 s ra).get
      (t.dmem.storeInt (t.regs.rsp.toBitVec + t.regs.rax.toBitVec * 8#64 + 16480#64) 8 w.toInt) := by
  rw [hs.pdk_addr hax hk]; exact Lc.st_pd hs.mem hk w

theorem TS.isSome_pdk (hs : TS s ra h L t) (hax : t.regs.rax.toBitVec = BitVec.ofNat 64 k)
    (hk : k < MAX_N) :
    (t.dmem.loadInt (t.regs.rsp.toBitVec + t.regs.rax.toBitVec * 8#64 + 16480#64) 8).isSome = true := by
  rw [hs.pdk_addr hax hk]; exact Lc.isSome_pd hs.mem hk

end

end Top
end Bbu.Unit
