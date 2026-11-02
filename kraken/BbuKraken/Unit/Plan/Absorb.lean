module

public import BbuKraken.Unit.Plan.KeepWildcard
import all BbuKraken.Unit.Plan.KeepWildcard

@[expose] public section

/-!
# `MappingBuilder::absorbSurplus`

`Names.absorbSurplus` in `build/kraken/c/build_bottom_up.S`: if `n = 0` it returns `DONE` at once. Else it pushes `rbp`, `rbx`
and runs the outer loop over the targets `rbx < n` (block `.5`, the step in `.4`). `rbp` is the
builder. A wildcard target without a source runs the inner loop of `Flat.absorbBest` over the
sources `rax < m` (blocks `.2`, `.1`, `.0`), with the best source so far in `rsi`, `rax - rbx` in
`rdx`, `m` in `rcx`, `m_dropped` in `rdi` and the mapping in `r8`. Block `.3` gives the best source
to `map`. The frame of the loops is the return slot of `map` and the saved `rbx`, `rbp`, as in
`mapInPlace` (`InPlaceU`).
-/

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

set_option experimental.vcgen true

namespace Bbu.Unit

open Bbu.Sep

def absorbA (_ : BG) (_ : MachineData) : Prop := True

def absorbQ (b b' : BG) (_ t : MachineData) : Prop :=
  al t = code (Flat.absorbSurplus b.fl b.M).1
    ∧ b' = { b with M := (Flat.absorbSurplus b.fl b.M).2 }

def absorbX (b b' : BG) (_s _t : MachineData) : Prop :=
  (Flat.absorbSurplus b.fl b.M).1 = .assertionFailed ∧
    b' = { b with M := (Flat.absorbSurplus b.fl b.M).2 }

namespace AbsorbU

open InPlaceU

/-! ### One turn of the loops -/

section
variable {fb : Flat.Builder} {M : Flat.Mapping} {j o best : Word}

-- The result of `absorbBest` is `NONE` or a source position.
theorem best_lt : ∀ o best, (best = Flat.NONE ∨ best < fb.m) →
    Flat.absorbBest fb M j o best = Flat.NONE ∨ Flat.absorbBest fb M j o best < fb.m := by
  intro o best hb
  fun_induction Flat.absorbBest fb M j o best with
  | case1 o best h best' ih =>
    apply ih
    dsimp only [best']
    split
    · exact Or.inr h
    · exact hb
  | case2 o best h => exact hb

theorem best_ge (h : ¬ o < fb.m) : Flat.absorbBest fb M j o best = best := by
  rw [Flat.absorbBest, dite_eq_right h]

theorem best_skip (h : o < fb.m) (hc : Flat.mappable fb M o = false) :
    Flat.absorbBest fb M j o best = Flat.absorbBest fb M j (o + 1) best := by
  rw [Flat.absorbBest, dite_eq_left h]
  simp [hc]

theorem best_drop (h : o < fb.m) (hd : (!(Flat.get fb.dropped o == 0)) = true) :
    Flat.absorbBest fb M j o best = Flat.absorbBest fb M j (o + 1) best := by
  rw [Bool.not_eq_true'] at hd
  exact best_skip h (by simp only [Flat.mappable, hd, Bool.false_and])

theorem best_dest (h : o < fb.m) (hd : (!(Flat.get M.dest o == Flat.NONE)) = true) :
    Flat.absorbBest fb M j o best = Flat.absorbBest fb M j (o + 1) best := by
  rw [Bool.not_eq_true'] at hd
  exact best_skip h (by simp only [Flat.mappable, hd, Bool.and_false])

theorem best_none (h : o < fb.m) (hd : (!(Flat.get fb.dropped o == 0)) = false)
    (hm : (!(Flat.get M.dest o == Flat.NONE)) = false) :
    Flat.absorbBest fb M j o Flat.NONE = Flat.absorbBest fb M j (o + 1) o := by
  rw [Flat.absorbBest, dite_eq_left h]
  simp [ClosestU.mappable_of hd hm]

theorem best_cmp (h : o < fb.m) (hd : (!(Flat.get fb.dropped o == 0)) = false)
    (hm : (!(Flat.get M.dest o == Flat.NONE)) = false) (hb : best ≠ Flat.NONE) :
    Flat.absorbBest fb M j o best = Flat.absorbBest fb M j (o + 1)
      (if Flat.absDiff o j < Flat.absDiff best j then o else best) := by
  rw [Flat.absorbBest, dite_eq_left h]
  simp only [ClosestU.mappable_of hd hm, hb, decide_false, Bool.false_or, Bool.true_and]
  by_cases hl : Flat.absDiff o j < Flat.absDiff best j <;> simp [hl]

theorem from_ge (h : ¬ j < fb.n) : Flat.absorbFrom fb M j = (.done, M) := by
  rw [Flat.absorbFrom, dite_eq_right h]

theorem skip_junk (h : j < fb.n) (hw : Flat.isWildcardTarget fb j = false) :
    Flat.absorbFrom fb M j = Flat.absorbFrom fb M (j + 1) := by
  rw [Flat.absorbFrom, dite_eq_left h]
  simp [hw]

theorem skip_pos (h : j < fb.n) (hp : (!(Flat.get M.pos j == Flat.NONE)) = true) :
    Flat.absorbFrom fb M j = Flat.absorbFrom fb M (j + 1) := by
  rw [Flat.absorbFrom, dite_eq_left h]
  simp only [Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq] at hp
  simp [Flat.hasSourceAssigned, hp]

theorem skip_none (h : j < fb.n) (hc : Flat.absorbBest fb M j 0 Flat.NONE = Flat.NONE) :
    Flat.absorbFrom fb M j = Flat.absorbFrom fb M (j + 1) := by
  rw [Flat.absorbFrom, dite_eq_left h]
  have hc0 : Flat.absorbBest fb M j 0#64 Flat.NONE = Flat.NONE := hc
  simp [hc0]

theorem skip_m0 (h : j < fb.n) (hm : fb.m = 0#64) :
    Flat.absorbFrom fb M j = Flat.absorbFrom fb M (j + 1) :=
  skip_none h (best_ge (by rw [hm]; decide))

theorem from_done (h : j < fb.n) (hw : Flat.isWildcardTarget fb j = true)
    (hp : (!(Flat.get M.pos j == Flat.NONE)) = false)
    (hc : Flat.absorbBest fb M j 0 Flat.NONE ≠ Flat.NONE)
    (hd : (Flat.mbMap fb M (Flat.absorbBest fb M j 0 Flat.NONE) j).1 = .done) :
    Flat.absorbFrom fb M j
      = Flat.absorbFrom fb (Flat.mbMap fb M (Flat.absorbBest fb M j 0 Flat.NONE) j).2 (j + 1) := by
  rw [Flat.absorbFrom, dite_eq_left h]
  simp only [Bool.not_eq_false', beq_iff_eq] at hp
  have hc0 : Flat.absorbBest fb M j 0#64 Flat.NONE ≠ Flat.NONE := hc
  have hd0 : (Flat.mbMap fb M (Flat.absorbBest fb M j 0#64 Flat.NONE) j).1 = .done := hd
  simp [Flat.hasSourceAssigned, hp, hw, hc0, hd0]

theorem from_fail (h : j < fb.n) (hw : Flat.isWildcardTarget fb j = true)
    (hp : (!(Flat.get M.pos j == Flat.NONE)) = false)
    (hc : Flat.absorbBest fb M j 0 Flat.NONE ≠ Flat.NONE)
    (hd : (Flat.mbMap fb M (Flat.absorbBest fb M j 0 Flat.NONE) j).1 ≠ .done) :
    Flat.absorbFrom fb M j = Flat.mbMap fb M (Flat.absorbBest fb M j 0 Flat.NONE) j := by
  rw [Flat.absorbFrom, dite_eq_left h]
  simp only [Bool.not_eq_false', beq_iff_eq] at hp
  have hc0 : Flat.absorbBest fb M j 0#64 Flat.NONE ≠ Flat.NONE := hc
  have hd0 : (Flat.mbMap fb M (Flat.absorbBest fb M j 0#64 Flat.NONE) j).1 ≠ .done := hd
  simp [Flat.hasSourceAssigned, hp, hw, hc0, hd0]
end

/-! ### The registers of the inner loop -/

-- `rbx` is a wildcard target without a source, `rax` a source position.
structure IS (b : BG) (M : Flat.Mapping) (t : MachineData) : Prop where
  jn : t.regs.rbx.toBitVec.toNat < b.n.toNat
  hw : Flat.isWildcardTarget b.fl t.regs.rbx.toBitVec = true
  hp : (!(Flat.get M.pos t.regs.rbx.toBitVec == Flat.NONE)) = false
  om : t.regs.rax.toBitVec.toNat < b.m.toNat
  rcx : t.regs.rcx.toBitVec = b.m
  rdi : t.regs.rdi.toBitVec = b.drp
  r8 : t.regs.r8.toBitVec = b.mp
  rdx : t.regs.rdx.toBitVec = t.regs.rax.toBitVec - t.regs.rbx.toBitVec

theorem IS.next {b : BG} {M : Flat.Mapping} {t t' : MachineData} (h : IS b M t)
    (hax : t'.regs.rax = t.regs.rax) (hbx : t'.regs.rbx = t.regs.rbx)
    (hcx : t'.regs.rcx = t.regs.rcx) (hdx : t'.regs.rdx = t.regs.rdx)
    (hdi : t'.regs.rdi = t.regs.rdi) (h8 : t'.regs.r8 = t.regs.r8) : IS b M t' :=
  ⟨by rw [hbx]; exact h.jn, by rw [hbx]; exact h.hw, by rw [hbx]; exact h.hp,
    by rw [hax]; exact h.om, by rw [hcx]; exact h.rcx, by rw [hdi]; exact h.rdi,
    by rw [h8]; exact h.r8, by rw [hdx, hax, hbx]; exact h.rdx⟩

/-! ### The invariant, the variant and the obligation of a block -/

def Inv (B : Addr) (b : BG) (F : MProp 64) (s : MachineData) (ra : Int64) (fr₀ : List Word) :
    CfgLabel → MachineData → Prop
  | .entry, t => t = s.pushRa ra
  | .exit, _ => False
  | .label l, t =>
    if l = Names.absorbSurplus then t = s.pushRa ra
    else if l = ".LB.MappingBuilder.absorbSurplus.0" then ∃ M w, LI B b F s ra M w t ∧ IS b M t
      ∧ Flat.absorbBest b.fl M t.regs.rbx.toBitVec (t.regs.rax.toBitVec + 1#64) t.regs.rax.toBitVec
        = Flat.absorbBest b.fl M t.regs.rbx.toBitVec 0 Flat.NONE
      ∧ Flat.absorbFrom b.fl M t.regs.rbx.toBitVec = Flat.absorbSurplus b.fl b.M
    else if l = ".LB.MappingBuilder.absorbSurplus.1" then ∃ M w, LI B b F s ra M w t ∧ IS b M t
      ∧ (t.regs.rsi.toBitVec = Flat.NONE ∨ t.regs.rsi.toBitVec < b.m)
      ∧ Flat.absorbBest b.fl M t.regs.rbx.toBitVec (t.regs.rax.toBitVec + 1#64) t.regs.rsi.toBitVec
        = Flat.absorbBest b.fl M t.regs.rbx.toBitVec 0 Flat.NONE
      ∧ Flat.absorbFrom b.fl M t.regs.rbx.toBitVec = Flat.absorbSurplus b.fl b.M
    else if l = ".LB.MappingBuilder.absorbSurplus.2" then ∃ M w, LI B b F s ra M w t ∧ IS b M t
      ∧ (t.regs.rsi.toBitVec = Flat.NONE ∨ t.regs.rsi.toBitVec < b.m)
      ∧ Flat.absorbBest b.fl M t.regs.rbx.toBitVec t.regs.rax.toBitVec t.regs.rsi.toBitVec
        = Flat.absorbBest b.fl M t.regs.rbx.toBitVec 0 Flat.NONE
      ∧ Flat.absorbFrom b.fl M t.regs.rbx.toBitVec = Flat.absorbSurplus b.fl b.M
    else if l = ".LB.MappingBuilder.absorbSurplus.3" then ∃ M w, LI B b F s ra M w t
      ∧ t.regs.rbx.toBitVec.toNat < b.n.toNat
      ∧ Flat.isWildcardTarget b.fl t.regs.rbx.toBitVec = true
      ∧ (!(Flat.get M.pos t.regs.rbx.toBitVec == Flat.NONE)) = false
      ∧ t.regs.rsi.toBitVec = Flat.absorbBest b.fl M t.regs.rbx.toBitVec 0 Flat.NONE
      ∧ Flat.absorbFrom b.fl M t.regs.rbx.toBitVec = Flat.absorbSurplus b.fl b.M
    else if l = ".LB.MappingBuilder.absorbSurplus.4" then ∃ M w, LI B b F s ra M w t
      ∧ t.regs.rbx.toBitVec.toNat < b.n.toNat
      ∧ Flat.absorbFrom b.fl M (t.regs.rbx.toBitVec + 1#64) = Flat.absorbSurplus b.fl b.M
    else if l = ".LB.MappingBuilder.absorbSurplus.5" then ∃ M w, LI B b F s ra M w t
      ∧ t.regs.rbx.toBitVec.toNat < b.n.toNat
      ∧ Flat.absorbFrom b.fl M t.regs.rbx.toBitVec = Flat.absorbSurplus b.fl b.M
    else if l = ".LB.MappingBuilder.absorbSurplus.6" then ∃ M w, LI B b F s ra M w t
      ∧ Flat.absorbSurplus b.fl b.M = (.done, M)
    else if l = ".LB.MappingBuilder.absorbSurplus.7" then ∃ M w, LI B b F s ra M w t
      ∧ al t = code (Flat.absorbSurplus b.fl b.M).1 ∧ (Flat.absorbSurplus b.fl b.M).2 = M
    else if l = ".LB.MappingBuilder.absorbSurplus.8" then Kg (BView B b ∗ F) s ra fr₀ t
      ∧ Flat.absorbSurplus b.fl b.M = (.done, b.M)
    else False

-- The variant: `n - rbx` for the outer loop, then `m - rax` for the inner loop.
def V (b : BG) (l : Label) (t : MachineData) : Nat :=
  if l = Names.absorbSurplus then 2 ^ 140
  else if l = ".LB.MappingBuilder.absorbSurplus.5" then
    (b.n.toNat - t.regs.rbx.toBitVec.toNat) * 2 ^ 68 + 2 ^ 67
  else if l = ".LB.MappingBuilder.absorbSurplus.2" then
    (b.n.toNat - t.regs.rbx.toBitVec.toNat) * 2 ^ 68 + 4 * (b.m.toNat - t.regs.rax.toBitVec.toNat) + 3
  else if l = ".LB.MappingBuilder.absorbSurplus.0" then
    (b.n.toNat - t.regs.rbx.toBitVec.toNat) * 2 ^ 68 + 4 * (b.m.toNat - t.regs.rax.toBitVec.toNat) + 2
  else if l = ".LB.MappingBuilder.absorbSurplus.1" then
    (b.n.toNat - t.regs.rbx.toBitVec.toNat) * 2 ^ 68 + 4 * (b.m.toNat - t.regs.rax.toBitVec.toNat) + 1
  else if l = ".LB.MappingBuilder.absorbSurplus.3" then
    (b.n.toNat - t.regs.rbx.toBitVec.toNat) * 2 ^ 68
  else if l = ".LB.MappingBuilder.absorbSurplus.4" then
    (b.n.toNat - t.regs.rbx.toBitVec.toNat - 1) * 2 ^ 68 + 2 ^ 67 + 1
  else 0

def E [Labels] (B : Addr) (b : BG) (F : MProp 64) (s : MachineData) (ra : Int64) :
    Int64 → MachineData → Prop :=
  fun a t => a = ra ∧ VPost BView BG.Ok B F 6 (fun a' t => absorbQ b a' s t) s t
    ∧ Sep.mod.Agree s t
    ∨ a = label "exit" ∧ t.regs.get64 .rdi = 1#64 ∧
      VPost BView BG.Ok B F 6 (fun a' t => absorbX b a' s t) s t

def Obl [Host] [FunDecls] (B : Addr) (b : BG) (F : MProp 64) (s : MachineData) (ra : Int64)
    (fr₀ : List Word) (blk : Program.Block) : Prop :=
  ∀ t, Inv B b F s ra fr₀ blk.label t →
    let I' (c : CfgLabel) (j : Nat) (_ : Unit) (u : MachineData) :=
      Inv B b F s ra fr₀ c u ∧ Program.Decreases (V b) blk.label blk.idx t c j u
    WP.wp blk.body (I' blk.next (blk.idx + 1))
      (Program.Intercept (Program.labels absorbSurplusAsm) (s.pushRa ra) I' (E B b F s ra)) t

def labels : List CfgLabel :=
  [.entry, .label Names.absorbSurplus,
    .label ".LB.MappingBuilder.absorbSurplus.0", .label ".LB.MappingBuilder.absorbSurplus.1",
    .label ".LB.MappingBuilder.absorbSurplus.2", .label ".LB.MappingBuilder.absorbSurplus.3",
    .label ".LB.MappingBuilder.absorbSurplus.4", .label ".LB.MappingBuilder.absorbSurplus.5",
    .label ".LB.MappingBuilder.absorbSurplus.6", .label ".LB.MappingBuilder.absorbSurplus.7",
    .label ".LB.MappingBuilder.absorbSurplus.8"]

theorem labels_cover : absorbSurplusAsm.ForallBlocks fun blk => blk.label ∈ labels := by
  simp only [labels, Names.absorbSurplus]
  cfg_labels

macro "ab_inv" : tactic => `(tactic|
  simp only [Inv, Names.absorbSurplus, String.reduceEq, ↓reduceIte])
macro "ab_inv" "at" h:ident : tactic => `(tactic|
  simp only [Inv, Names.absorbSurplus, String.reduceEq, ↓reduceIte] at $h:ident)
macro "ab_var" : tactic => `(tactic|
  simp only [V, Names.absorbSurplus, String.reduceEq, ↓reduceIte, Nat.reducePow])

/-! ### The blocks -/

open ShallowestCopy

section
variable [Host] [FunDecls] (B : Addr) (b : BG) (F : MProp 64) (s : MachineData) (ra : Int64)
  (fr₀ : List Word)

set_option maxHeartbeats 100000 in
theorem b_entry : absorbSurplusAsm.ForallBlocks fun blk =>
    blk.label = .entry → Obl B b F s ra fr₀ blk := by
  cfg_block [Obl]
  intro t ht
  kvcgen64
  ab_inv
  exact ht

set_option maxHeartbeats 100000 in
theorem b_fn (hpre : VPre BView BG.Ok B b F absorbA 6 s) (w₀ w₁ w₂ w₃ w₄ w₅ : Word)
    (hk0 : Kg (BView B b ∗ F) s ra [w₀, w₁, w₂, w₃, w₄, w₅] (s.pushRa ra)) :
    absorbSurplusAsm.ForallBlocks fun blk =>
      blk.label = .label Names.absorbSurplus → Obl B b F s ra [w₀, w₁, w₂, w₃, w₄, w₅] blk := by
  cfg_block [Obl, Names.absorbSurplus]
  intro t ht
  ab_inv at ht
  subst ht
  have hrdi : (s.pushRa ra).regs.rdi.toBitVec = B := by
    simpa [MachineData.pushRa] using hpre.rdi
  have hm0 := hk0.vmem
  have hq : (s.pushRa ra).regs.rsp.toBitVec = rsp s - 8#64 := by
    rw [← Reg64s.get64_rsp, hk0.sp64]
  have hsp2 : (s.pushRa ra).regs.rsp.toBitVec - 8#64 - 8#64 - 8#64 = rsp s - 8#64 - 24#64 := by
    rw [hq]; bv_omega
  obtain ⟨hpo, hpm⟩ := hk0.pushes (xs := [(s.pushRa ra).regs.rbp.toBitVec,
    (s.pushRa ra).regs.rbx.toBitVec]) (by simp)
  simp only [pushes] at hpm
  change (Stk (rsp s) (fr s ⟨w₀, w₁, w₂, w₃⟩) ra.toBitVec ∗ BView B b ∗ F).get _ at hpm
  simp only [PushOk] at hpo
  obtain ⟨p1, p2, -⟩ := hpo
  have h_n := BView.rd_n hm0
  unfold rd at h_n
  have k_n := BView.isSome_n hm0
  clear hm0
  kvcgen64
  all_goals try symexec_norm
  all_goals try simp only [hrdi, h_n, sub_beq_zero] at *
  vc_by_shape
  | load =>
    first
    | with_reducible exact k_n
    | with_reducible exact p1
    | with_reducible exact p2
  | goto ".LB.MappingBuilder.absorbSurplus.8" =>
    rename_i hc
    have h0 := beq_iff_eq.mp hc
    cfg_goto
    · exact (hk0.next rfl rfl rfl rfl rfl rfl rfl rfl).stack
    · ab_inv
      exact ⟨hk0.next rfl rfl rfl rfl rfl rfl rfl rfl,
        from_ge (by show ¬ (0 : Word) < b.n; rw [h0]; decide)⟩
    · simp [V, Names.absorbSurplus]
  | goto ".LB.MappingBuilder.absorbSurplus.5" =>
    rename_i hc
    have h0 : b.n ≠ 0#64 := by simpa using hc
    have hpos : 0 < b.n.toNat := Nat.pos_of_ne_zero fun h => h0 (BitVec.eq_of_toNat_eq h)
    cfg_goto
    · exact Kb.stack ⟨hpm, hsp2⟩ (by decide)
    · ab_inv
      exact ⟨b.M, ⟨w₀, w₁, w₂, w₃⟩, ⟨⟨hpm, hsp2⟩, by simpa [MachineData.pushRa] using hpre.rdi, rfl, rfl, rfl, rfl⟩,
        hpos, rfl⟩
    · left; have := b.n.isLt; ab_var; simp; omega

set_option maxHeartbeats 100000 in
theorem b_4 : absorbSurplusAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.MappingBuilder.absorbSurplus.4" → Obl B b F s ra fr₀ blk := by
  cfg_block [Obl]
  intro t ht
  ab_inv at ht
  obtain ⟨M, w, hli, hlt, hrest⟩ := ht
  have hb := hli.kb.mem
  rw [sep_lc] at hb
  have hbp := hli.rbp
  have h_n := BView.rd_n hb
  unfold rd at h_n
  have k_n := BView.isSome_n hb
  clear hb
  kvcgen64
  all_goals try symexec_norm
  all_goals try simp only [hbp, h_n] at *
  vc_by_shape
  | load => with_reducible exact k_n
  | goto ".LB.MappingBuilder.absorbSurplus.6" =>
    have hge := jnb_true _ _ (by assumption)
    rw [BitVec.add_comm] at hge
    cfg_goto
    · exact hli.stk rfl rfl
    · ab_inv
      exact ⟨M, w, hli.next rfl rfl rfl rfl rfl rfl rfl,
        hrest.symm.trans (from_ge fun h => absurd (BitVec.lt_def.1 h) (Nat.not_lt.2 hge))⟩
    · left; ab_var; omega
  | other =>
    have hlt' := jnb_false _ _ (by assumption)
    first
    | (left
       ab_var
       have e : (1#64 + t.regs.rbx.toBitVec).toNat = t.regs.rbx.toBitVec.toNat + 1 := by bv_omega
       omega)
    | (ab_inv
       refine ⟨M, w, hli.next rfl rfl rfl rfl rfl rfl rfl, hlt', ?_⟩
       rw [BitVec.add_comm]
       exact hrest)

set_option maxHeartbeats 100000 in
theorem b_6 : absorbSurplusAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.MappingBuilder.absorbSurplus.6" → Obl B b F s ra fr₀ blk := by
  cfg_block [Obl]
  intro t ht
  ab_inv at ht
  obtain ⟨M, w, hli, hd⟩ := ht
  kvcgen64
  all_goals try symexec_norm
  vc_by_shape
  | other =>
    first
    | (right; exact ⟨by ab_var, Nat.lt_succ_self _⟩)
    | (ab_inv
       exact ⟨M, w, hli.next rfl rfl rfl rfl rfl rfl rfl, by rw [hd]; rfl, by rw [hd]⟩)

set_option maxHeartbeats 100000 in
theorem b_7 (hok : b.Ok) : absorbSurplusAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.MappingBuilder.absorbSurplus.7" → Obl B b F s ra fr₀ blk := by
  cfg_block [Obl]
  intro t ht
  ab_inv at ht
  obtain ⟨M, w, hli, hal, hM⟩ := ht
  obtain ⟨p0, p1⟩ := hli.pop_isSome
  have hokM : BG.Ok { b with M := M } := ⟨hok.m, hok.n, hok.sw, hok.tw, hok.db⟩
  kvcgen64
  all_goals try symexec_norm
  vc_by_shape
  | load =>
    first
    | with_reducible exact p0
    | with_reducible exact p1
  | retAddr =>
    refine Option.isSome_iff_exists.mpr
      ⟨ra, Kg.retAddr (P := BView B { b with M := M } ∗ F) (s := s) (fr := fr s w) ?_⟩
    exact hli.pop_kg rfl (by bv_omega) rfl rfl rfl rfl rfl rfl
  | ret =>
    refine ProofKit.intercept_mono_exit
      (E := fun a t => a = ra ∧
        VPost BView BG.Ok B F 6 (fun a' t => absorbQ b a' s t) s t ∧
          Sep.mod.Agree s t) ?_ (fun h => Or.inl h)
    refine Kg.vret (ok := BG.Ok) (a' := { b with M := M })
      (hli.pop_kg rfl (by bv_omega) rfl rfl rfl rfl rfl rfl) rfl hokM
      fun t' _ hax => ⟨?_, by rw [hM]⟩
    simp only [al] at hal ⊢
    rw [hax]
    exact hal

set_option maxHeartbeats 100000 in
theorem b_8 (hok : b.Ok) (hfr : fr₀.length = 6) : absorbSurplusAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.MappingBuilder.absorbSurplus.8" → Obl B b F s ra fr₀ blk := by
  cfg_block [Obl]
  intro t ht
  ab_inv at ht
  obtain ⟨hk, hd⟩ := ht
  kvcgen64
  all_goals try symexec_norm
  vc_by_shape
  | retAddr =>
    exact Option.isSome_iff_exists.mpr ⟨ra, (hk.next rfl rfl rfl rfl rfl rfl rfl rfl).retAddr⟩
  | ret =>
    refine ProofKit.intercept_mono_exit
      (E := fun a t => a = ra ∧
        VPost BView BG.Ok B F 6 (fun a' t => absorbQ b a' s t) s t ∧
          Sep.mod.Agree s t) ?_ (fun h => Or.inl h)
    refine Kg.vret (ok := BG.Ok) (a' := b) (hk.next rfl rfl rfl rfl rfl rfl rfl rfl) hfr hok
      fun t' _ hax => ⟨?_, by rw [hd]⟩
    simp only [al]
    rw [hax, hd]
    rfl

set_option maxHeartbeats 100000 in
theorem b_5 (hok : b.Ok) : absorbSurplusAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.MappingBuilder.absorbSurplus.5" → Obl B b F s ra fr₀ blk := by
  cfg_block [Obl]
  intro t ht
  ab_inv at ht
  obtain ⟨M, w, hli, hlt, hrest⟩ := ht
  have hokM : BG.Ok { b with M := M } := ⟨hok.m, hok.n, hok.sw, hok.tw, hok.db⟩
  have hb := hli.kb.mem
  rw [sep_lc] at hb
  have hbp := hli.rbp
  have hmax : t.regs.rbx.toBitVec.toNat < MAX_N := Nat.lt_of_lt_of_le hlt hok.n
  obtain ⟨_, hM⟩ := BView.mapM hb
  have h_tgt := BView.rd_tgt hb
  have h_drp := BView.rd_drp hb
  have h_mp := BView.rd_mp hb
  have h_m := BView.rd_m hb
  have h_kind := BView.rdb_kind hb hokM hlt
  have h_pos := MapM.rd_pos hM hmax
  unfold rd at h_tgt h_drp h_mp h_m h_pos
  unfold rdb at h_kind
  have k_tgt := BView.isSome_tgt hb
  have k_drp := BView.isSome_drp hb
  have k_mp := BView.isSome_mp hb
  have k_m := BView.isSome_m hb
  have k_kind := BView.isSome_kind hb hokM hlt
  have k_pos := MapM.isSome_pos hM hmax
  clear hb hM
  kvcgen64
  all_goals try symexec_norm
  all_goals try simp only [hbp, h_tgt, h_drp, h_mp, h_m, fold_slot, slot_8192, h_pos,
    sub_beq_zero, neg_one_eq_none] at *
  vc_by_shape
  | load =>
    first
    | with_reducible exact k_tgt
    | with_reducible exact k_drp
    | with_reducible exact k_mp
    | with_reducible exact k_m
    | with_reducible exact k_kind
    | with_reducible exact k_pos
  | goto ".LB.MappingBuilder.absorbSurplus.4" =>
    have hskip : Flat.absorbFrom b.fl M t.regs.rbx.toBitVec
        = Flat.absorbFrom b.fl M (t.regs.rbx.toBitVec + 1#64) := by
      first
      | (refine skip_m0 (BitVec.lt_def.2 hlt) ?_
         have h := beq_iff_eq.1 ‹(b.m &&& b.m == BitVec.zero 64) = true›
         rw [BitVec.and_self] at h
         exact h)
      | (refine skip_pos (BitVec.lt_def.2 hlt) ?_; with_reducible assumption)
      | (refine skip_junk (BitVec.lt_def.2 hlt) ?_
         exact (CopiesU.junk_flag (fb := b.fl) hlt h_kind).symm.trans
           (by rw [← Bool.not_eq_true']; with_reducible assumption))
    cfg_goto
    · exact hli.stk rfl rfl
    · ab_inv
      exact ⟨M, w, hli.next rfl rfl rfl rfl rfl rfl rfl, hlt, hskip.symm.trans hrest⟩
    · left; ab_var; omega
  | goto ".LB.MappingBuilder.absorbSurplus.2" =>
    have hw : Flat.isWildcardTarget b.fl t.regs.rbx.toBitVec = true :=
      (CopiesU.junk_flag (fb := b.fl) hlt h_kind).symm.trans
        (by rw [← Bool.not_eq_false']; with_reducible assumption)
    have hp : (!(Flat.get M.pos t.regs.rbx.toBitVec == Flat.NONE)) = false := by
      with_reducible assumption
    have hm0 : 0 < b.m.toNat := by
      have h : (b.m &&& b.m == BitVec.zero 64) = false := by with_reducible assumption
      rw [BitVec.and_self, beq_eq_false_iff_ne] at h
      exact Nat.pos_of_ne_zero fun e => h (BitVec.eq_of_toNat_eq e)
    have hpn : Flat.get M.pos t.regs.rbx.toBitVec = Flat.NONE := by simpa using hp
    cfg_goto
    · exact hli.stk rfl rfl
    · ab_inv
      refine ⟨M, w, hli.next rfl rfl rfl rfl rfl rfl rfl,
        ⟨hlt, hw, hp, hm0, rfl, rfl, rfl, (BitVec.zero_sub _).symm⟩, Or.inl hpn, ?_, hrest⟩
      simp only [hpn]
      rfl
    · left; ab_var; have := b.m.isLt; simp; omega

set_option maxHeartbeats 100000 in
theorem b_2 (hok : b.Ok) : absorbSurplusAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.MappingBuilder.absorbSurplus.2" → Obl B b F s ra fr₀ blk := by
  cfg_block [Obl]
  intro t ht
  ab_inv at ht
  obtain ⟨M, w, hli, hi, hbd, hbest, hrest⟩ := ht
  have hokM : BG.Ok { b with M := M } := ⟨hok.m, hok.n, hok.sw, hok.tw, hok.db⟩
  have hb := hli.kb.mem
  rw [sep_lc] at hb
  have hdi := hi.rdi
  have h8 := hi.r8
  have hlt' : t.regs.rax.toBitVec < b.fl.m := BitVec.lt_def.2 hi.om
  have hmax : t.regs.rax.toBitVec.toNat < MAX_N := Nat.lt_of_lt_of_le hi.om hok.m
  obtain ⟨_, hM⟩ := BView.mapM hb
  have h_db : rdb t.dmem (b.drp + t.regs.rax.toBitVec) = Flat.get b.fl.dropped t.regs.rax.toBitVec :=
    BView.rdb_drp (b := { b with M := M }) hb hokM hi.om
  have h_dst := MapM.rd_dest hM hmax
  unfold rd at h_dst
  unfold rdb at h_db
  have k_db := BView.isSome_drp_byte hb hokM hi.om
  have k_dst := MapM.isSome_dest hM hmax
  clear hb hM
  kvcgen64
  all_goals try symexec_norm
  all_goals try simp only [hdi, h8, h_db, fold_slot, h_dst, sub_beq_zero, neg_one_eq_none,
    ClosestU.byte_ne0] at *
  vc_by_shape
  | load =>
    first
    | with_reducible exact k_db
    | with_reducible exact k_dst
  | goto ".LB.MappingBuilder.absorbSurplus.1" =>
    cfg_goto
    · exact hli.stk rfl rfl
    · ab_inv
      refine ⟨M, w, hli.next rfl rfl rfl rfl rfl rfl rfl, hi.next rfl rfl rfl rfl rfl rfl, ?_, ?_,
        hrest⟩
      · first
        | exact hbd
        | (simp only [ClosestU.bor_iff, hi.rdx, ClosestU.absD_i]
           split
           · exact Or.inr hlt'
           · exact hbd)
      · first
        | (refine (best_drop hlt' ?_).symm.trans hbest; with_reducible assumption)
        | (refine (best_dest hlt' ?_).symm.trans hbest; with_reducible assumption)
        | (have hne : t.regs.rsi.toBitVec ≠ Flat.NONE := by
             simpa using ‹(t.regs.rsi.toBitVec == Flat.NONE) = false›
           refine Eq.trans ?_ ((best_cmp hlt' ?_ ?_ hne).symm.trans hbest)
           · simp only [ClosestU.bor_iff, hi.rdx, ClosestU.absD_i]; try rfl
           · with_reducible assumption
           · with_reducible assumption)
    · left; ab_var; omega
  | goto ".LB.MappingBuilder.absorbSurplus.0" =>
    have hn : t.regs.rsi.toBitVec = Flat.NONE := beq_iff_eq.1 ‹_›
    cfg_goto
    · exact hli.stk rfl rfl
    · ab_inv
      refine ⟨M, w, hli.next rfl rfl rfl rfl rfl rfl rfl, hi.next rfl rfl rfl rfl rfl rfl, ?_, hrest⟩
      rw [hn] at hbest
      refine (best_none hlt' ?_ ?_).symm.trans hbest <;> with_reducible assumption
    · left; ab_var; omega

set_option maxHeartbeats 100000 in
theorem b_1 : absorbSurplusAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.MappingBuilder.absorbSurplus.1" → Obl B b F s ra fr₀ blk := by
  cfg_block [Obl]
  intro t ht
  ab_inv at ht
  obtain ⟨M, w, hli, hi, hbd, hbest, hrest⟩ := ht
  have hcx := hi.rcx
  have hom := hi.om
  kvcgen64
  all_goals try symexec_norm
  all_goals try simp only [hcx, sub_beq_zero] at *
  vc_by_shape
  | goto ".LB.MappingBuilder.absorbSurplus.3" =>
    have he : 1#64 + t.regs.rax.toBitVec = b.m := beq_iff_eq.1 ‹_›
    cfg_goto
    · exact hli.stk rfl rfl
    · ab_inv
      refine ⟨M, w, hli.next rfl rfl rfl rfl rfl rfl rfl, hi.jn, hi.hw, hi.hp, ?_, hrest⟩
      rw [BitVec.add_comm, he] at hbest
      exact (best_ge fun h => absurd h (BitVec.lt_irrefl _)).symm.trans hbest
    · left; ab_var; omega
  | other =>
    have hne : 1#64 + t.regs.rax.toBitVec ≠ b.m := by
      simpa using ‹(1#64 + t.regs.rax.toBitVec == b.m) = false›
    have hne' : (1#64 + t.regs.rax.toBitVec).toNat ≠ b.m.toNat :=
      fun e => hne (BitVec.eq_of_toNat_eq e)
    have e1 : (1#64 + t.regs.rax.toBitVec).toNat = t.regs.rax.toBitVec.toNat + 1 := by
      have := b.m.isLt
      bv_omega
    have hom' : (1#64 + t.regs.rax.toBitVec).toNat < b.m.toNat := by omega
    first
    | (left; ab_var; omega)
    | (ab_inv
       refine ⟨M, w, hli.next rfl rfl rfl rfl rfl rfl rfl,
         ⟨hi.jn, hi.hw, hi.hp, hom', hi.rcx, hi.rdi, hi.r8, ?_⟩, hbd, ?_, hrest⟩
       · show 1#64 + t.regs.rdx.toBitVec = 1#64 + t.regs.rax.toBitVec - t.regs.rbx.toBitVec
         rw [hi.rdx]
         bv_omega
       · show Flat.absorbBest _ _ _ (1#64 + t.regs.rax.toBitVec) _ = _
         rw [BitVec.add_comm]
         exact hbest)

set_option maxHeartbeats 100000 in
theorem b_0 : absorbSurplusAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.MappingBuilder.absorbSurplus.0" → Obl B b F s ra fr₀ blk := by
  cfg_block [Obl]
  intro t ht
  ab_inv at ht
  obtain ⟨M, w, hli, hi, hbest, hrest⟩ := ht
  kvcgen64
  all_goals try symexec_norm
  vc_by_shape
  | other =>
    first
    | (left; ab_var; omega)
    | (ab_inv
       exact ⟨M, w, hli.next rfl rfl rfl rfl rfl rfl rfl, hi.next rfl rfl rfl rfl rfl rfl,
         Or.inr (BitVec.lt_def.2 hi.om), hbest, hrest⟩)

set_option maxHeartbeats 100000 in
theorem b_3 (hout : ∀ l ∈ Program.labels absorbSurplusAsm, label l ≠ label "exit")
    (hmap : BSpecWithExit Names.map mapA 2 mapQ mapX) (hok : b.Ok) :
    absorbSurplusAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.MappingBuilder.absorbSurplus.3" → Obl B b F s ra fr₀ blk := by
  cfg_block [Obl]
  intro t ht
  ab_inv at ht
  obtain ⟨M, w, hli, hlt, hw, hp, hsi, hrest⟩ := ht
  have hokM : BG.Ok { b with M := M } := ⟨hok.m, hok.n, hok.sw, hok.tw, hok.db⟩
  simp only [Names.map] at hmap
  kvcgen64 [hmap]
  all_goals try symexec_norm
  all_goals try simp only [sub_beq_zero, neg_one_eq_none] at *
  vc_by_shape
  | goto ".LB.MappingBuilder.absorbSurplus.4" =>
    have hn : t.regs.rsi.toBitVec = Flat.NONE := beq_iff_eq.1 ‹_›
    have hskip := skip_none (fb := b.fl) (M := M) (BitVec.lt_def.2 hlt) (hsi.symm.trans hn)
    cfg_goto
    · exact hli.stk rfl rfl
    · ab_inv
      exact ⟨M, w, hli.next rfl rfl rfl rfl rfl rfl rfl, hlt, hskip.symm.trans hrest⟩
    · left; ab_var; omega
  | other =>
    have hne : t.regs.rsi.toBitVec ≠ Flat.NONE := by
      simpa using ‹(t.regs.rsi.toBitVec == Flat.NONE) = false›
    have hc : Flat.absorbBest b.fl M t.regs.rbx.toBitVec 0 Flat.NONE ≠ Flat.NONE :=
      fun e => hne (hsi.trans e)
    have hsm : t.regs.rsi.toBitVec.toNat < b.m.toNat := by
      rcases best_lt (fb := b.fl) (M := M) (j := t.regs.rbx.toBitVec) 0 Flat.NONE (Or.inl rfl)
        with h | h
      · exact absurd (hsi.trans h) hne
      · rw [hsi]; exact BitVec.lt_def.1 h
    refine Kb.vcallWithExit (V := BView) (A := mapA) (Q := mapQ) (X := mapX) (S := B) (s := s) (ra := ra) (w := w.ret)
      (F := F) (lo := [w.low0, w.low1])
      (hi := [w.pad, s.regs.rbx.toBitVec, s.regs.rbp.toBitVec]) (k := 2)
      ?kb rfl rfl ?rdi hokM ?A ?normal ?abort
    case kb => exact Kb.next hli.kb rfl rfl
    case rdi => exact hli.rbp
    case A => exact ⟨hsm, hlt⟩
    case normal =>
      intro t2 a' lo' w' hkb hl hQ hok' hag
      obtain ⟨w2, hli2, hbx⟩ := LI.after hag (hli.next rfl rfl rfl rfl rfl rfl rfl) hkb hl hQ.2
      have hal : al t2 = code (Flat.mbMap b.fl M t.regs.rsi.toBitVec t.regs.rbx.toBitVec).1 := hQ.1
      clear hQ hkb
      kvcgen64
      all_goals try symexec_norm
      vc_by_shape
      | goto ".LB.MappingBuilder.absorbSurplus.7" =>
        have hd := code_ne_zero fun e =>
          al_ne (by first
            | with_reducible assumption
            | (rw [Bool.not_eq_true']; with_reducible assumption)) (hal.trans e)
        have hf : Flat.absorbSurplus b.fl b.M = Flat.mbMap b.fl M t.regs.rsi.toBitVec t.regs.rbx.toBitVec := by
          rw [hsi] at hd ⊢
          exact hrest.symm.trans (from_fail (BitVec.lt_def.2 hlt) hw hp hc hd)
        cfg_goto
        · exact hli2.stk rfl rfl
        · ab_inv
          exact ⟨_, w2, hli2.next rfl rfl rfl rfl rfl rfl rfl, by rw [hf]; exact hal, by rw [hf]; rfl⟩
        · left; ab_var; omega
      | other =>
        have hd := code_eq_zero (hal.symm.trans
          (al_zero (by first
            | with_reducible assumption
            | (rw [Bool.not_eq_false']; with_reducible assumption))))
        have hdn : Flat.absorbFrom b.fl (Flat.mbMap b.fl M t.regs.rsi.toBitVec t.regs.rbx.toBitVec).2
            (t.regs.rbx.toBitVec + 1#64) = Flat.absorbSurplus b.fl b.M := by
          rw [hsi] at hd ⊢
          exact (from_done (BitVec.lt_def.2 hlt) hw hp hc hd).symm.trans hrest
        first
        | (left; ab_var; rw [hbx]; omega)
        | (ab_inv
           refine ⟨_, w2, hli2.next rfl rfl rfl rfl rfl rfl rfl, ?_, ?_⟩
           · show t2.regs.rbx.toBitVec.toNat < _; rw [hbx]; exact hlt
           · show Flat.absorbFrom _ _ (t2.regs.rbx.toBitVec + 1#64) = _
             rw [hbx]
             exact hdn)
    case abort =>
      intro t2 a' lo' w' hmem hl hrel hok' harg
      obtain ⟨ha', hf⟩ := hrel
      subst a'
      change Flat.mbMap b.fl M t.regs.rsi.toBitVec t.regs.rbx.toBitVec =
        (.assertionFailed, M) at hf
      have hd : (Flat.mbMap b.fl M t.regs.rsi.toBitVec t.regs.rbx.toBitVec).1 ≠ .done := by
        rw [hf]
        change Flat.Status.assertionFailed ≠ Flat.Status.done
        decide
      have hm : Flat.absorbSurplus b.fl b.M =
          Flat.mbMap b.fl M t.regs.rsi.toBitVec t.regs.rbx.toBitVec := by
        rw [hsi] at hd ⊢
        exact hrest.symm.trans (from_fail (BitVec.lt_def.2 hlt) hw hp hc hd)
      refine Or.inr ⟨Or.inr ⟨rfl, harg, ?_⟩, ?_⟩
      · refine ⟨{ b with M := M }, ?_, hokM,
          lo' ++ w' :: [w.pad, s.regs.rbx.toBitVec, s.regs.rbp.toBitVec], ra.toBitVec,
          by simp [hl], ?_⟩
        · constructor
          · rw [hm, hf]
          · rw [hm, hf]
        · simpa only [MProp.sep_assoc] using hmem
      · intro l hl ha
        exact False.elim (hout l hl ha)

end

end AbsorbU

end Bbu.Unit

namespace Bbu.Unit

open AbsorbU in
theorem absorbSurplus_unit [Host] [FunDecls]
    (hout : ∀ l ∈ Program.labels absorbSurplusAsm, label l ≠ label "exit") (hmap : BSpecWithExit Names.map mapA 2 mapQ mapX) :
    BThmWithExit absorbSurplusAsm absorbA 6 absorbQ absorbX := by
  intro B b F s ra
  refine ⟨fun s₀ ⟨h₀, hpre⟩ => ?_⟩
  subst h₀
  obtain ⟨fr₀, hfr, hk0⟩ := hpre.kg ra
  match fr₀, hfr, hk0 with
  | [w₀, w₁, w₂, w₃, w₄, w₅], hfr, hk0 =>
  refine Program.WP.cfg (AbsorbU.Inv B b F s ra [w₀, w₁, w₂, w₃, w₄, w₅]) (AbsorbU.V b) ?_ rfl
  refine forallBlocks_cases labels labels_cover fun l hl => ?_
  simp only [labels, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact b_entry B b F s ra _
  · exact b_fn B b F s ra hpre w₀ w₁ w₂ w₃ w₄ w₅ hk0
  · exact b_0 B b F s ra _
  · exact b_1 B b F s ra _
  · exact b_2 B b F s ra _ hpre.ok
  · exact b_3 B b F s ra _ hout hmap hpre.ok
  · exact b_4 B b F s ra _
  · exact b_5 B b F s ra _ hpre.ok
  · exact b_6 B b F s ra _
  · exact b_7 B b F s ra _ hpre.ok
  · exact b_8 B b F s ra _ hpre.ok hfr

end Bbu.Unit
