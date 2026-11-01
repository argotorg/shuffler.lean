module

public import BbuKraken.Unit.Plan.MapWildcard
import all BbuKraken.Unit.Plan.MapWildcard

@[expose] public section

/-!
# `MappingBuilder::keepWildcardSlots`

`c/bbu/<Names.keepWildcardSlots>.S`: the same frame and loop as `mapInPlace` (`InPlaceU`), with
an other test in block `.1`: a target wildcard slot `j` without a source, that `map` can take, is
given to `map` as `(j, j)`. Each turn of the loop is one unfold of `Flat.keepFrom`.
-/

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

set_option experimental.vcgen true

namespace Bbu.Unit

open Bbu.Sep

def keepWildA (_ : BG) (_ : MachineData) : Prop := True

def keepWildQ (b b' : BG) (_ t : MachineData) : Prop :=
  al t = code (Flat.keepWildcardSlots b.fl b.M).1
    ∧ b' = { b with M := (Flat.keepWildcardSlots b.fl b.M).2 }

namespace KeepU

open InPlaceU

/-! ### One turn of the loop -/

section
variable {fb : Flat.Builder} {M : Flat.Mapping} {j : Word}

theorem from_ge (h : ¬ j < Flat.commonSize fb) : Flat.keepFrom fb M j = (.done, M) := by
  rw [Flat.keepFrom, dite_eq_right h]

theorem from_skip (h : j < Flat.commonSize fb)
    (hc : (Flat.isWildcardTarget fb j && !Flat.hasSourceAssigned M j && Flat.mappable fb M j)
      = false) :
    Flat.keepFrom fb M j = Flat.keepFrom fb M (j + 1) := by
  rw [Flat.keepFrom, dite_eq_left h, hc]; rfl

theorem from_done (h : j < Flat.commonSize fb)
    (hc : (Flat.isWildcardTarget fb j && !Flat.hasSourceAssigned M j && Flat.mappable fb M j)
      = true)
    (hd : (Flat.mbMap fb M j j).1 = .done) :
    Flat.keepFrom fb M j = Flat.keepFrom fb (Flat.mbMap fb M j j).2 (j + 1) := by
  rw [Flat.keepFrom, dite_eq_left h, ite_eq_left hc]
  dsimp only
  rw [ite_eq_right (by simp [hd])]

theorem from_fail (h : j < Flat.commonSize fb)
    (hc : (Flat.isWildcardTarget fb j && !Flat.hasSourceAssigned M j && Flat.mappable fb M j)
      = true)
    (hd : (Flat.mbMap fb M j j).1 ≠ .done) :
    Flat.keepFrom fb M j = Flat.mbMap fb M j j := by
  rw [Flat.keepFrom, dite_eq_left h, ite_eq_left hc]
  dsimp only
  rw [ite_eq_left hd]

theorem skip_junk (h : j < Flat.commonSize fb) (hw : Flat.isWildcardTarget fb j = false) :
    Flat.keepFrom fb M j = Flat.keepFrom fb M (j + 1) :=
  from_skip h (by simp [hw])

theorem skip_pos (h : j < Flat.commonSize fb) (hp : (!(Flat.get M.pos j == Flat.NONE)) = true) :
    Flat.keepFrom fb M j = Flat.keepFrom fb M (j + 1) := by
  simp only [Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq] at hp
  exact from_skip h (by simp [Flat.hasSourceAssigned, hp])

theorem skip_drop (h : j < Flat.commonSize fb) (hd : (!(Flat.get fb.dropped j == 0)) = true) :
    Flat.keepFrom fb M j = Flat.keepFrom fb M (j + 1) := by
  rw [Bool.not_eq_true'] at hd
  exact from_skip h (by simp only [Flat.mappable, hd, Bool.false_and, Bool.and_false])

theorem skip_dest (h : j < Flat.commonSize fb) (hd : (!(Flat.get M.dest j == Flat.NONE)) = true) :
    Flat.keepFrom fb M j = Flat.keepFrom fb M (j + 1) := by
  rw [Bool.not_eq_true'] at hd
  exact from_skip h (by simp only [Flat.mappable, hd, Bool.and_false])

theorem cand_of (hw : Flat.isWildcardTarget fb j = true)
    (hp : (!(Flat.get M.pos j == Flat.NONE)) = false)
    (hd : (!(Flat.get fb.dropped j == 0)) = false) (hm : (!(Flat.get M.dest j == Flat.NONE)) = false) :
    (Flat.isWildcardTarget fb j && !Flat.hasSourceAssigned M j && Flat.mappable fb M j) = true := by
  rw [ClosestU.mappable_of hd hm, hw]
  simp only [Bool.not_eq_false', beq_iff_eq] at hp
  simp [Flat.hasSourceAssigned, hp]
end

/-! ### The invariant, the variant and the obligation of a block -/

def Inv (B : Addr) (b : BG) (F : MProp 64) (s : MachineData) (ra : Int64) (fr₀ : List Word) :
    CfgLabel → MachineData → Prop
  | .entry, t => t = s.pushRa ra
  | .exit, _ => False
  | .label l, t =>
    if l = Names.keepWildcardSlots then t = s.pushRa ra
    else if l = ".LB.MappingBuilder.keepWildcardSlots.0" then ∃ M w, LI B b F s ra M w t
      ∧ t.regs.rbx.toBitVec.toNat < (Flat.commonSize b.fl).toNat
      ∧ Flat.keepFrom b.fl M (t.regs.rbx.toBitVec + 1#64) = Flat.keepWildcardSlots b.fl b.M
    else if l = ".LB.MappingBuilder.keepWildcardSlots.1" then ∃ M w, LI B b F s ra M w t
      ∧ t.regs.rbx.toBitVec.toNat < (Flat.commonSize b.fl).toNat
      ∧ Flat.keepFrom b.fl M t.regs.rbx.toBitVec = Flat.keepWildcardSlots b.fl b.M
    else if l = ".LB.MappingBuilder.keepWildcardSlots.2" then ∃ M w, LI B b F s ra M w t
      ∧ Flat.keepWildcardSlots b.fl b.M = (.done, M)
    else if l = ".LB.MappingBuilder.keepWildcardSlots.3" then ∃ M w, LI B b F s ra M w t
      ∧ al t = code (Flat.keepWildcardSlots b.fl b.M).1 ∧ (Flat.keepWildcardSlots b.fl b.M).2 = M
    else if l = ".LB.MappingBuilder.keepWildcardSlots.4" then Kg (BView B b ∗ F) s ra fr₀ t
      ∧ Flat.keepWildcardSlots b.fl b.M = (.done, b.M)
    else False

-- The variant. A turn of the loop decreases `commonSize - rbx`.
def V (b : BG) (l : Label) (t : MachineData) : Nat :=
  if l = Names.keepWildcardSlots then 2 ^ 70
  else if l = ".LB.MappingBuilder.keepWildcardSlots.0" then
    2 * ((Flat.commonSize b.fl).toNat - t.regs.rbx.toBitVec.toNat)
  else if l = ".LB.MappingBuilder.keepWildcardSlots.1" then
    2 * ((Flat.commonSize b.fl).toNat - t.regs.rbx.toBitVec.toNat) + 1
  else 0

def E (B : Addr) (b : BG) (F : MProp 64) (s : MachineData) (ra : Int64) :
    Int64 → MachineData → Prop :=
  fun a t => a = ra ∧ VPost BView BG.Ok B F 3 (fun a' t => keepWildQ b a' s t) s t
    ∧ Sep.mod.Agree s t

def Obl [Host] [FunDecls] (B : Addr) (b : BG) (F : MProp 64) (s : MachineData) (ra : Int64)
    (fr₀ : List Word) (blk : Program.Block) : Prop :=
  ∀ t, Inv B b F s ra fr₀ blk.label t →
    let I' (c : CfgLabel) (j : Nat) (_ : Unit) (u : MachineData) :=
      Inv B b F s ra fr₀ c u ∧ Program.Decreases (V b) blk.label blk.idx t c j u
    WP.wp blk.body (I' blk.next (blk.idx + 1))
      (Program.Intercept (Program.labels keepWildcardSlotsAsm) (s.pushRa ra) I' (E B b F s ra)) t

def labels : List CfgLabel :=
  [.entry, .label Names.keepWildcardSlots,
    .label ".LB.MappingBuilder.keepWildcardSlots.0", .label ".LB.MappingBuilder.keepWildcardSlots.1",
    .label ".LB.MappingBuilder.keepWildcardSlots.2", .label ".LB.MappingBuilder.keepWildcardSlots.3",
    .label ".LB.MappingBuilder.keepWildcardSlots.4"]

theorem labels_cover : keepWildcardSlotsAsm.ForallBlocks fun blk => blk.label ∈ labels := by
  simp only [labels, Names.keepWildcardSlots]
  cfg_labels

macro "kw_inv" : tactic => `(tactic|
  simp only [Inv, Names.keepWildcardSlots, String.reduceEq, ↓reduceIte])
macro "kw_inv" "at" h:ident : tactic => `(tactic|
  simp only [Inv, Names.keepWildcardSlots, String.reduceEq, ↓reduceIte] at $h:ident)
macro "kw_var" : tactic => `(tactic|
  simp only [V, Names.keepWildcardSlots, String.reduceEq, ↓reduceIte])

/-! ### The blocks -/

open ShallowestCopy

section
variable [Host] [FunDecls] (B : Addr) (b : BG) (F : MProp 64) (s : MachineData) (ra : Int64)
  (fr₀ : List Word)

set_option maxHeartbeats 100000 in
theorem b_entry : keepWildcardSlotsAsm.ForallBlocks fun blk =>
    blk.label = .entry → Obl B b F s ra fr₀ blk := by
  cfg_block [Obl]
  intro t ht
  kvcgen64
  kw_inv
  exact ht

set_option maxHeartbeats 100000 in
theorem b_fn (hpre : VPre BView BG.Ok B b F keepWildA 3 s) (w₀ w₁ w₂ : Word)
    (hk0 : Kg (BView B b ∗ F) s ra [w₀, w₁, w₂] (s.pushRa ra)) :
    keepWildcardSlotsAsm.ForallBlocks fun blk =>
      blk.label = .label Names.keepWildcardSlots → Obl B b F s ra [w₀, w₁, w₂] blk := by
  cfg_block [Obl, Names.keepWildcardSlots]
  intro t ht
  kw_inv at ht
  subst ht
  have hrdi : (s.pushRa ra).regs.rdi.toBitVec = B := by
    simpa [MachineData.pushRa] using hpre.rdi
  have hm0 := hk0.vmem
  have hq : (s.pushRa ra).regs.rsp.toBitVec = rsp s - 8#64 := by
    rw [← Reg64s.get64_rsp, hk0.sp64]
  have hsp2 : (s.pushRa ra).regs.rsp.toBitVec - 8#64 - 8#64 = rsp s - 8#64 - 16#64 := by
    rw [hq]; bv_omega
  obtain ⟨hpo, hpm⟩ := hk0.pushes (xs := [(s.pushRa ra).regs.rbp.toBitVec,
    (s.pushRa ra).regs.rbx.toBitVec]) (by simp)
  simp only [pushes] at hpm
  change (Stk (rsp s) (fr s w₀) ra.toBitVec ∗ BView B b ∗ F).get _ at hpm
  simp only [PushOk] at hpo
  obtain ⟨p1, p2, -⟩ := hpo
  have h_m := BView.rd_m hm0
  have h_n := BView.rd_n hm0
  unfold rd at h_m h_n
  have k_m := BView.isSome_m hm0
  have k_n := BView.isSome_n hm0
  clear hm0
  kvcgen64
  all_goals try symexec_norm
  all_goals try simp only [hrdi, h_m, h_n] at *
  vc_by_shape
  | load =>
    first
    | with_reducible exact k_m
    | with_reducible exact k_n
    | with_reducible exact p1
    | with_reducible exact p2
  | goto ".LB.MappingBuilder.keepWildcardSlots.4" =>
    rename_i hc
    have h0 := zf_true hc
    rw [cmova] at h0
    cfg_goto
    · exact (hk0.next rfl rfl rfl rfl rfl rfl rfl rfl).stack
    · kw_inv
      exact ⟨hk0.next rfl rfl rfl rfl rfl rfl rfl rfl,
        from_ge (by show ¬ (0 : Word) < (if b.m < b.n then b.m else b.n); rw [h0]; decide)⟩
    · simp [V, Names.keepWildcardSlots]
  | goto ".LB.MappingBuilder.keepWildcardSlots.1" =>
    rename_i hc
    have h0 := zf_false hc
    rw [cmova] at h0
    have hcs : 0 < (Flat.commonSize b.fl).toNat :=
      Nat.pos_of_ne_zero fun h => h0 (BitVec.eq_of_toNat_eq h)
    cfg_goto
    · exact Kb.stack ⟨hpm, hsp2⟩ (by decide)
    · kw_inv
      exact ⟨b.M, w₀, ⟨⟨hpm, hsp2⟩, by simpa [MachineData.pushRa] using hpre.rdi, rfl, rfl, rfl, rfl⟩,
        hcs, rfl⟩
    · left; have := (Flat.commonSize b.fl).isLt; simp [V, Names.keepWildcardSlots]; omega

set_option maxHeartbeats 100000 in
theorem b_0 : keepWildcardSlotsAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.MappingBuilder.keepWildcardSlots.0" → Obl B b F s ra fr₀ blk := by
  cfg_block [Obl]
  intro t ht
  kw_inv at ht
  obtain ⟨M, w, hli, hlt, hrest⟩ := ht
  have hb := hli.kb.mem
  rw [sep_lc] at hb
  have hbp := hli.rbp
  have h_m := BView.rd_m hb
  have h_n := BView.rd_n hb
  unfold rd at h_m h_n
  have k_m := BView.isSome_m hb
  have k_n := BView.isSome_n hb
  clear hb
  kvcgen64
  all_goals try symexec_norm
  all_goals try simp only [hbp, h_m, h_n] at *
  all_goals try rw [cmova] at *
  vc_by_shape
  | load =>
    first
    | with_reducible exact k_m
    | with_reducible exact k_n
  | goto ".LB.MappingBuilder.keepWildcardSlots.2" =>
    have hge := jnb_true _ _ (by assumption)
    rw [BitVec.add_comm] at hge
    cfg_goto
    · exact hli.stk rfl rfl
    · kw_inv
      exact ⟨M, w, hli.next rfl rfl rfl rfl rfl rfl rfl,
        hrest.symm.trans (from_ge fun h => absurd (BitVec.lt_def.1 h) (Nat.not_lt.2 hge))⟩
    · left; kw_var; omega
  | other =>
    have hlt' := jnb_false _ _ (by assumption)
    first
    | (left
       kw_var
       have e : (1#64 + t.regs.rbx.toBitVec).toNat = t.regs.rbx.toBitVec.toNat + 1 := by bv_omega
       omega)
    | (kw_inv
       refine ⟨M, w, hli.next rfl rfl rfl rfl rfl rfl rfl, hlt', ?_⟩
       rw [BitVec.add_comm]
       exact hrest)

theorem b_1 (hmap : BSpec Names.map mapA 0 mapQ) (hok : b.Ok) :
    keepWildcardSlotsAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.MappingBuilder.keepWildcardSlots.1" → Obl B b F s ra fr₀ blk := by
  cfg_block [Obl]
  intro t ht
  kw_inv at ht
  obtain ⟨M, w, hli, hlt, hrest⟩ := ht
  have hokM : BG.Ok { b with M := M } := ⟨hok.m, hok.n, hok.sw, hok.tw, hok.db⟩
  have hb := hli.kb.mem
  rw [sep_lc] at hb
  have hbp := hli.rbp
  have hm : t.regs.rbx.toBitVec.toNat < b.m.toNat := Nat.lt_of_lt_of_le hlt (cs_le_m b.fl)
  have hn : t.regs.rbx.toBitVec.toNat < b.n.toNat := Nat.lt_of_lt_of_le hlt (cs_le_n b.fl)
  have hmax : t.regs.rbx.toBitVec.toNat < MAX_N := Nat.lt_of_lt_of_le hm hok.m
  obtain ⟨_, hM⟩ := BView.mapM hb
  have h_tgt := BView.rd_tgt hb
  have h_drp := BView.rd_drp hb
  have h_mp := BView.rd_mp hb
  have h_kind := BView.rdb_kind hb hokM hn
  have h_db : rdb t.dmem (b.drp + t.regs.rbx.toBitVec) = Flat.get b.fl.dropped t.regs.rbx.toBitVec :=
    BView.rdb_drp (b := { b with M := M }) hb hokM hm
  have h_pos := MapM.rd_pos hM hmax
  have h_dst := MapM.rd_dest hM hmax
  unfold rd at h_tgt h_drp h_mp h_pos h_dst
  unfold rdb at h_db h_kind
  have k_tgt := BView.isSome_tgt hb
  have k_drp := BView.isSome_drp hb
  have k_mp := BView.isSome_mp hb
  have k_kind := BView.isSome_kind hb hokM hn
  have k_db := BView.isSome_drp_byte hb hokM hm
  have k_pos := MapM.isSome_pos hM hmax
  have k_dst := MapM.isSome_dest hM hmax
  clear hb hM
  simp only [Names.map] at hmap
  kvcgen64 [hmap]
  all_goals try symexec_norm
  all_goals try simp only [hbp, h_tgt, h_drp, h_mp, h_db, fold_slot, slot_8192, h_pos, h_dst,
    sub_beq_zero, neg_one_eq_none, ClosestU.byte_ne0] at *
  vc_by_shape
  | load =>
    first
    | with_reducible exact k_tgt
    | with_reducible exact k_drp
    | with_reducible exact k_mp
    | with_reducible exact k_kind
    | with_reducible exact k_db
    | with_reducible exact k_pos
    | with_reducible exact k_dst
  | goto ".LB.MappingBuilder.keepWildcardSlots.0" =>
    have hskip : Flat.keepFrom b.fl M t.regs.rbx.toBitVec
        = Flat.keepFrom b.fl M (t.regs.rbx.toBitVec + 1#64) := by
      first
      | (refine skip_dest (BitVec.lt_def.2 hlt) ?_; with_reducible assumption)
      | (refine skip_drop (BitVec.lt_def.2 hlt) ?_; with_reducible assumption)
      | (refine skip_pos (BitVec.lt_def.2 hlt) ?_; with_reducible assumption)
      | (refine skip_junk (BitVec.lt_def.2 hlt) ?_
         exact (CopiesU.junk_flag (fb := b.fl) hn h_kind).symm.trans
           (by rw [← Bool.not_eq_true']; with_reducible assumption))
      | (refine skip_junk (BitVec.lt_def.2 hlt) ?_
         exact (CopiesU.junk_flag (fb := b.fl) hn h_kind).symm.trans ‹_›)
    cfg_goto
    · exact hli.stk rfl rfl
    · kw_inv
      exact ⟨M, w, hli.next rfl rfl rfl rfl rfl rfl rfl, hlt, hskip.symm.trans hrest⟩
    · left; kw_var; omega
  | other =>
    have hw : Flat.isWildcardTarget b.fl t.regs.rbx.toBitVec = true := by
      first
      | exact (CopiesU.junk_flag (fb := b.fl) hn h_kind).symm.trans ‹_›
      | exact (CopiesU.junk_flag (fb := b.fl) hn h_kind).symm.trans
          (by rw [← Bool.not_eq_false']; with_reducible assumption)
    have hcand := cand_of (fb := b.fl) (M := M) (j := t.regs.rbx.toBitVec) hw
      (by with_reducible assumption) (by with_reducible assumption) (by with_reducible assumption)
    clear hw h_kind
    refine Kb.vcall (V := BView) (A := mapA) (Q := mapQ) (S := B) (s := s) (ra := ra) (w := w)
      (F := F) (lo := []) (hi := [s.regs.rbx.toBitVec, s.regs.rbp.toBitVec]) (k := 0)
      ?kb rfl rfl ?rdi hokM ?A ?_
    case kb => exact Kb.next hli.kb rfl rfl
    case rdi => exact hli.rbp
    case A => exact ⟨hm, hn⟩
    intro t2 a' lo' w' hkb hl hQ hok' hag
    obtain ⟨hli2, hbx⟩ := LI.after hag (hli.next rfl rfl rfl rfl rfl rfl rfl) hkb hl hQ.2
    have hal : al t2 = code (Flat.mbMap b.fl M t.regs.rbx.toBitVec t.regs.rbx.toBitVec).1 := hQ.1
    clear hQ hkb
    kvcgen64
    all_goals try symexec_norm
    vc_by_shape
    | goto ".LB.MappingBuilder.keepWildcardSlots.0" =>
      have hd := code_eq_zero (hal.symm.trans
        (al_zero (by rw [Bool.not_eq_false']; with_reducible assumption)))
      cfg_goto
      · exact hli2.stk rfl rfl
      · kw_inv
        refine ⟨_, w', hli2.next rfl rfl rfl rfl rfl rfl rfl, ?_, ?_⟩
        · show t2.regs.rbx.toBitVec.toNat < _; rw [hbx]; exact hlt
        · show Flat.keepFrom _ _ (t2.regs.rbx.toBitVec + 1#64) = _
          rw [hbx]
          exact (from_done (BitVec.lt_def.2 hlt) hcand hd).symm.trans hrest
      · left; kw_var; rw [hbx]; omega
    | goto ".LB.MappingBuilder.keepWildcardSlots.3" =>
      have hd := code_ne_zero fun e =>
        al_ne (by rw [Bool.not_eq_true']; with_reducible assumption) (hal.trans e)
      have hf := hrest.symm.trans (from_fail (BitVec.lt_def.2 hlt) hcand hd)
      cfg_goto
      · exact hli2.stk rfl rfl
      · kw_inv
        exact ⟨_, w', hli2.next rfl rfl rfl rfl rfl rfl rfl, by rw [hf]; exact hal, by rw [hf]; rfl⟩
      · left; kw_var; omega
set_option maxHeartbeats 100000 in
theorem b_2 : keepWildcardSlotsAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.MappingBuilder.keepWildcardSlots.2" → Obl B b F s ra fr₀ blk := by
  cfg_block [Obl]
  intro t ht
  kw_inv at ht
  obtain ⟨M, w, hli, hd⟩ := ht
  kvcgen64
  all_goals try symexec_norm
  vc_by_shape
  | other =>
    first
    | (right; exact ⟨by kw_var, Nat.lt_succ_self _⟩)
    | (kw_inv
       exact ⟨M, w, hli.next rfl rfl rfl rfl rfl rfl rfl, by rw [hd]; rfl, by rw [hd]⟩)

set_option maxHeartbeats 100000 in
theorem b_3 (hok : b.Ok) : keepWildcardSlotsAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.MappingBuilder.keepWildcardSlots.3" → Obl B b F s ra fr₀ blk := by
  cfg_block [Obl]
  intro t ht
  kw_inv at ht
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
    refine Option.isSome_iff_exists.mpr ⟨ra, Kg.retAddr (P := BView B { b with M := M } ∗ F) (s := s) (fr := fr s w) ?_⟩
    exact hli.pop_kg rfl (by bv_omega) rfl rfl rfl rfl rfl rfl
  | ret =>
    refine Kg.vret (ok := BG.Ok) (a' := { b with M := M })
      (hli.pop_kg rfl (by bv_omega) rfl rfl rfl rfl rfl rfl) rfl hokM
      fun t' _ hax => ⟨?_, by rw [hM]⟩
    simp only [al] at hal ⊢
    rw [hax]
    exact hal

set_option maxHeartbeats 100000 in
theorem b_4 (hok : b.Ok) (hfr : fr₀.length = 3) : keepWildcardSlotsAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.MappingBuilder.keepWildcardSlots.4" → Obl B b F s ra fr₀ blk := by
  cfg_block [Obl]
  intro t ht
  kw_inv at ht
  obtain ⟨hk, hd⟩ := ht
  kvcgen64
  all_goals try symexec_norm
  vc_by_shape
  | retAddr =>
    exact Option.isSome_iff_exists.mpr ⟨ra, (hk.next rfl rfl rfl rfl rfl rfl rfl rfl).retAddr⟩
  | ret =>
    refine Kg.vret (ok := BG.Ok) (a' := b) (hk.next rfl rfl rfl rfl rfl rfl rfl rfl) hfr hok
      fun t' _ hax => ⟨?_, by rw [hd]⟩
    simp only [al]
    rw [hax, hd]
    rfl

end

end KeepU

open KeepU in
theorem keepWildcardSlots_unit [Host] [FunDecls] (hmap : BSpec Names.map mapA 0 mapQ) :
    BThm keepWildcardSlotsAsm keepWildA 3 keepWildQ := by
  intro B b F s ra
  refine ⟨fun s₀ ⟨h₀, hpre⟩ => ?_⟩
  subst h₀
  obtain ⟨fr₀, hfr, hk0⟩ := hpre.kg ra
  match fr₀, hfr, hk0 with
  | [w₀, w₁, w₂], hfr, hk0 =>
  refine Program.WP.cfg (KeepU.Inv B b F s ra [w₀, w₁, w₂]) (KeepU.V b) ?_ rfl
  refine forallBlocks_cases labels labels_cover fun l hl => ?_
  simp only [labels, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact b_entry B b F s ra _
  · exact b_fn B b F s ra hpre w₀ w₁ w₂ hk0
  · exact b_0 B b F s ra _
  · exact b_1 B b F s ra _ hmap hpre.ok
  · exact b_2 B b F s ra _
  · exact b_3 B b F s ra _ hpre.ok
  · exact b_4 B b F s ra _ hpre.ok hfr

end Bbu.Unit
