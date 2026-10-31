import BbuKraken.Unit.Plan.MapInPlace

/-!
# `MappingBuilder::mapClosestCopies`

`c/bbu/<Names.mapClosestCopies>.S`: if `n = 0` it returns `DONE` at once. Else it pushes `rbp`,
`rbx` and runs the loop over the targets `rbx < n`. `rbp` is the builder. Each turn of the loop
is one unfold of `Flat.closestCopiesFrom`: for a target with no source that is not a wildcard,
`closestCopy` gives a copy and `map` maps the copy to the target. A status other than `DONE`
stops the loop. The frame of the loop is the four free words of `closestCopy`, the return slot
of the callees and the saved `rbx`, `rbp`.
-/

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

set_option experimental.vcgen true

namespace Bbu.Unit

open Bbu.Sep

def mapClosestA (_ : BG) (_ : MachineData) : Prop := True

def mapClosestQ (b b' : BG) (_ t : MachineData) : Prop :=
  al t = code (Flat.mapClosestCopies b.fl b.M).1
    ∧ b' = { b with M := (Flat.mapClosestCopies b.fl b.M).2 }

namespace CopiesU

-- The frame of the body: the free words of `closestCopy`, the return slot of the callees, then
-- the saved `rbx` and `rbp`.
def fr (s : MachineData) (lo : List Word) (w : Word) : List Word :=
  lo ++ w :: [s.regs.rbx.toBitVec, s.regs.rbp.toBitVec]

-- The registers in the loop. `M` is the `Mapping` so far.
structure LI (B : Addr) (b : BG) (F : MProp 64) (s : MachineData) (ra : Int64)
    (M : Flat.Mapping) (lo : List Word) (w : Word) (t : MachineData) : Prop where
  kb : Kb (BView B { b with M := M } ∗ F) s ra (fr s lo w) 16#64 t
  hl : lo.length = 4
  rbp : t.regs.rbp.toBitVec = B
  r12 : t.regs.r12 = s.regs.r12
  r13 : t.regs.r13 = s.regs.r13
  r14 : t.regs.r14 = s.regs.r14
  r15 : t.regs.r15 = s.regs.r15

/-! ### One turn of the loop -/

section
variable {fb : Flat.Builder} {M : Flat.Mapping} {t inW : Bool} {j i best : Word}

-- The result of `closestCopy` is `NONE` or a source position.
theorem closestFrom_lt {t : Word} {inW : Bool} :
    ∀ i best, (best = Flat.NONE ∨ best < fb.m) →
      Flat.closestFrom fb M t inW i best = Flat.NONE ∨ Flat.closestFrom fb M t inW i best < fb.m := by
  intro i best hb
  fun_induction Flat.closestFrom fb M t inW i best with
  | case1 i best h best' ih =>
    apply ih
    dsimp only [best']
    split
    · split
      · exact Or.inr h
      · exact hb
    · exact hb
  | case2 i best h => exact hb

theorem closestCopy_lt {t : Word} {inW : Bool} (h : Flat.closestCopy fb M t inW ≠ Flat.NONE) :
    Flat.closestCopy fb M t inW < fb.m :=
  (closestFrom_lt 0 Flat.NONE (Or.inl rfl)).resolve_left h

theorem from_ge (h : ¬ j < fb.n) : Flat.closestCopiesFrom fb M j = (.done, M) := by
  rw [Flat.closestCopiesFrom, dite_eq_right h]

theorem skip_pos (h : j < fb.n) (hp : (!(Flat.get M.pos j == Flat.NONE)) = true) :
    Flat.closestCopiesFrom fb M j = Flat.closestCopiesFrom fb M (j + 1) := by
  rw [Flat.closestCopiesFrom, dite_eq_left h]
  simp only [Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq] at hp
  simp [Flat.hasSourceAssigned, hp]

theorem skip_junk (h : j < fb.n) (hw : Flat.isWildcardTarget fb j = true) :
    Flat.closestCopiesFrom fb M j = Flat.closestCopiesFrom fb M (j + 1) := by
  rw [Flat.closestCopiesFrom, dite_eq_left h]
  simp [hw]

theorem skip_none (h : j < fb.n) (hc : Flat.closestCopy fb M j false = Flat.NONE) :
    Flat.closestCopiesFrom fb M j = Flat.closestCopiesFrom fb M (j + 1) := by
  rw [Flat.closestCopiesFrom, dite_eq_left h]
  simp [hc]

theorem from_done (h : j < fb.n) (hp : (!(Flat.get M.pos j == Flat.NONE)) = false)
    (hw : Flat.isWildcardTarget fb j = false) (hc : Flat.closestCopy fb M j false ≠ Flat.NONE)
    (hd : (Flat.mbMap fb M (Flat.closestCopy fb M j false) j).1 = .done) :
    Flat.closestCopiesFrom fb M j
      = Flat.closestCopiesFrom fb (Flat.mbMap fb M (Flat.closestCopy fb M j false) j).2 (j + 1) := by
  rw [Flat.closestCopiesFrom, dite_eq_left h]
  simp only [Bool.not_eq_false', beq_iff_eq] at hp
  simp [Flat.hasSourceAssigned, hp, hw, hc, hd]

theorem from_fail (h : j < fb.n) (hp : (!(Flat.get M.pos j == Flat.NONE)) = false)
    (hw : Flat.isWildcardTarget fb j = false) (hc : Flat.closestCopy fb M j false ≠ Flat.NONE)
    (hd : (Flat.mbMap fb M (Flat.closestCopy fb M j false) j).1 ≠ .done) :
    Flat.closestCopiesFrom fb M j = Flat.mbMap fb M (Flat.closestCopy fb M j false) j := by
  rw [Flat.closestCopiesFrom, dite_eq_left h]
  simp only [Bool.not_eq_false', beq_iff_eq] at hp
  simp [Flat.hasSourceAssigned, hp, hw, hc, hd]

-- `cmpb $1, 4(%rax,%rdx)`: target slot `j` is a wildcard.
theorem junk_flag {x : BitVec 8} (hn : j.toNat < fb.n.toNat) (hk : x = (Flat.get fb.target j).kind) :
    (x - 1#8 == BitVec.zero 8) = Flat.isWildcardTarget fb j := by
  rw [ClosestU.kind_flag hn hk]
  simp [Flat.inWildcardSlot, BitVec.lt_def, hn]
end

/-! ### The registers -/

section
variable {B : Addr} {b : BG} {F : MProp 64} {s t t' : MachineData} {ra : Int64}
  {M : Flat.Mapping} {lo : List Word} {w : Word}

theorem LI.next (h : LI B b F s ra M lo w t) (hm : t'.dmem = t.dmem)
    (hsp : t'.regs.rsp = t.regs.rsp) (hbp : t'.regs.rbp = t.regs.rbp)
    (h12 : t'.regs.r12 = t.regs.r12) (h13 : t'.regs.r13 = t.regs.r13)
    (h14 : t'.regs.r14 = t.regs.r14) (h15 : t'.regs.r15 = t.regs.r15) : LI B b F s ra M lo w t' :=
  ⟨h.kb.next hm hsp, h.hl, by rw [hbp]; exact h.rbp, h12 ▸ h.r12, h13 ▸ h.r13, h14 ▸ h.r14,
    h15 ▸ h.r15⟩

theorem LI.stk (h : LI B b F s ra M lo w t) (hm : t'.dmem = t.dmem)
    (hsp : t'.regs.rsp = t.regs.rsp) : t'.StackAtOrBelow (s.pushRa ra) :=
  (h.kb.next hm hsp).stack (by decide)

-- The state after a call: the callees keep `rbx`, `rbp` and `r12`…`r15`.
theorem LI.after {c : MachineData} {M' : Flat.Mapping} {a' : BG} {xs lo' : List Word} {w' : Word}
    (hag : Sep.mod.Agree c t) (h : LI B b F s ra M lo w c)
    (hkb : Kb (BView B a' ∗ F) s ra
      (xs ++ lo' ++ w' :: [s.regs.rbx.toBitVec, s.regs.rbp.toBitVec]) 16#64 t)
    (hl : (xs ++ lo').length = 4) (ha : a' = { b with M := M' }) :
    LI B b F s ra M' (xs ++ lo') w' t ∧ t.regs.rbx = c.regs.rbx := by
  subst ha
  refine ⟨⟨by rw [fr]; exact hkb, hl, ?_, ?_, ?_, ?_, ?_⟩,
    mod_keep hag (by simp [Sep.mod]) Reg64s.get64_rbx⟩
  · rw [mod_keep hag (by simp [Sep.mod]) Reg64s.get64_rbp]; exact h.rbp
  · rw [mod_keep hag (by simp [Sep.mod]) Reg64s.get64_r12]; exact h.r12
  · rw [mod_keep hag (by simp [Sep.mod]) Reg64s.get64_r13]; exact h.r13
  · rw [mod_keep hag (by simp [Sep.mod]) Reg64s.get64_r14]; exact h.r14
  · rw [mod_keep hag (by simp [Sep.mod]) Reg64s.get64_r15]; exact h.r15

theorem LI.pop_isSome (h : LI B b F s ra M lo w t) :
    (t.dmem.loadInt t.regs.rsp.toBitVec 8).isSome = true
      ∧ (t.dmem.loadInt (t.regs.rsp.toBitVec + 8#64) 8).isSome = true := by
  obtain ⟨e0, e1⟩ := InPlaceU.pop_addr t.regs.rsp.toBitVec
  refine ⟨?_, ?_⟩
  · rw [e0]; exact Kb.isSome_hi (lo := lo ++ [w]) (hi := [s.regs.rbx.toBitVec, s.regs.rbp.toBitVec])
      (by simpa [fr] using h.kb) rfl (by simp)
  · rw [e1]; exact Kb.isSome_hi (lo := lo ++ [w]) (hi := [s.regs.rbx.toBitVec, s.regs.rbp.toBitVec])
      (by simpa [fr] using h.kb) rfl (by simp)

-- The state after the pops.
theorem LI.pop_kg (h : LI B b F s ra M lo w t) (hm : t'.dmem = t.dmem)
    (hsp : t'.regs.rsp.toBitVec = t.regs.rsp.toBitVec + 8#64 + 8#64)
    (hbx : t'.regs.rbx.toBitVec = rd t.dmem t.regs.rsp.toBitVec)
    (hbp : t'.regs.rbp.toBitVec = rd t.dmem (t.regs.rsp.toBitVec + 8#64))
    (h12 : t'.regs.r12 = t.regs.r12) (h13 : t'.regs.r13 = t.regs.r13)
    (h14 : t'.regs.r14 = t.regs.r14) (h15 : t'.regs.r15 = t.regs.r15) :
    Kg (BView B { b with M := M } ∗ F) s ra (fr s lo w) t' := by
  obtain ⟨e0, e1⟩ := InPlaceU.pop_addr t.regs.rsp.toBitVec
  have hkb : Kb (BView B { b with M := M } ∗ F) s ra
      ((lo ++ [w]) ++ [s.regs.rbx.toBitVec, s.regs.rbp.toBitVec]) 16#64 t := by
    simpa [fr] using h.kb
  refine h.kb.kg hm ?_ ?_ ?_ (h12.trans h.r12) (h13.trans h.r13) (h14.trans h.r14)
    (h15.trans h.r15) <;> (try apply UInt64.toBitVec_inj.mp)
  · rw [hsp, h.kb.sp]; bv_omega
  · rw [hbx, e0]
    exact Kb.rd_hi (hi := [s.regs.rbx.toBitVec, s.regs.rbp.toBitVec]) hkb rfl (i := 0) (by simp)
  · rw [hbp, e1]
    exact Kb.rd_hi (hi := [s.regs.rbx.toBitVec, s.regs.rbp.toBitVec]) hkb rfl (i := 1) (by simp)
end

/-! ### The invariant, the variant and the obligation of a block -/

def Inv (B : Addr) (b : BG) (F : MProp 64) (s : MachineData) (ra : Int64) (fr₀ : List Word) :
    CfgLabel → MachineData → Prop
  | .entry, t => t = s.pushRa ra
  | .exit, _ => False
  | .label l, t =>
    if l = Names.mapClosestCopies then t = s.pushRa ra
    else if l = ".LB.MappingBuilder.mapClosestCopies.0" then ∃ M lo w, LI B b F s ra M lo w t
      ∧ t.regs.rbx.toBitVec.toNat < b.n.toNat
      ∧ Flat.closestCopiesFrom b.fl M (t.regs.rbx.toBitVec + 1#64)
        = Flat.mapClosestCopies b.fl b.M
    else if l = ".LB.MappingBuilder.mapClosestCopies.1" then ∃ M lo w, LI B b F s ra M lo w t
      ∧ t.regs.rbx.toBitVec.toNat < b.n.toNat
      ∧ Flat.closestCopiesFrom b.fl M t.regs.rbx.toBitVec = Flat.mapClosestCopies b.fl b.M
    else if l = ".LB.MappingBuilder.mapClosestCopies.2" then ∃ M lo w, LI B b F s ra M lo w t
      ∧ Flat.mapClosestCopies b.fl b.M = (.done, M)
    else if l = ".LB.MappingBuilder.mapClosestCopies.3" then ∃ M lo w, LI B b F s ra M lo w t
      ∧ al t = code (Flat.mapClosestCopies b.fl b.M).1 ∧ (Flat.mapClosestCopies b.fl b.M).2 = M
    else if l = ".LB.MappingBuilder.mapClosestCopies.4" then Kg (BView B b ∗ F) s ra fr₀ t
      ∧ Flat.mapClosestCopies b.fl b.M = (.done, b.M)
    else False

-- The variant. A turn of the loop decreases `n - rbx`.
def V (b : BG) (l : Label) (t : MachineData) : Nat :=
  if l = Names.mapClosestCopies then 2 ^ 70
  else if l = ".LB.MappingBuilder.mapClosestCopies.0" then
    2 * (b.n.toNat - t.regs.rbx.toBitVec.toNat)
  else if l = ".LB.MappingBuilder.mapClosestCopies.1" then
    2 * (b.n.toNat - t.regs.rbx.toBitVec.toNat) + 1
  else 0

def E (B : Addr) (b : BG) (F : MProp 64) (s : MachineData) (ra : Int64) :
    Int64 → MachineData → Prop :=
  fun a t => a = ra ∧ VPost BView BG.Ok B F 7 (fun a' t => mapClosestQ b a' s t) s t
    ∧ Sep.mod.Agree s t

def Obl [Host] [FunDecls] (B : Addr) (b : BG) (F : MProp 64) (s : MachineData) (ra : Int64)
    (fr₀ : List Word) (blk : Program.Block) : Prop :=
  ∀ t, Inv B b F s ra fr₀ blk.label t →
    let I' (c : CfgLabel) (j : Nat) (_ : Unit) (u : MachineData) :=
      Inv B b F s ra fr₀ c u ∧ Program.Decreases (V b) blk.label blk.idx t c j u
    WP.wp blk.body (I' blk.next (blk.idx + 1))
      (Program.Intercept (Program.labels mapClosestCopiesAsm) (s.pushRa ra) I' (E B b F s ra)) t

def labels : List CfgLabel :=
  [.entry, .label Names.mapClosestCopies,
    .label ".LB.MappingBuilder.mapClosestCopies.0", .label ".LB.MappingBuilder.mapClosestCopies.1",
    .label ".LB.MappingBuilder.mapClosestCopies.2", .label ".LB.MappingBuilder.mapClosestCopies.3",
    .label ".LB.MappingBuilder.mapClosestCopies.4"]

theorem labels_cover : mapClosestCopiesAsm.ForallBlocks fun blk => blk.label ∈ labels := by
  simp only [labels, Names.mapClosestCopies]
  cfg_labels

macro "mc_inv" : tactic => `(tactic|
  simp only [Inv, Names.mapClosestCopies, String.reduceEq, ↓reduceIte])
macro "mc_inv" "at" h:ident : tactic => `(tactic|
  simp only [Inv, Names.mapClosestCopies, String.reduceEq, ↓reduceIte] at $h:ident)
macro "mc_var" : tactic => `(tactic|
  simp only [V, Names.mapClosestCopies, String.reduceEq, ↓reduceIte])

/-! ### The blocks -/

open ShallowestCopy

section
variable [Host] [FunDecls] (B : Addr) (b : BG) (F : MProp 64) (s : MachineData) (ra : Int64)
  (fr₀ : List Word)

set_option maxHeartbeats 100000 in
theorem b_entry : mapClosestCopiesAsm.ForallBlocks fun blk =>
    blk.label = .entry → Obl B b F s ra fr₀ blk := by
  cfg_block [Obl]
  intro t ht
  kvcgen64
  mc_inv
  exact ht

set_option maxHeartbeats 100000 in
theorem b_fn (hpre : VPre BView BG.Ok B b F mapClosestA 7 s) (w₀ w₁ w₂ w₃ w₄ w₅ w₆ : Word)
    (hk0 : Kg (BView B b ∗ F) s ra [w₀, w₁, w₂, w₃, w₄, w₅, w₆] (s.pushRa ra)) :
    mapClosestCopiesAsm.ForallBlocks fun blk =>
      blk.label = .label Names.mapClosestCopies
        → Obl B b F s ra [w₀, w₁, w₂, w₃, w₄, w₅, w₆] blk := by
  cfg_block [Obl, Names.mapClosestCopies]
  intro t ht
  mc_inv at ht
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
  change (Stk (rsp s) (fr s [w₀, w₁, w₂, w₃] w₄) ra.toBitVec ∗ BView B b ∗ F).get _ at hpm
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
  | goto ".LB.MappingBuilder.mapClosestCopies.4" =>
    rename_i hc
    have h0 := beq_iff_eq.mp hc
    cfg_goto
    · exact (hk0.next rfl rfl rfl rfl rfl rfl rfl rfl).stack
    · mc_inv
      exact ⟨hk0.next rfl rfl rfl rfl rfl rfl rfl rfl,
        from_ge (by show ¬ (0 : Word) < b.n; rw [h0]; decide)⟩
    · simp [V, Names.mapClosestCopies]
  | goto ".LB.MappingBuilder.mapClosestCopies.1" =>
    rename_i hc
    have h0 : b.n ≠ 0#64 := by simpa using hc
    have hpos : 0 < b.n.toNat := Nat.pos_of_ne_zero fun h => h0 (BitVec.eq_of_toNat_eq h)
    cfg_goto
    · exact Kb.stack ⟨hpm, hsp2⟩ (by decide)
    · mc_inv
      exact ⟨b.M, [w₀, w₁, w₂, w₃], w₄, ⟨⟨hpm, hsp2⟩, rfl,
        by simpa [MachineData.pushRa] using hpre.rdi, rfl, rfl, rfl, rfl⟩, hpos, rfl⟩
    · left; have := b.n.isLt; simp [V, Names.mapClosestCopies]; omega

set_option maxHeartbeats 100000 in
theorem b_0 : mapClosestCopiesAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.MappingBuilder.mapClosestCopies.0" → Obl B b F s ra fr₀ blk := by
  cfg_block [Obl]
  intro t ht
  mc_inv at ht
  obtain ⟨M, lo, w, hli, hlt, hrest⟩ := ht
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
  | goto ".LB.MappingBuilder.mapClosestCopies.2" =>
    have hge := InPlaceU.jnb_true _ _ (by assumption)
    rw [BitVec.add_comm] at hge
    cfg_goto
    · exact hli.stk rfl rfl
    · mc_inv
      exact ⟨M, lo, w, hli.next rfl rfl rfl rfl rfl rfl rfl,
        hrest.symm.trans (from_ge fun h => absurd (BitVec.lt_def.1 h) (Nat.not_lt.2 hge))⟩
    · left; mc_var; omega
  | other =>
    have hlt' := InPlaceU.jnb_false _ _ (by assumption)
    first
    | (left
       mc_var
       have e : (1#64 + t.regs.rbx.toBitVec).toNat = t.regs.rbx.toBitVec.toNat + 1 := by bv_omega
       omega)
    | (mc_inv
       refine ⟨M, lo, w, hli.next rfl rfl rfl rfl rfl rfl rfl, hlt', ?_⟩
       rw [BitVec.add_comm]
       exact hrest)

theorem b_1 (hcc : BSpec Names.closestCopy closestA 4 closestQ) (hmap : BSpec Names.map mapA 0 mapQ)
    (hok : b.Ok) : mapClosestCopiesAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.MappingBuilder.mapClosestCopies.1" → Obl B b F s ra fr₀ blk := by
  cfg_block [Obl]
  intro t ht
  mc_inv at ht
  obtain ⟨M, lo, w, hli, hlt, hrest⟩ := ht
  have hokM : BG.Ok { b with M := M } := ⟨hok.m, hok.n, hok.sw, hok.tw, hok.db⟩
  have hb := hli.kb.mem
  rw [sep_lc] at hb
  have hbp := hli.rbp
  have hmax : t.regs.rbx.toBitVec.toNat < MAX_N := Nat.lt_of_lt_of_le hlt hok.n
  obtain ⟨_, hM⟩ := BView.mapM hb
  have h_tgt := BView.rd_tgt hb
  have h_mp := BView.rd_mp hb
  have h_pos := MapM.rd_pos hM hmax
  have h_kind := BView.rdb_kind hb hokM hlt
  unfold rd at h_tgt h_mp h_pos
  unfold rdb at h_kind
  have k_tgt := BView.isSome_tgt hb
  have k_mp := BView.isSome_mp hb
  have k_pos := MapM.isSome_pos hM hmax
  have k_kind := BView.isSome_kind hb hokM hlt
  clear hb hM
  simp only [Names.closestCopy] at hcc
  kvcgen64 [hcc]
  all_goals try symexec_norm
  all_goals try simp only [hbp, h_tgt, h_mp, fold_slot, slot_8192, h_pos, sub_beq_zero,
    neg_one_eq_none] at *
  vc_by_shape
  | load =>
    first
    | with_reducible exact k_mp
    | with_reducible exact k_pos
    | with_reducible exact k_tgt
    | with_reducible exact k_kind
  | goto ".LB.MappingBuilder.mapClosestCopies.0" =>
    have hskip : Flat.closestCopiesFrom b.fl M t.regs.rbx.toBitVec
        = Flat.closestCopiesFrom b.fl M (t.regs.rbx.toBitVec + 1#64) := by
      first
      | (refine skip_pos (BitVec.lt_def.2 hlt) ?_; with_reducible assumption)
      | (refine skip_junk (BitVec.lt_def.2 hlt) ?_
         exact (junk_flag (fb := b.fl) hlt h_kind).symm.trans ‹_›)
    cfg_goto
    · exact hli.stk rfl rfl
    · mc_inv
      exact ⟨M, lo, w, hli.next rfl rfl rfl rfl rfl rfl rfl, hlt, hskip.symm.trans hrest⟩
    · left; mc_var; omega
  | other =>
    rename_i hp hj
    have hw : Flat.isWildcardTarget b.fl t.regs.rbx.toBitVec = false :=
      (junk_flag (fb := b.fl) hlt h_kind).symm.trans hj
    clear hj h_kind
    refine Kb.vcall_above (V := BView) (A := closestA) (Q := closestQ) (S := B) (s := s) (ra := ra)
      (F := F) (xs := []) (lo := lo) (w := w)
      (hi := [s.regs.rbx.toBitVec, s.regs.rbp.toBitVec]) (k := 4) ?kb rfl hli.hl ?rdi hokM ?A ?_
    case kb => exact Kb.next hli.kb rfl rfl
    case rdi => exact hli.rbp
    case A => exact hlt
    intro t2 a' lo' w' hkb hl hQ hok' hag
    obtain ⟨hli2, hbx⟩ := LI.after (xs := []) hag (hli.next rfl rfl rfl rfl rfl rfl rfl) hkb
      (by simpa using hl) hQ.1
    have hrax : t2.regs.rax.toBitVec = Flat.closestCopy b.fl M t.regs.rbx.toBitVec false := hQ.2
    clear hQ hkb
    simp only [Names.map] at hmap
    kvcgen64 [hmap]
    all_goals try symexec_norm
    all_goals try simp only [sub_beq_zero, neg_one_eq_none] at *
    vc_by_shape
    | goto ".LB.MappingBuilder.mapClosestCopies.0" =>
      have hn : Flat.closestCopy b.fl M t.regs.rbx.toBitVec false = Flat.NONE := by
        rw [← hrax]; exact beq_iff_eq.mp ‹_›
      cfg_goto
      · exact hli2.stk rfl rfl
      · mc_inv
        refine ⟨M, _, w', hli2.next rfl rfl rfl rfl rfl rfl rfl, ?_, ?_⟩
        · show t2.regs.rbx.toBitVec.toNat < _; rw [hbx]; exact hlt
        · show Flat.closestCopiesFrom _ _ (t2.regs.rbx.toBitVec + 1#64) = _
          rw [hbx]
          exact (skip_none (BitVec.lt_def.2 hlt) hn).symm.trans hrest
      · left; mc_var; rw [hbx]; omega
    | other =>
      rename_i hc
      have hne : Flat.closestCopy b.fl M t.regs.rbx.toBitVec false ≠ Flat.NONE := by
        rw [← hrax]; exact fun e => by simp [e] at hc
      refine Kb.vcall_above (V := BView) (A := mapA) (Q := mapQ) (S := B) (s := s) (ra := ra)
        (F := F) (a := { b with M := M }) (xs := lo') (lo := []) (w := w')
        (hi := [s.regs.rbx.toBitVec, s.regs.rbp.toBitVec]) (k := 0) ?kb rfl rfl ?rdi hokM ?A ?_
      case kb => rw [List.append_nil]; exact Kb.next hli2.kb rfl rfl
      case rdi => exact hli2.rbp
      case A =>
        exact ⟨by show t2.regs.rax.toBitVec.toNat < _; rw [hrax]; exact BitVec.lt_def.1 (closestCopy_lt hne),
          by show t2.regs.rbx.toBitVec.toNat < _; rw [hbx]; exact hlt⟩
      intro t3 a'' lo'' w'' hkb3 hl3 hQ3 hok3 hag3
      obtain ⟨hli3, hbx3⟩ := LI.after (xs := lo') hag3 (hli2.next rfl rfl rfl rfl rfl rfl rfl) hkb3
        (by simpa [hl3] using hli2.hl) hQ3.2
      have hal : al t3 = code (Flat.mbMap b.fl M t2.regs.rax.toBitVec t2.regs.rbx.toBitVec).1 := hQ3.1
      rw [hrax, hbx] at hal
      clear hQ3 hkb3
      kvcgen64
      all_goals try symexec_norm
      vc_by_shape
      | goto ".LB.MappingBuilder.mapClosestCopies.0" =>
        have hd := code_eq_zero (hal.symm.trans
          (al_zero (by rw [Bool.not_eq_false']; with_reducible assumption)))
        cfg_goto
        · exact hli3.stk rfl rfl
        · mc_inv
          refine ⟨_, _, w'', hli3.next rfl rfl rfl rfl rfl rfl rfl, ?_, ?_⟩
          · show t3.regs.rbx.toBitVec.toNat < _; rw [hbx3, hbx]; exact hlt
          · show Flat.closestCopiesFrom _ _ (t3.regs.rbx.toBitVec + 1#64) = _
            rw [hbx3, hbx, hrax]
            exact (from_done (BitVec.lt_def.2 hlt) hp hw hne hd).symm.trans hrest
        · left; mc_var; rw [hbx3, hbx]; omega
      | goto ".LB.MappingBuilder.mapClosestCopies.3" =>
        have hd := code_ne_zero fun e =>
          al_ne (by rw [Bool.not_eq_true']; with_reducible assumption) (hal.trans e)
        have hf := hrest.symm.trans (from_fail (BitVec.lt_def.2 hlt) hp hw hne hd)
        cfg_goto
        · exact hli3.stk rfl rfl
        · mc_inv
          exact ⟨_, _, w'', hli3.next rfl rfl rfl rfl rfl rfl rfl, by rw [hf]; exact hal,
            by rw [hf, hrax, hbx]; rfl⟩
        · left; mc_var; omega

set_option maxHeartbeats 100000 in
theorem b_2 : mapClosestCopiesAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.MappingBuilder.mapClosestCopies.2" → Obl B b F s ra fr₀ blk := by
  cfg_block [Obl]
  intro t ht
  mc_inv at ht
  obtain ⟨M, lo, w, hli, hd⟩ := ht
  kvcgen64
  all_goals try symexec_norm
  vc_by_shape
  | other =>
    first
    | (right; exact ⟨by mc_var, Nat.lt_succ_self _⟩)
    | (mc_inv
       exact ⟨M, lo, w, hli.next rfl rfl rfl rfl rfl rfl rfl, by rw [hd]; rfl, by rw [hd]⟩)

set_option maxHeartbeats 100000 in
theorem b_3 (hok : b.Ok) : mapClosestCopiesAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.MappingBuilder.mapClosestCopies.3" → Obl B b F s ra fr₀ blk := by
  cfg_block [Obl]
  intro t ht
  mc_inv at ht
  obtain ⟨M, lo, w, hli, hal, hM⟩ := ht
  obtain ⟨p0, p1⟩ := hli.pop_isSome
  have hokM : BG.Ok { b with M := M } := ⟨hok.m, hok.n, hok.sw, hok.tw, hok.db⟩
  have hfl : (fr s lo w).length = 7 := by simp [fr, hli.hl]
  kvcgen64
  all_goals try symexec_norm
  vc_by_shape
  | load =>
    first
    | with_reducible exact p0
    | with_reducible exact p1
  | retAddr =>
    refine Option.isSome_iff_exists.mpr
      ⟨ra, Kg.retAddr (P := BView B { b with M := M } ∗ F) (s := s) (fr := fr s lo w) ?_⟩
    exact hli.pop_kg rfl (by bv_omega) rfl rfl rfl rfl rfl rfl
  | ret =>
    refine Kg.vret (ok := BG.Ok) (a' := { b with M := M })
      (hli.pop_kg rfl (by bv_omega) rfl rfl rfl rfl rfl rfl) hfl hokM
      fun t' _ hax => ⟨?_, by rw [hM]⟩
    simp only [al] at hal ⊢
    rw [hax]
    exact hal

set_option maxHeartbeats 100000 in
theorem b_4 (hok : b.Ok) (hfr : fr₀.length = 7) : mapClosestCopiesAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.MappingBuilder.mapClosestCopies.4" → Obl B b F s ra fr₀ blk := by
  cfg_block [Obl]
  intro t ht
  mc_inv at ht
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

end CopiesU

open CopiesU in
theorem mapClosestCopies_unit [Host] [FunDecls] (hcc : BSpec Names.closestCopy closestA 4 closestQ)
    (hmap : BSpec Names.map mapA 0 mapQ) :
    BThm mapClosestCopiesAsm mapClosestA 7 mapClosestQ := by
  intro B b F s ra
  refine ⟨fun s₀ ⟨h₀, hpre⟩ => ?_⟩
  subst h₀
  obtain ⟨fr₀, hfr, hk0⟩ := hpre.kg ra
  match fr₀, hfr, hk0 with
  | [w₀, w₁, w₂, w₃, w₄, w₅, w₆], hfr, hk0 =>
  refine Program.WP.cfg (CopiesU.Inv B b F s ra [w₀, w₁, w₂, w₃, w₄, w₅, w₆]) (CopiesU.V b) ?_ rfl
  refine forallBlocks_cases labels labels_cover fun l hl => ?_
  simp only [labels, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact b_entry B b F s ra _
  · exact b_fn B b F s ra hpre w₀ w₁ w₂ w₃ w₄ w₅ w₆ hk0
  · exact b_0 B b F s ra _
  · exact b_1 B b F s ra _ hcc hmap hpre.ok
  · exact b_2 B b F s ra _
  · exact b_3 B b F s ra _ hpre.ok
  · exact b_4 B b F s ra _ hpre.ok hfr

end Bbu.Unit
