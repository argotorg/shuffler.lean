module

public import FlatShuffler.Unit.Plan.HasOther
import all FlatShuffler.Unit.Plan.HasOther

@[expose] public section

/-!
# `Planner::isDemanded`

`Names.isDemanded` in `build/kraken/c/build_bottom_up.S`: no frame, no call, no store. If `n = 0` it returns `false` at
once. Else it runs the loop over the targets `rax < n`: `rcx` is `m_target` and `r8` is `n`. It
skips a target slot of kind `Junk` (`cmpb $1, 4(%rcx,%rax,8)`) and compares the low 6 bytes of
the other target slots and of the slot `rsi` (`xorq; salq $16`). Each turn of the loop is one
unfold of `Flat.demandedFrom`.
-/

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

set_option experimental.vcgen true

namespace FlatShuffler.Unit

open FlatShuffler.Sep

/-! ## The target of a `Planner` -/

section
variable {P : Addr} {p : PlannerObjectMemory} {F : MProp 64} {m : Mem 64} {i : Word}

theorem plannerObjectOwnedMemory.rd_tgt (h : (plannerObjectOwnedMemory P p ∗ F).get m) : rd m (P + 16#64) = p.tgt :=
  rd_of_eq h (by unfold plannerObjectOwnedMemory; ecancel)
theorem plannerObjectOwnedMemory.isSome_tgt (h : (plannerObjectOwnedMemory P p ∗ F).get m) :
    (m.loadInt (P + 16#64) 8).isSome = true :=
  isSome_of_eq p.tgt h (by unfold plannerObjectOwnedMemory; ecancel)
theorem plannerObjectOwnedMemory.rd_targetSize (h : (plannerObjectOwnedMemory P p ∗ F).get m) : rd m (P + 24#64) = p.targetSize :=
  rd_of_eq h (by unfold plannerObjectOwnedMemory; ecancel)
theorem plannerObjectOwnedMemory.isSome_targetSize (h : (plannerObjectOwnedMemory P p ∗ F).get m) : (m.loadInt (P + 24#64) 8).isSome = true :=
  isSome_of_eq p.targetSize h (by unfold plannerObjectOwnedMemory; ecancel)

theorem plannerObjectOwnedMemory.arr_tgt (h : (plannerObjectOwnedMemory P p ∗ F).get m) : ∃ R, (Arr p.tgt p.tw ∗ R).get m :=
  ⟨_, (by unfold plannerObjectOwnedMemory; ecancel : plannerObjectOwnedMemory P p ∗ F = Arr p.tgt p.tw ∗ _) ▸ h⟩

theorem plannerObjectOwnedMemory.isSome_tw (h : (plannerObjectOwnedMemory P p ∗ F).get m) (hok : p.Ok) (hi : i.toNat < p.targetSize.toNat) :
    (m.loadInt (slotAt p.tgt i.toNat) 8).isSome = true :=
  let ⟨_, h⟩ := plannerObjectOwnedMemory.arr_tgt h; Arr.isSome h (hok.tw ▸ hi)

-- Slot `i < n` of the target.
theorem plannerObjectOwnedMemory.rd_tw (h : (plannerObjectOwnedMemory P p ∗ F).get m) (hok : p.Ok) (hi : i.toNat < p.targetSize.toNat) :
    StackSlot.ofWord (rd m (slotAt p.tgt i.toNat)) = Flat.get p.fl.target i := by
  obtain ⟨_, h⟩ := plannerObjectOwnedMemory.arr_tgt h
  have hi' : i.toNat < p.tw.length := hok.tw ▸ hi
  show _ = Flat.get (vec (p.tw.map StackSlot.ofWord)) i
  rw [get_vecL (by simpa using hi') (by simpa [hok.tw] using hok.targetSizeFitsBuffer), List.getElem_map]
  exact congrArg StackSlot.ofWord (Arr.rd h hi')

-- Byte 4 of the target word `i < n`.
theorem plannerObjectOwnedMemory.b8_kind (h : (plannerObjectOwnedMemory P p ∗ F).get m) (hok : p.Ok) (hi : i.toNat < p.targetSize.toNat) :
    ∃ R, (B8 (slotAt p.tgt i.toNat + 4#64) (Flat.get p.fl.target i).kind ∗ R).get m := by
  obtain ⟨R, h⟩ := plannerObjectOwnedMemory.arr_tgt h
  have hi' : i.toNat < p.tw.length := hok.tw ▸ hi
  obtain ⟨Q, e⟩ := Arr.focus p.tgt p.tw hi'
  obtain ⟨P, e'⟩ := Wd.focus_byte (slotAt p.tgt i.toNat) p.tw[i.toNat] (j := 4) (by decide)
  have hk : (Flat.get p.fl.target i).kind = p.tw[i.toNat].extractLsb' (8 * 4) 8 := by
    show (Flat.get (vec (p.tw.map StackSlot.ofWord)) i).kind = _
    rw [get_vecL (by simpa using hi') (by simpa [hok.tw] using hok.targetSizeFitsBuffer), List.getElem_map]
    rfl
  rw [e] at h
  change ((Wd (slotAt p.tgt i.toNat) p.tw[i.toNat] ∗ Q) ∗ R).get m at h
  rw [e', MProp.sep_assoc, MProp.sep_assoc] at h
  exact ⟨_, hk ▸ h⟩

theorem plannerObjectOwnedMemory.rdb_kind (h : (plannerObjectOwnedMemory P p ∗ F).get m) (hok : p.Ok) (hi : i.toNat < p.targetSize.toNat) :
    rdb m (slotAt p.tgt i.toNat + 4#64) = (Flat.get p.fl.target i).kind :=
  let ⟨_, h⟩ := plannerObjectOwnedMemory.b8_kind h hok hi; B8.rdb h

theorem plannerObjectOwnedMemory.isSome_kind (h : (plannerObjectOwnedMemory P p ∗ F).get m) (hok : p.Ok) (hi : i.toNat < p.targetSize.toNat) :
    (m.loadInt (slotAt p.tgt i.toNat + 4#64) 1).isSome = true :=
  let ⟨_, h⟩ := plannerObjectOwnedMemory.b8_kind h hok hi; B8.isSome h
end

/-! ## The contract -/

def isDemandedA (_ : PlannerObjectMemory) (_ : MachineData) : Prop := True

def isDemandedQ (p p' : PlannerObjectMemory) (s t : MachineData) : Prop :=
  p' = p ∧ al t = if Flat.isDemanded p.fl (StackSlot.ofWord (rsi s)) then 1#8 else 0#8

namespace DemandU

/-! ### One turn of the loop -/

section
variable {pl : Flat.Planner} {x : StackSlot} {j : Word}

theorem from_ge (h : ¬ j < pl.targetSize) : Flat.demandedFrom pl x j = false := by
  rw [Flat.demandedFrom, dite_eq_right h]

theorem skip_junk (h : j < pl.targetSize) (hj : isJunk (Flat.get pl.target j) = true) :
    Flat.demandedFrom pl x j = Flat.demandedFrom pl x (j + 1) := by
  rw [Flat.demandedFrom, dite_eq_left h]
  simp [hj]

theorem skip_ne (h : j < pl.targetSize) (hs : Flat.get pl.target j ≠ x) :
    Flat.demandedFrom pl x j = Flat.demandedFrom pl x (j + 1) := by
  rw [Flat.demandedFrom, dite_eq_left h]
  simp [hs]

theorem found (h : j < pl.targetSize) (hj : isJunk (Flat.get pl.target j) = false)
    (hs : Flat.get pl.target j = x) : Flat.demandedFrom pl x j = true := by
  rw [Flat.demandedFrom, dite_eq_left h]
  subst hs; simp [hj]
end

-- `cmpb $1, 4(%rcx,%rax,8)`: `zf` is `isJunk`.
theorem junk_flag {x : BitVec 8} {sl : StackSlot} (hk : x = sl.kind) :
    (x - 1#8 == BitVec.zero 8) = isJunk sl := by
  have e : (x - 1#8 == BitVec.zero 8) = (x == Junk) := by
    rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
    unfold Junk
    constructor <;> intro h <;> bv_decide
  rw [e, hk]
  rfl

/-! ### The registers -/

structure LI (P : Addr) (p : PlannerObjectMemory) (F : MProp 64) (s : MachineData) (ra : Int64)
    (t : MachineData) : Prop where
  kg : Kg (plannerObjectOwnedMemory P p ∗ F) s ra [] t
  rsi : t.regs.rsi.toBitVec = s.regs.rsi.toBitVec
  rcx : t.regs.rcx.toBitVec = p.tgt
  r8 : t.regs.r8.toBitVec = p.targetSize

section
variable {P : Addr} {p : PlannerObjectMemory} {F : MProp 64} {s t t' : MachineData} {ra : Int64}

theorem LI.next (hl : LI P p F s ra t) (hm : t'.dmem = t.dmem) (hsp : t'.regs.rsp = t.regs.rsp)
    (hbx : t'.regs.rbx = t.regs.rbx) (hbp : t'.regs.rbp = t.regs.rbp)
    (h12 : t'.regs.r12 = t.regs.r12) (h13 : t'.regs.r13 = t.regs.r13)
    (h14 : t'.regs.r14 = t.regs.r14) (h15 : t'.regs.r15 = t.regs.r15)
    (hsi : t'.regs.rsi = t.regs.rsi) (hcx : t'.regs.rcx = t.regs.rcx)
    (h8 : t'.regs.r8 = t.regs.r8) : LI P p F s ra t' :=
  ⟨hl.kg.next hm hsp hbx hbp h12 h13 h14 h15, by rw [hsi]; exact hl.rsi,
    by rw [hcx]; exact hl.rcx, by rw [h8]; exact hl.r8⟩

theorem LI.stk (hl : LI P p F s ra t) (_hm : t'.dmem = t.dmem) (hsp : t'.regs.rsp = t.regs.rsp) :
    t'.StackAtOrBelow (s.pushRa ra) :=
  MachineData.stackAtOrBelow_of_toNat_lt (by simp [hsp, hl.kg.sp])
end

/-! ### The invariant, the variant and the obligation of a block -/

-- The result of the unit.
abbrev res (p : PlannerObjectMemory) (s : MachineData) : Bool := Flat.isDemanded p.fl (StackSlot.ofWord (rsi s))

-- `ret` with the result bit `b` in `rax`.
theorem al_res {p : PlannerObjectMemory} {s t t' : MachineData} {b : Bool} (hb : res p s = b)
    (hax : rax t' = rax t) (hal : (rax t).setWidth 8 = if b then 1#8 else 0#8) :
    al t' = if Flat.isDemanded p.fl (StackSlot.ofWord (rsi s)) then 1#8 else 0#8 := by
  show (rax t').setWidth 8 = _
  rw [hax, hal, ← hb]

def Inv (P : Addr) (p : PlannerObjectMemory) (F : MProp 64) (s : MachineData) (ra : Int64) :
    CfgLabel → MachineData → Prop
  | .entry, t => t = s.pushRa ra
  | .exit, _ => False
  | .label l, t =>
    if l = Names.isDemanded then t = s.pushRa ra
    else if l = ".LB.Planner.isDemanded.0" then
      LI P p F s ra t ∧ t.regs.rax.toBitVec.toNat < p.targetSize.toNat
      ∧ Flat.demandedFrom p.fl (StackSlot.ofWord (rsi s)) (t.regs.rax.toBitVec + 1#64) = res p s
    else if l = ".LB.Planner.isDemanded.1" then
      LI P p F s ra t ∧ t.regs.rax.toBitVec.toNat < p.targetSize.toNat
      ∧ Flat.demandedFrom p.fl (StackSlot.ofWord (rsi s)) t.regs.rax.toBitVec = res p s
    else if l = ".LB.Planner.isDemanded.2" then
      Kg (plannerObjectOwnedMemory P p ∗ F) s ra [] t ∧ res p s = false
    else if l = ".LB.Planner.isDemanded.3" then
      Kg (plannerObjectOwnedMemory P p ∗ F) s ra [] t ∧ res p s = false
    else False

-- The variant. A turn of the loop decreases `n - rax`.
def V (p : PlannerObjectMemory) (l : Label) (t : MachineData) : Nat :=
  if l = Names.isDemanded then 2 ^ 70
  else if l = ".LB.Planner.isDemanded.0" then
    2 * (p.targetSize.toNat - t.regs.rax.toBitVec.toNat) - 1
  else if l = ".LB.Planner.isDemanded.1" then
    2 * (p.targetSize.toNat - t.regs.rax.toBitVec.toNat)
  else 0

def E (P : Addr) (p : PlannerObjectMemory) (F : MProp 64) (s : MachineData) (ra : Int64) :
    Int64 → MachineData → Prop :=
  fun a t => a = ra ∧ VPost plannerObjectOwnedMemory PlannerObjectMemory.Ok P F 0 (fun p' t => isDemandedQ p p' s t) s t
    ∧ Sep.mod.Agree s t

def Obl [Host] [FunDecls] (P : Addr) (p : PlannerObjectMemory) (F : MProp 64) (s : MachineData) (ra : Int64)
    (blk : Program.Block) : Prop :=
  ∀ t, Inv P p F s ra blk.label t →
    let I' (c : CfgLabel) (j : Nat) (_ : Unit) (u : MachineData) :=
      Inv P p F s ra c u ∧ Program.Decreases (V p) blk.label blk.idx t c j u
    WP.wp blk.body (I' blk.next (blk.idx + 1))
      (Program.Intercept (Program.labels isDemandedAsm) (s.pushRa ra) I' (E P p F s ra)) t

def labels : List CfgLabel :=
  [.entry, .label Names.isDemanded,
    .label ".LB.Planner.isDemanded.0",
    .label ".LB.Planner.isDemanded.1",
    .label ".LB.Planner.isDemanded.2",
    .label ".LB.Planner.isDemanded.3"]

theorem labels_cover : isDemandedAsm.ForallBlocks fun blk => blk.label ∈ labels := by
  simp only [labels, Names.isDemanded]
  cfg_labels

macro "dm_inv" : tactic => `(tactic|
  simp only [Inv, Names.isDemanded, String.reduceEq, ↓reduceIte])
macro "dm_inv" "at" h:ident : tactic => `(tactic|
  simp only [Inv, Names.isDemanded, String.reduceEq, ↓reduceIte] at $h:ident)
macro "dm_var" : tactic => `(tactic|
  simp only [V, Names.isDemanded, String.reduceEq, ↓reduceIte])

/-! ### The blocks -/

open ShallowestCopy

section
variable [Host] [FunDecls] (P : Addr) (p : PlannerObjectMemory) (F : MProp 64) (s : MachineData) (ra : Int64)

set_option maxHeartbeats 100000 in
theorem b_entry : isDemandedAsm.ForallBlocks fun blk =>
    blk.label = .entry → Obl P p F s ra blk := by
  cfg_block [Obl]
  intro t ht
  kvcgen64
  dm_inv
  exact ht

set_option maxHeartbeats 100000 in
theorem b_fn (hpre : VPre plannerObjectOwnedMemory PlannerObjectMemory.Ok P p F isDemandedA 0 s)
    (hk0 : Kg (plannerObjectOwnedMemory P p ∗ F) s ra [] (s.pushRa ra)) :
    isDemandedAsm.ForallBlocks fun blk =>
      blk.label = .label Names.isDemanded → Obl P p F s ra blk := by
  cfg_block [Obl, Names.isDemanded]
  intro t ht
  dm_inv at ht
  subst ht
  have hrdi : (s.pushRa ra).regs.rdi.toBitVec = P := by
    simpa [MachineData.pushRa] using hpre.rdi
  have hm := hk0.vmem
  have h_n := plannerObjectOwnedMemory.rd_targetSize hm
  have k_n := plannerObjectOwnedMemory.isSome_targetSize hm
  have h_t := plannerObjectOwnedMemory.rd_tgt hm
  have k_t := plannerObjectOwnedMemory.isSome_tgt hm
  unfold rd at h_n h_t
  clear hm
  kvcgen64
  all_goals try symexec_norm
  all_goals try simp only [hrdi, h_n, h_t, BitVec.and_self] at k_n k_t ⊢
  vc_by_shape
  | load =>
    first
    | with_reducible exact k_n
    | with_reducible exact k_t
  | goto ".LB.Planner.isDemanded.3" =>
    rename_i hc
    simp only [hrdi, h_n, BitVec.and_self] at hc
    have h0 := beq_iff_eq.mp hc
    cfg_goto
    · exact (hk0.next rfl rfl rfl rfl rfl rfl rfl rfl).stack
    · dm_inv
      exact ⟨hk0.next rfl rfl rfl rfl rfl rfl rfl rfl,
        from_ge (by show ¬ (0 : Word) < p.targetSize; rw [h0]; decide)⟩
    · simp [V, Names.isDemanded]
  | goto ".LB.Planner.isDemanded.1" =>
    rename_i hc
    simp only [hrdi, h_n, BitVec.and_self] at hc
    have h0 : p.targetSize ≠ 0#64 := by simpa using hc
    have hpos : 0 < p.targetSize.toNat := Nat.pos_of_ne_zero fun e => h0 (BitVec.eq_of_toNat_eq e)
    cfg_goto
    · exact (hk0.next rfl rfl rfl rfl rfl rfl rfl rfl).stack
    · dm_inv
      exact ⟨⟨hk0.next rfl rfl rfl rfl rfl rfl rfl rfl, rfl, rfl, rfl⟩, hpos, rfl⟩
    · left; have := p.targetSize.isLt; simp [V, Names.isDemanded]; omega


set_option maxHeartbeats 100000 in
theorem b_0 : isDemandedAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.Planner.isDemanded.0" → Obl P p F s ra blk := by
  cfg_block [Obl]
  intro t ht
  dm_inv at ht
  obtain ⟨hli, hlt, hrest⟩ := ht
  have h8 := hli.r8
  kvcgen64
  all_goals try symexec_norm
  all_goals try simp only [sub_beq_zero] at *
  vc_by_shape
  | goto ".LB.Planner.isDemanded.2" =>
    rename_i hc
    have he : t.regs.rax.toBitVec + 1#64 = p.targetSize := by
      rw [BitVec.add_comm, ← h8]; exact beq_iff_eq.mp hc
    cfg_goto
    · exact hli.stk rfl rfl
    · dm_inv
      exact ⟨hli.kg.next rfl rfl rfl rfl rfl rfl rfl rfl,
        hrest.symm.trans (from_ge (by rw [he]; exact BitVec.lt_irrefl _))⟩
    · left; dm_var; omega
  | other =>
    rename_i hc
    have hne : 1#64 + t.regs.rax.toBitVec ≠ p.targetSize := by
      rw [← h8]; simpa using hc
    have e : (1#64 + t.regs.rax.toBitVec).toNat = t.regs.rax.toBitVec.toNat + 1 := by bv_omega
    have hlt' : (1#64 + t.regs.rax.toBitVec).toNat < p.targetSize.toNat := by
      have : (1#64 + t.regs.rax.toBitVec).toNat ≠ p.targetSize.toNat :=
        fun x => hne (BitVec.eq_of_toNat_eq x)
      omega
    first
    | (left; dm_var; omega)
    | (dm_inv
       refine ⟨hli.next rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl, hlt', ?_⟩
       rw [BitVec.add_comm]; exact hrest)

set_option maxHeartbeats 100000 in
theorem b_1 (hok : PlannerObjectMemory.Ok p) : isDemandedAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.Planner.isDemanded.1" → Obl P p F s ra blk := by
  cfg_block [Obl]
  intro t ht
  dm_inv at ht
  obtain ⟨hli, hlt, hrest⟩ := ht
  have hlt' : t.regs.rax.toBitVec < p.fl.targetSize := BitVec.lt_def.2 hlt
  have hcx := hli.rcx
  have hsi := hli.rsi
  have hm := hli.kg.vmem
  have h_kind := plannerObjectOwnedMemory.rdb_kind hm hok hlt
  have k_kind := plannerObjectOwnedMemory.isSome_kind hm hok hlt
  have h_tw := plannerObjectOwnedMemory.rd_tw hm hok hlt
  have k_tw := plannerObjectOwnedMemory.isSome_tw hm hok hlt
  unfold rdb at h_kind
  unfold rd at h_tw
  clear hm
  kvcgen64
  all_goals try symexec_norm
  all_goals try simp only [hcx, hsi, fold_slot] at *
  vc_by_shape
  | load =>
    first
    | with_reducible exact k_kind
    | with_reducible exact k_tw
  | closed => decide
  | goto ".LB.Planner.isDemanded.0" =>
    have hskip : Flat.demandedFrom p.fl (StackSlot.ofWord s.regs.rsi.toBitVec) t.regs.rax.toBitVec
        = Flat.demandedFrom p.fl (StackSlot.ofWord s.regs.rsi.toBitVec)
          (t.regs.rax.toBitVec + 1#64) := by
      first
      | (refine skip_junk hlt' ((junk_flag h_kind).symm.trans ?_); with_reducible assumption)
      | exact skip_ne hlt' fun e => (jne_true (by with_reducible assumption)) (h_tw.trans e).symm
    cfg_goto
    · exact hli.stk rfl rfl
    · dm_inv
      exact ⟨hli.next rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl, hlt, hskip.symm.trans hrest⟩
    · left; dm_var; omega
  | retAddr =>
    exact Option.isSome_iff_exists.mpr ⟨ra, (hli.kg.next rfl rfl rfl rfl rfl rfl rfl rfl).retAddr⟩
  | ret =>
    have hj : isJunk (Flat.get p.fl.target t.regs.rax.toBitVec) = false :=
      (junk_flag h_kind).symm.trans (by with_reducible assumption)
    have heq := jne_false (by with_reducible assumption)
    have hres : res p s = true := hrest.symm.trans (found hlt' hj (h_tw.symm.trans heq.symm))
    refine Kg.vret (ok := PlannerObjectMemory.Ok) (a' := p) (hli.kg.next rfl rfl rfl rfl rfl rfl rfl rfl) rfl hok
      fun t' _ hax => ⟨rfl, al_res hres hax rfl⟩
  all_goals decide

set_option maxHeartbeats 100000 in
theorem b_2 (hok : PlannerObjectMemory.Ok p) : isDemandedAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.Planner.isDemanded.2" → Obl P p F s ra blk := by
  cfg_block [Obl]
  intro t ht
  dm_inv at ht
  obtain ⟨hk, hd⟩ := ht
  kvcgen64
  all_goals try symexec_norm
  vc_by_shape
  | retAddr => exact Option.isSome_iff_exists.mpr ⟨ra, (hk.next rfl rfl rfl rfl rfl rfl rfl rfl).retAddr⟩
  | ret =>
    refine Kg.vret (ok := PlannerObjectMemory.Ok) (a' := p) (hk.next rfl rfl rfl rfl rfl rfl rfl rfl) rfl hok
      fun t' _ hax => ⟨rfl, al_res hd hax rfl⟩

set_option maxHeartbeats 100000 in
theorem b_3 (hok : PlannerObjectMemory.Ok p) : isDemandedAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.Planner.isDemanded.3" → Obl P p F s ra blk := by
  cfg_block [Obl]
  intro t ht
  dm_inv at ht
  obtain ⟨hk, hd⟩ := ht
  kvcgen64
  all_goals try symexec_norm
  vc_by_shape
  | retAddr => exact Option.isSome_iff_exists.mpr ⟨ra, (hk.next rfl rfl rfl rfl rfl rfl rfl rfl).retAddr⟩
  | ret =>
    refine Kg.vret (ok := PlannerObjectMemory.Ok) (a' := p) (hk.next rfl rfl rfl rfl rfl rfl rfl rfl) rfl hok
      fun t' _ hax => ⟨rfl, al_res hd hax rfl⟩

end

end DemandU

end FlatShuffler.Unit

namespace FlatShuffler.Unit
open DemandU in
theorem isDemanded_unit [Host] [FunDecls] :
    VThm plannerObjectOwnedMemory PlannerObjectMemory.Ok isDemandedAsm isDemandedA 0 isDemandedQ := by
  intro P p F s ra
  refine ⟨fun s₀ ⟨h₀, hpre⟩ => ?_⟩
  subst h₀
  obtain ⟨fr, hfr, hk0⟩ := hpre.kg ra
  obtain rfl : fr = [] := List.eq_nil_of_length_eq_zero hfr
  refine Program.WP.cfg (DemandU.Inv P p F s ra) (DemandU.V p) ?_ rfl
  refine forallBlocks_cases labels labels_cover fun l hl => ?_
  simp only [labels, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl
  · exact b_entry P p F s ra
  · exact b_fn P p F s ra hpre hk0
  · exact b_0 P p F s ra
  · exact b_1 P p F s ra hpre.ok
  · exact b_2 P p F s ra hpre.ok
  · exact b_3 P p F s ra hpre.ok
end FlatShuffler.Unit
