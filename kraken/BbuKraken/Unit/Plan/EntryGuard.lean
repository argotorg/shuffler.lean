module

public import BbuKraken.Unit.Plan.EntryFrame
import all BbuKraken.Unit.Plan.EntryFrame
public import BbuKraken.Unit.Plan.EntryIdsModel
import all BbuKraken.Unit.Plan.EntryIdsModel
public import BbuKraken.Unit.Run.Load
import all BbuKraken.Unit.Run.Load

@[expose] public section

open Std.WP Lean.Order ProofKit
open scoped Program.WP
set_option experimental.vcgen true

namespace Bbu.Unit.EntryValidU
open Bbu.Sep

private theorem frame88 (x : Word) : x - 8#64 - 8#64 - 80#64 = x - 8#64 - 88#64 := by
  bv_omega

private theorem arg96 (x : Word) : x - 8#64 - 8#64 - 80#64 + 96#64 = x := by bv_omega
private theorem arg104 (x : Word) : x - 8#64 - 8#64 - 80#64 + 104#64 = x + 8#64 := by bv_omega

private theorem low8_widen (w : BitVec 32) :
    (w.setWidth 64).extractLsb' 0 8 = w.setWidth 8 := by bv_decide

private theorem split_frame (xs : List Word) (hl : xs.length = entryD) :
    xs.take (xs.length - 1) = xs.take 8241 ++ (xs.drop 8241).take 10 := by
  have ht : (xs.take 8241).length = 8241 := by simp [hl, entryD]
  calc
    _ = (xs.take 8241 ++ xs.drop 8241).take 8251 := by
      rw [List.take_append_drop, hl]
      rfl
    _ = _ := by
      rw [List.take_append, ht]
      simp only [List.take_take, Nat.reduceSub]
      rw [show min 8251 8241 = 8241 by decide]

set_option maxRecDepth 4096 in
theorem b_fn [Host] [FunDecls] (g : EG) (F : MProp 64) (s : MachineData) (ra : Int64)
    (hp : Pre g F s) (hs : Sizes g)
    (K : Unit → MachineData → Prop) (I' : CfgLabel → Nat → Unit → MachineData → Prop)
    (E : Int64 → MachineData → Prop)
    (hsource : ∀ t, SourceHead g F s ra t →
      Program.Intercept planAsm.labels (s.pushRa ra) I' E (label ".LB.plan.1") t)
    (hempty : ∀ t, SourceDone g F s ra t → g.r.p.m = 0#64 →
      Program.Intercept planAsm.labels (s.pushRa ra) I' E (label ".LB.plan.14") t) :
    planAsm.ForallBlocks fun blk => blk.label = .label Names.plan →
      WP.wp blk.body K
        (Program.Intercept planAsm.labels (s.pushRa ra) I' E) (s.pushRa ra) := by
  cfg_block [Names.plan]
  obtain ⟨hok, hdi, hsi, hdx, hcx, h8, h9, ha, hcountPtr, hcount, htrace,
    xs, w, hl, hm⟩ := hp
  have hk := Kg.init (ra := ra) hm
  have hpush := hk.pushes (xs := [s.regs.rbx.toBitVec]) (by simp [hl, entryD])
  have kmapped := hpush.1.1
  have hmem := hpush.2
  let lo := xs.take 8241
  let locals := (xs.drop 8241).take 10
  have hlo : lo.length = 8241 := by simp [lo, hl, entryD]
  have hloc : locals.length = 10 := by simp [locals, hl, entryD]
  have he : xs.take (xs.length - [s.regs.rbx.toBitVec].length) ++
      [s.regs.rbx.toBitVec].reverse = fr s lo locals := by
    simp only [List.length_singleton, List.reverse_singleton, split_frame xs hl]
    simp only [fr, List.append_assoc, lo, locals]
  rw [he] at hmem
  let q := (s.pushRa ra).regs.rsp.toBitVec - 8#64 - 80#64
  let m0 := pushes (s.pushRa ra).dmem (s.pushRa ra).regs.rsp.toBitVec
    [s.regs.rbx.toBitVec]
  let u0 : MachineData := {s.pushRa ra with
    regs := {(s.pushRa ra).regs with rsp := ⟨q⟩}, dmem := m0}
  have hb0 : Bd g F s ra lo locals u0 :=
    ⟨⟨hmem, frame88 (rsp s)⟩, hlo, hloc, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨R, eA⟩ : ∃ R, Stk (rsp s) (fr s lo locals) ra.toBitVec ∗
      (View (rsp s) g ∗ F) = B32 (rsp s) g.allowed ∗ R :=
    ⟨_, by unfold View Args; ecancel⟩
  have ra' := EntryU.b32_read (eA ▸ hmem)
  have ka := B32.isSome (eA ▸ hmem)
  obtain ⟨R, eB⟩ : ∃ R, Stk (rsp s) (fr s lo locals) ra.toBitVec ∗
      (View (rsp s) g ∗ F) = B32 (rsp s + 8#64) g.strategy ∗ R :=
    ⟨_, by unfold View Args; ecancel⟩
  have rb' := EntryU.b32_read (eB ▸ hmem)
  have kb := B32.isSome (eB ▸ hmem)
  have h96 : (s.pushRa ra).regs.rsp.toBitVec - 8#64 - 80#64 + 96#64 = rsp s :=
    arg96 (rsp s)
  have h104 : (s.pushRa ra).regs.rsp.toBitVec - 8#64 - 80#64 + 104#64 = rsp s + 8#64 :=
    arg104 (rsp s)
  have hbx : (s.pushRa ra).regs.rbx = s.regs.rbx := rfl
  have hregs : (s.pushRa ra).regs = {s.regs with rsp := ⟨rsp s - 8#64⟩} := rfl
  simp only [pushes] at ka kb ra' rb'
  simp only [rdi, rsi, rdx, rcx, r8, r9, Reg64s.get64_rdi, Reg64s.get64_rsi,
    Reg64s.get64_rdx, Reg64s.get64_rcx, Reg64s.get64_r8, Reg64s.get64_r9] at hdi hsi hdx hcx h8 h9
  kvcgen64
  all_goals try symexec_norm at ⊢
  all_goals try simp only [h96, h104, hbx, ra', rb'] at ⊢
  vc_by_shape
  | load => run_loads [kmapped, ka, kb]
  | goto ".LB.plan.12" =>
    rename_i hc
    rw [MachineData.status_mk, Idioms.cmp_a_imm _ 1024 (by decide)] at hc
    simp only [hregs, hdi, hsi, decide_eq_true_eq] at hc
    have hmB := sizes_m hs
    have hnB := sizes_n hs
    change g.r.p.m.toNat ≤ 1024 at hmB
    change g.r.p.n.toNat ≤ 1024 at hnB
    exact False.elim (by omega)
  | goto ".LB.plan.13" =>
    rename_i hm hn af he
    rw [MachineData.status_mk, Idioms.cmp_a_imm _ 1 (by decide)] at he
    symexec_norm at he
    simp only [h96, h104, hbx, ra', rb', low8_widen, decide_eq_true_eq] at he
    have hor := (EntryU.bad_or g.strategy g.allowed).mp he
    exact False.elim (hs (hor.elim (fun h => Or.inr (Or.inr (Or.inr h)))
      (fun h => Or.inr (Or.inr (Or.inl h)))))
  | goto ".LB.plan.14" =>
    rename_i hm hn af he af' hz
    symexec_norm at hz
    simp only [hregs, hdi, BitVec.and_self, BitVec.zero_eq, beq_iff_eq] at hz
    apply hempty
    · refine ⟨lo, locals, ?_, ?_⟩
      · exact ⟨(by apply hb0.next <;> rfl), hdi, hsi, hdx, hcx, h8, h9, rfl, rfl⟩
      · exact idsFrom_end _ _ (by rw [hok.sw, hz]; decide)
    · exact hz
  | goto ".LB.plan.1" =>
    rename_i hm hn af he af' hz
    symexec_norm at hz
    simp only [hregs, hdi, BitVec.and_self, BitVec.zero_eq, beq_eq_false_iff_ne] at hz
    apply hsource
    refine ⟨lo, locals, ?_, ?_, rfl⟩
    · exact ⟨(by apply hb0.next <;> rfl), hdi, hsi, hdx, hcx, h8, h9, rfl, rfl⟩
    · change 0#64 < g.r.p.m
      bv_omega

end Bbu.Unit.EntryValidU
