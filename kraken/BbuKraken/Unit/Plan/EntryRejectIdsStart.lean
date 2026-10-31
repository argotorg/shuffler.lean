import BbuKraken.Unit.Plan.EntryRejectIdsDefs
import BbuKraken.Unit.Run.Load
import ProofKit.Idioms

open Std.WP Lean.Order ProofKit
open scoped Program.WP
set_option experimental.vcgen true

namespace Bbu.Unit.EntryRejectIds
open Bbu.Sep EntryValidU

private theorem frame88 (x : Word) : x - 8#64 - 8#64 - 80#64 = x - 8#64 - 88#64 := by bv_omega
private theorem arg96 (x : Word) : x - 8#64 - 8#64 - 80#64 + 96#64 = x := by bv_omega
private theorem arg104 (x : Word) : x - 8#64 - 8#64 - 80#64 + 104#64 = x + 8#64 := by bv_omega
private theorem positive (x : Word) (h : x ≠ 0#64) : 0#64 < x := by bv_omega
private theorem low8_widen_extract (w : BitVec 32) :
    (w.setWidth 64).extractLsb' 0 8 = w.setWidth 8 := by bv_decide

section
variable [Host] [FunDecls] (g : G) (F : MProp 64) (s : MachineData) (ra : Int64)

theorem b_entry : planAsm.ForallBlocks fun blk => blk.label = .entry → Obl g F s ra blk := by
  cfg_block [Obl]
  intro t ht
  kvcgen64
  simpa only [Inv, Names.plan, ↓reduceIte] using ht

theorem b_fn (hp : Pre g F s) : planAsm.ForallBlocks fun blk =>
    blk.label = .label Names.plan → Obl g F s ra blk := by
  cfg_block [Obl, Names.plan]
  intro t ht
  simp only [Inv, Names.plan, ↓reduceIte] at ht
  subst t
  obtain ⟨hok, hdi, hsi, hdx, hcx, h9, fr, v, hl, hm⟩ := hp
  have hk := Kg.init (ra := ra) hm
  have hx := hk.pushes (xs := [s.regs.rbx.toBitVec]) (by simp [hl])
  have hh := hx.2
  simp only [List.length_singleton, List.reverse_singleton] at hh
  obtain ⟨R, he⟩ : ∃ R, Stk (rsp s) (fr.take (fr.length - 1) ++ [s.regs.rbx.toBitVec])
      ra.toBitVec ∗ Args g F s = B32 (rsp s) g.allowed ∗ R :=
    ⟨_, by unfold Args EntryU.Args; ecancel⟩
  have ha := EntryU.b32_read (he ▸ hh)
  have ka := B32.isSome (he ▸ hh)
  obtain ⟨R', he'⟩ : ∃ R', Stk (rsp s) (fr.take (fr.length - 1) ++ [s.regs.rbx.toBitVec])
      ra.toBitVec ∗ Args g F s = B32 (rsp s + 8#64) g.strategy ∗ R' :=
    ⟨_, by unfold Args EntryU.Args; ecancel⟩
  have hb := EntryU.b32_read (he' ▸ hh)
  have kb := B32.isSome (he' ▸ hh)
  have kp := hx.1.1
  simp only [pushes] at hh ha ka hb kb
  have h96 : (s.pushRa ra).regs.rsp.toBitVec - 8#64 - 80#64 + 96#64 = rsp s := by
    exact arg96 (rsp s)
  have h104 : (s.pushRa ra).regs.rsp.toBitVec - 8#64 - 80#64 + 104#64 = rsp s + 8#64 := by
    exact arg104 (rsp s)
  have hbx : (s.pushRa ra).regs.rbx = s.regs.rbx := rfl
  have hregs : (s.pushRa ra).regs = {s.regs with rsp := ⟨rsp s - 8#64⟩} := rfl
  have hlo : (fr.take (fr.length - 1)).length = 10 := by simp [hl]
  have hmB := hok.m
  have hnB := hok.n
  simp only [rdi, rsi, rdx, rcx, r9, Reg64s.get64_rdi, Reg64s.get64_rsi,
    Reg64s.get64_rdx, Reg64s.get64_rcx, Reg64s.get64_r9] at hdi hsi hdx hcx h9
  kvcgen64
  all_goals try symexec_norm at ⊢
  all_goals try simp only [h96, h104, hbx, ha, hb] at ⊢
  vc_by_shape
  | load => run_loads [kp, ka, kb]
  | goto ".LB.plan.12" =>
    rename_i hc
    rw [MachineData.status_mk, Idioms.cmp_a_imm _ 1024 (by decide)] at hc
    simp only [hregs, hdi, hsi, decide_eq_true_eq] at hc
    exact False.elim (by omega)
  | goto ".LB.plan.13" =>
    rename_i hm hn af he
    rw [MachineData.status_mk, Idioms.cmp_a_imm _ 1 (by decide)] at he
    symexec_norm at he
    simp only [h96, h104, hbx, ha, hb, low8_widen_extract, decide_eq_true_eq] at he
    have hor := (EntryU.bad_or g.strategy g.allowed).mp he
    exact False.elim (hok.sizes (hor.elim (fun h => Or.inr (Or.inr (Or.inr h)))
      (fun h => Or.inr (Or.inr (Or.inl h)))))
  | goto ".LB.plan.14" =>
    rename_i hm hn af he af' hz
    symexec_norm at hz
    simp only [hregs, hdi, BitVec.and_self, BitVec.zero_eq, beq_iff_eq] at hz
    have hs : idsFrom g.sw g.idCount 0 = true :=
      idsFrom_end _ _ (by have := hok.sw; rw [hz] at this; simpa using this)
    cfg_goto
    · refine Kb.stack (P := Args g F s)
        (fr := fr.take (fr.length - 1) ++ [s.regs.rbx.toBitVec]) (d := 88#64) ?_ (by decide)
      exact ⟨hh, frame88 _⟩
    · simp only [Inv, Names.plan, String.reduceEq, ↓reduceIte]
      exact ⟨⟨_, ⟨⟨⟨hh, frame88 _⟩, hlo, rfl, rfl, rfl, rfl, rfl⟩,
        hdi, hsi, hdx, hcx, h9⟩, hs⟩, hz⟩
    · left
      simp only [V, Names.plan, String.reduceEq, ↓reduceIte, or_false, or_true]
      omega
  | goto ".LB.plan.1" =>
    rename_i hm hn af he af' hz
    symexec_norm at hz
    simp only [hregs, hdi, BitVec.and_self, BitVec.zero_eq, beq_eq_false_iff_ne] at hz
    cfg_goto
    · refine Kb.stack (P := Args g F s)
        (fr := fr.take (fr.length - 1) ++ [s.regs.rbx.toBitVec]) (d := 88#64) ?_ (by decide)
      exact ⟨hh, frame88 _⟩
    · simp only [Inv, Names.plan, String.reduceEq, ↓reduceIte]
      refine ⟨_, ⟨⟨⟨hh, frame88 _⟩, hlo, rfl, rfl, rfl, rfl, rfl⟩,
        hdi, hsi, hdx, hcx, h9⟩, ?_, rfl⟩
      change 0#64 < g.m
      exact positive _ hz
    · left
      simp only [V, Names.plan, String.reduceEq, ↓reduceIte, rax, Reg64s.get64_rax,
        MachineData.regs_mk, Reg64s.get, BitVec.toNat_ofNat, Nat.zero_mod, Nat.sub_zero]
      omega

theorem b_9 : planAsm.ForallBlocks fun blk =>
    blk.label = .label ".LB.plan.9" → Obl g F s ra blk := by
  cfg_block [Obl]
  intro t ht
  simp only [Inv, Names.plan, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨lo, hb, hdx⟩ := ht
  have kp := hb.popSome
  rw [BitVec.add_comm] at kp
  kvcgen64
  all_goals try symexec_norm at ⊢
  vc_by_shape
  | load => with_reducible exact kp
  | retAddr =>
    refine Option.isSome_iff_exists.mpr ⟨ra, Kg.retAddr
      (P := Args g F s) (s := s) (fr := lo ++ [s.regs.rbx.toBitVec]) ?_⟩
    exact hb.pop rfl rfl rfl rfl rfl rfl rfl rfl
  | ret =>
    refine Kg.ret (P := Args g F s) (fr := lo ++ [s.regs.rbx.toBitVec]) ?_
      fun u hmem hax => ?_
    · exact hb.pop rfl rfl rfl rfl rfl rfl rfl rfl
    · exact ⟨hax.trans hdx, lo ++ [s.regs.rbx.toBitVec], ra.toBitVec,
        by simp [hb.len], hmem ▸ hb.kb.mem⟩

end
end Bbu.Unit.EntryRejectIds
