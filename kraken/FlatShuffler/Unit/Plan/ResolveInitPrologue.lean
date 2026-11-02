module

public import FlatShuffler.Unit.Plan.ResolveInitDefs
import all FlatShuffler.Unit.Plan.ResolveInitDefs
public import FlatShuffler.Unit.Run.Load
import all FlatShuffler.Unit.Run.Load

@[expose] public section

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

set_option experimental.vcgen true

namespace FlatShuffler.Unit.ResolveU
open FlatShuffler.Sep

theorem prologue_sp (q : Word) :
    q - 8#64 - 8#64 - 8#64 - 8#64 - 8#64 - 8#64 - 9272#64 = q - 9320#64 := by
  bv_omega

set_option maxRecDepth 4096 in
theorem b_fn [Host] [FunDecls]
    (P : Addr) (r : RG) (F : MProp 64) (s : MachineData) (ra : Int64)
    (rest : Label → MachineData → Prop) (var : Label → MachineData → Nat)
    (hok : r.Ok) (ha : resolveA r s) (hdi : rdi s = P) (xs : List Word) (hl : xs.length = resolveD)
    (hk : Kg (RView P r ∗ F) s ra xs (s.pushRa ra)) :
    resolveAsm.ForallBlocks fun blk => blk.label = .label Names.resolve →
      Obl P r F s ra (initFullPhase P r F s ra rest) (initFullVar s var) blk := by
  simp only [Names.resolve]
  cfg_block [Obl]
  intro t ht
  simp only [Inv, Names.resolve, ↓reduceIte] at ht
  subst t
  obtain ⟨hps, _⟩ := hk.pushes (xs := pushWords (s.pushRa ra)) (by simp [pushWords, hl, resolveD])
  let base := (s.pushRa ra).regs.rsp.toBitVec - 9320#64
  let u : MachineData := { s.pushRa ra with
    regs := { (s.pushRa ra).regs with rsp := ⟨base⟩ },
    dmem := pushes (s.pushRa ra).dmem (s.pushRa ra).regs.rsp.toBitVec (pushWords (s.pushRa ra)) }
  obtain ⟨lo, L, hb⟩ := prologue_stack hk hl (t := u) rfl rfl
  obtain ⟨_, hslot⟩ := hb.typedWord 3 (by decide)
  have kslot := Wd.isSome hslot
  change (u.dmem.loadInt (base + 24#64) 8).isSome = true at kslot
  let v : MachineData := { u with dmem := u.dmem.storeInt (base + 24#64) 8 ((s.pushRa ra).regs.rcx.toBitVec.toInt) }
  have hv := hb.storeLocal (u := v) (i := 3) (by simp) (rcx s) rfl rfl
  rw [Lc.set_excess] at hv
  have hm := hv.kb.mem
  rw [sep_lc] at hm
  obtain ⟨_, hp⟩ := RView.pv hm
  have km := plannerObjectOwnedMemory.isSome_m hp
  have rm := plannerObjectOwnedMemory.rd_m hp
  unfold rd at rm
  simp only [pushWords, PushOk] at hps
  rcases hps with ⟨k0, k1, k2, k3, k4, k5, _⟩
  have hdi' : (s.pushRa ra).regs.rdi.toBitVec = P := hdi
  have hsi' : (s.pushRa ra).regs.rsi.toBitVec = r.mp := ha.1
  have h8' : (s.pushRa ra).regs.r8.toBitVec = r.currentPtr := ha.2.1
  dsimp only [v, u, base] at kslot km rm
  simp only [pushWords, pushes] at kslot km rm
  kvcgen64
  all_goals try symexec_norm at ⊢
  all_goals try rw [prologue_sp] at ⊢
  all_goals try simp only [hdi', rm] at ⊢
  vc_by_shape
  | load => run_loads [k0, k1, k2, k3, k4, k5, kslot, km]
  | goto ".LB.Planner.resolve.1" =>
    rename_i hj
    symexec_norm at hj
    rw [prologue_sp] at hj
    simp only [hdi', rm, BitVec.and_self, beq_iff_eq] at hj
    have hx : r.p.m = 0#64 := hj
    cfg_goto
    · exact hv.kb.stack (by decide)
    · simp only [Inv, initFullPhase, zphase, Names.resolve,
        String.reduceEq, ↓reduceIte, AfterZero]
      refine ⟨lo, { L with excess := rcx s }.toList, (by apply hv.next <;> rfl),
        ⟨{ L with excess := rcx s }, rfl, rfl⟩,
        ⟨hsi', hdi', h8', rfl, rfl⟩, ?_⟩
      rw [hx]
      intro q hq
      exact False.elim (by bv_omega)
    · left
      simp only [V, initFullVar, zvar, initVar, Names.resolve, String.reduceEq,
        ↓reduceIte, or_false]
      decide
  | other =>
    rename_i hj
    symexec_norm at hj
    rw [prologue_sp] at hj
    simp only [hdi', rm, BitVec.and_self, beq_eq_false_iff_ne, BitVec.zero_eq] at hj
    have hx : 0#64 < r.p.m := by bv_omega
    first
    | (left
       simp only [V, initFullVar, zvar, initVar, Names.resolve, String.reduceEq,
         ↓reduceIte, or_false]
       simp only [rcx, rax, Reg64s.get64_rcx, Reg64s.get64_rax]
       have hsmall := hok.planner.m
       change r.p.m.toNat ≤ 1024 at hsmall
       have heq : (base + 8240#64 + r.p.m) - (base + 8240#64) = r.p.m := by bv_omega
       change ((base + 8240#64 + r.p.m) - (base + 8240#64)).toNat + 67113864 + 1 + 2 <
         67120000 + 2
       rw [heq]
       omega)
    | (simp only [Inv, initFullPhase, zphase, Names.resolve,
         String.reduceEq, ↓reduceIte, Zero]
       refine ⟨lo, { L with excess := rcx s }.toList, 0#64, ?_, ?_, ?_, hx, ?_, ?_, ?_⟩
       · apply hv.next <;> rfl
       · exact ⟨{ L with excess := rcx s }, rfl, rfl⟩
       · constructor
         · exact hsi'
         · exact hdi'
         · exact h8'
         · simp only [r9, Reg64s.get64_r9, MachineData.pushRa, Reg64s.set64_rsp]
         · simp only [rdx, Reg64s.get64_rdx, MachineData.pushRa, Reg64s.set64_rsp]
       · simp only [rax, Reg64s.get64_rax, BitVec.add_zero]
       · simp only [rcx, Reg64s.get64_rcx]
       · intro q hq; exact False.elim (by bv_omega))

end FlatShuffler.Unit.ResolveU
