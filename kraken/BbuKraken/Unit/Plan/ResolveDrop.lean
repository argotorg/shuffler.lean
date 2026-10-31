import BbuKraken.Unit.Plan.ResolveDropFrame
import BbuKraken.Unit.Plan.ResolveDropSpecs
import BbuKraken.Unit.Run.Load

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

set_option experimental.vcgen true

namespace Bbu.Unit.ResolveU
open Bbu.Sep

theorem b_14 [Host] [FunDecls]
    (P : Addr) (r : RG) (F : MProp 64) (s : MachineData) (ra : Int64)
    (rest : Label → MachineData → Prop) (var : Label → MachineData → Nat)
    (hok : r.Ok) :
    resolveAsm.ForallBlocks fun blk => blk.label = .label ".LB.Planner.resolve.14" →
      Obl P r F s ra (loopPhase P r F s ra (dropPhase P r F s ra rest)) (loopVar s var) blk := by
  cfg_block [Obl]
  intro t ht
  simp only [Inv, loopPhase, dropPhase, Names.resolve, String.reduceEq,
    ↓reduceIte, DropReady] at ht
  obtain ⟨w, lo, L, best, h, h15, hbest, hm⟩ := ht
  have ho := Nat.lt_of_lt_of_le (BitVec.lt_def.mp hbest) hok.planner.m
  have hi : best.toNat / 8 < 128 := by have hh : best.toNat < 1024 := ho; omega
  let t1 : MachineData := { t with dmem := (t.dmem.storeInt
    (t.regs.rsp.toBitVec + 8240#64 + best) 1 1) }
  obtain ⟨v, hb1, hdn⟩ := h.bd.dropLocal (u := t1) ho rfl rfl
  let L1 : Lc := { L with droppedWords := L.droppedWords.set (best.toNat / 8) v hi }
  change Bd P (w.ghost r) F s ra lo L1.toList t1 at hb1
  change L1.droppedNow = Flat.put L.droppedNow best 1 at hdn
  rw [h.droppedNow] at hdn
  let t2 : MachineData := { t1 with dmem := t1.dmem.storeInt (r.p.drp + best) 1 1 }
  let w' := w.drop best
  have hb2 : Bd P (w'.ghost r) F s ra lo L1.toList t2 :=
    hb1.storeDropped (BitVec.lt_def.mp hbest) ho 1 rfl rfl
  let t3 : MachineData := { t2 with dmem := (t2.dmem.storeInt
    (t.regs.rsp.toBitVec + 32#64) 8 (w.pass + 1#64).toInt) }
  let L2 := { L1 with pass := w.pass + 1#64 }
  have hb3 := hb2.storeLocal (u := t3) (i := 4) (by simp) (w.pass + 1#64) rfl rfl
  rw [Lc.set_pass] at hb3
  change Bd P (w'.ghost r) F s ra lo L2.toList t3 at hb3
  have kdn := h.bd.zeroByteSome ho
  obtain ⟨_, hpv⟩ := RView.pv hb1.kb.vmem
  obtain ⟨_, hptr⟩ := PView.droppedPtr hpv
  have kptr := Wd.isSome hptr
  have rptr := Wd.rd hptr
  change rd t1.dmem (P + 48#64) = r.p.drp at rptr
  obtain ⟨_, hdrop⟩ := RView.dropped hb1.kb.vmem
  have kd := SpillSetProof.Bs.isSome hdrop (x := best)
    (by simpa only [List.length_take, Vector.length_toList, Work.ghost] using
      Nat.lt_min.mpr (And.intro (BitVec.lt_def.mp hbest) ho))
  obtain ⟨_, hp2⟩ := hb2.typedWord 4 (by decide)
  have kp2 := Wd.isSome hp2
  have rp2 := Wd.rd hp2
  change rd t2.dmem (t.regs.rsp.toBitVec + 32#64) = L.pass at rp2
  rw [h.pass] at rp2
  obtain ⟨_, hp3⟩ := hb3.typedWord 4 (by decide)
  have kp3 := Wd.isSome hp3
  have rp3 := Wd.rd hp3
  change rd t3.dmem (t.regs.rsp.toBitVec + 32#64) = w.pass + 1#64 at rp3
  have hbase3 : loopBase s t3 = (rcx s - (w.pass + 1#64)).toNat * 32768 := by
    unfold loopBase
    change (rcx s - rd t3.dmem (t.regs.rsp.toBitVec + 32#64)).toNat * 32768 = _
    rw [rp3]
  obtain ⟨_, he3⟩ := hb3.typedWord 3 (by decide)
  have ke3 := Wd.isSome he3
  have re3 := Wd.rd he3
  change rd t3.dmem (t.regs.rsp.toBitVec + 24#64) = L.excess at re3
  rw [h.excess] at re3
  have haddr : t.regs.rsp.toBitVec + best + 8240#64 =
      t.regs.rsp.toBitVec + 8240#64 + best := by bv_omega
  have hinc : 1#64 + w.pass = w.pass + 1#64 := by bv_omega
  have hstore : (w.pass.toInt + (1#64).toInt).bmod (2 ^ 64) =
      (w.pass + 1#64).toInt := (BitVec.toInt_add _ _).symm
  have hpass : w.pass < rcx s := h.ok.pass
  have hsub : (rcx s - (w.pass + 1#64)).toNat + 1 = (rcx s - w.pass).toNat := by bv_omega
  simp only [rcx, Reg64s.get64_rcx] at hpass hsub hbase3
  change (t1.dmem.loadInt (P + 48#64) 8).isSome = true at kptr
  change (t1.dmem.loadInt (r.p.drp + best) 1).isSome = true at kd
  change (t2.dmem.loadInt (t.regs.rsp.toBitVec + 32#64) 8).isSome = true at kp2
  change (t3.dmem.loadInt (t.regs.rsp.toBitVec + 32#64) 8).isSome = true at kp3
  change (t3.dmem.loadInt (t.regs.rsp.toBitVec + 24#64) 8).isSome = true at ke3
  unfold rd at rptr rp2 rp3 re3
  dsimp only [t1, t2, t3] at kptr kd kp2 kp3 ke3 rptr rp2 rp3 re3
  kvcgen64 [mov_byte_idx_imm_spec]
  all_goals try symexec_norm at ⊢
  all_goals try simp only [h15, h.r14, haddr, rptr, rp2, hinc, hstore, rp3, re3] at ⊢
  vc_by_shape
  | load => run_loads [kdn, kptr, kd, kp2, kp3, ke3]
  | goto ".LB.Planner.resolve.8" =>
    rename_i hj
    symexec_norm at hj
    simp only [h15, h.r14, haddr, rptr, rp2, hinc, hstore, rp3, re3,
      Idioms.sub_beq_zero, Bool.not_eq_true', beq_eq_false_iff_ne, BitVec.zero_eq] at hj
    have hn : w.pass + 1#64 ≠ rcx s := hj
    have hlt : w.pass + 1#64 < rcx s := by
      simp only [rcx, Reg64s.get64_rcx] at hn ⊢
      bv_omega
    cfg_goto
    · exact h.bd.kb.stack (by decide)
    · simp only [Inv, loopPhase, Names.resolve, String.reduceEq, ↓reduceIte, Outer]
      exact ⟨w', lo, L2,
        ⟨hb3.next rfl rfl, h.candidates, hdn, h.count, rfl, h.excess,
          ⟨h.ok.count, hlt, h.ok.bounded, h.ok.live⟩, h.r12, h.r14, h.r13⟩, hm⟩
    · left
      simp only [V, loopVar, String.reduceEq, false_or, ↓reduceIte]
      change loopBase s t3 + 20000 + 2 < loopBase s t + 4 + 2
      rw [hbase3, h.base]
      simp only [rcx, Reg64s.get64_rcx]
      omega
  | goto ".LB.Planner.resolve.3" =>
    rename_i hj
    symexec_norm at hj
    simp only [h15, h.r14, haddr, rptr, rp2, hinc, hstore, rp3, re3,
      Idioms.sub_beq_zero, Bool.not_eq_false', beq_iff_eq, BitVec.zero_eq] at hj
    have he : w.pass + 1#64 = rcx s := hj
    have hq : modelQ r (w'.ghost r) s .dropped := by
      apply Work.modelQ hm
      rw [Work.result, pass_done (by change ¬w.pass + 1#64 < rcx s; rw [he]; exact BitVec.lt_irrefl _)]
      rfl
    cfg_goto
    · exact h.bd.kb.stack (by decide)
    · simp only [Inv, Names.resolve, String.reduceEq, ↓reduceIte, Result]
      exact ⟨w'.ghost r, lo, L2.toList, .dropped, hb3.next rfl rfl,
        update_ok hok _ _, hq, rfl⟩
    · left
      simp only [V, loopVar, String.reduceEq, false_or, ↓reduceIte]
      omega

end Bbu.Unit.ResolveU
