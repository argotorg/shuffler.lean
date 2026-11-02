module

public import BbuKraken.Unit.Plan.ResolveInitAppend
import all BbuKraken.Unit.Plan.ResolveInitAppend
public import BbuKraken.Unit.Run.Load
import all BbuKraken.Unit.Run.Load

@[expose] public section

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

set_option experimental.vcgen true

namespace Bbu.Unit.ResolveU
open Bbu.Sep

set_option maxRecDepth 4096 in
theorem b_4 [Host] [FunDecls]
    (P : Addr) (r : RG) (F : MProp 64) (s : MachineData) (ra : Int64)
    (rest : Label → MachineData → Prop) (var : Label → MachineData → Nat)
    (hok : r.Ok) (ha : resolveA r s) :
    resolveAsm.ForallBlocks fun blk => blk.label = .label ".LB.Planner.resolve.4" →
      Obl P r F s ra (initFullPhase P r F s ra rest) (initFullVar s var) blk := by
  cfg_block [Obl]
  intro t ht
  simp only [Inv, initFullPhase, zphase, initPhase, Names.resolve,
    String.reduceEq, ↓reduceIte, Scan, Bool.false_eq_true] at ht
  obtain ⟨lo, L, u0, count, hc, hbp, hp, hcount, hnext, he⟩ := ht
  have hsize := ha.2.2.1
  have hpN : (rdx t).toNat < MAX_N := Nat.lt_of_lt_of_le (BitVec.lt_def.mp hp) hsize
  have hcN : count.toNat < MAX_N := by have hh := BitVec.le_def.mp hcount; omega
  have hm := hc.bd.kb.mem
  rw [sep_lc] at hm
  obtain ⟨_, hcurm⟩ := RView.working hm
  obtain ⟨_, hplanm⟩ := RView.plan hm
  have h8 : t.regs.r8.toBitVec = r.currentPtr := hc.r8
  have h12 := hc.r12
  have rdCur := MapM.rd_dest hcurm hpN
  have kCur := MapM.isSome_dest hcurm hpN
  let d := Flat.get r.current.dest (rdx t)
  let off := Flat.get r.M.pos d
  have dBound (hd : d ≠ Flat.NONE) : d.toNat < MAX_N := by
    have hd' := (ha.2.2.2.2.2 _ (BitVec.lt_def.mp hp)).resolve_left hd
    exact Nat.lt_of_lt_of_le hd' hok.planner.n
  have offBound (hd : d ≠ Flat.NONE) (ho : off ≠ Flat.NONE) : off.toNat < r.p.m.toNat :=
    (hok.planPos d ((ha.2.2.2.2.2 _ (BitVec.lt_def.mp hp)).resolve_left hd)).resolve_left ho
  have rdPos (hd : d ≠ Flat.NONE) := MapM.rd_pos hplanm (dBound hd)
  have kPos (hd : d ≠ Flat.NONE) := MapM.isSome_pos hplanm (dBound hd)
  have rdDest (hd : d ≠ Flat.NONE) (ho : off ≠ Flat.NONE) :=
    MapM.rd_dest hplanm (Nat.lt_of_lt_of_le (offBound hd ho) hok.planner.m)
  have kDest (hd : d ≠ Flat.NONE) (ho : off ≠ Flat.NONE) :=
    MapM.isSome_dest hplanm (Nat.lt_of_lt_of_le (offBound hd ho) hok.planner.m)
  obtain ⟨_, hslot⟩ := hc.bd.typedWord (6 + count.toNat) (by change count.toNat < 1024 at hcN; omega)
  have kslot := Wd.isSome hslot
  unfold rd at rdCur rdPos rdDest
  symexec_norm at hp hcount hnext he rdCur kCur rdPos kPos rdDest kDest hpN
  change BitVec.ofInt 64 (t.dmem.loadInt
    (slotAt r.currentPtr t.regs.rdx.toBitVec.toNat) 8).get! = d at rdCur
  have hposnext : (t.regs.rdx.toBitVec + 1#64).toNat ≤ MAX_N := by
    change (t.regs.rdx.toBitVec + 1).toNat ≤ MAX_N
    rw [small_succ _ hpN]; omega
  have hcountNext : count ≤ t.regs.rdx.toBitVec + 1#64 := by
    change t.regs.rdx.toBitVec.toNat < 1024 at hpN
    bv_omega
  by_cases hd : d = Flat.NONE
  · have step := he.trans (candidates_skip_dest hp hd)
    kvcgen64
    all_goals try symexec_norm at *
    all_goals try simp only [h8, h12, fold_slot, slot_8192, rdCur, neg_one_eq_none,
      sub_beq_zero, beq_iff_eq, beq_eq_false_iff_ne, not_true_eq_false, hd] at *
    all_goals try contradiction
    vc_by_shape
    | load => run_loads [kCur]
    | goto ".LB.Planner.resolve.3" =>
      cfg_goto
      · exact hc.bd.kb.stack (by decide)
      · simp only [Inv, initFullPhase, zphase, initPhase, Names.resolve,
          String.reduceEq, ↓reduceIte, Scan]
        exact ⟨lo, L, u0, count, hc.next rfl rfl rfl rfl rfl rfl,
          hbp, hp, hcountNext, hposnext, step⟩
      · left
        simp only [V, initFullVar, zvar, initVar, Names.resolve, String.reduceEq, ↓reduceIte, false_or]
        symexec_norm at ⊢
        omega
  · have rp := rdPos hd
    have kp := kPos hd
    change BitVec.ofInt 64 (t.dmem.loadInt
      (slotAt (r.mp + 8192#64) d.toNat) 8).get! = off at rp
    by_cases ho : off = Flat.NONE
    · have step := he.trans (candidates_skip_source hp ho)
      kvcgen64
      all_goals try symexec_norm at *
      all_goals try simp only [h8, h12, fold_slot, slot_8192, rdCur, rp, neg_one_eq_none,
        sub_beq_zero, beq_iff_eq, beq_eq_false_iff_ne, not_true_eq_false, not_false_eq_true, hd, ho] at *
      all_goals try contradiction
      vc_by_shape
      | load => first | run_loads [kCur, kp] | exact kp
      | goto ".LB.Planner.resolve.3" =>
        cfg_goto
        · exact hc.bd.kb.stack (by decide)
        · simp only [Inv, initFullPhase, zphase, initPhase, Names.resolve,
            String.reduceEq, ↓reduceIte, Scan]
          exact ⟨lo, L, u0, count, hc.next rfl rfl rfl rfl rfl rfl,
            hbp, hp, hcountNext, hposnext, step⟩
        · left
          simp only [V, initFullVar, zvar, initVar, Names.resolve, String.reduceEq, ↓reduceIte, false_or]
          symexec_norm at ⊢
          omega
    · have rr := rdDest hd ho
      have kr := kDest hd ho
      by_cases hr : Flat.get r.M.dest off = Flat.NONE
      · have failed := he.trans (candidates_fail hp hd ho hr)
        have hmodel : modelQ r r s .assertionFailed := by
          intro u
          rw [resolve_independent r hok s ha u u0]
          have hf := resolve_failed_candidates (p := r.p.fl) (sp := r.spills)
            (dropped := r.dropped) (excess := rcx s) failed
          exact ⟨congrArg Prod.fst hf, by
            have hsp := congrArg (fun q => q.2.1) hf
            have hdr := congrArg (fun q => q.2.2) hf
            rw [hsp, hdr]⟩
        kvcgen64
        all_goals try symexec_norm at *
        all_goals try simp only [h8, h12, fold_slot, slot_8192, rdCur, rp, rr, neg_one_eq_none,
          sub_beq_zero, beq_iff_eq, beq_eq_false_iff_ne, not_false_eq_true, hd, ho, hr] at *
        all_goals try contradiction
        vc_by_shape
        | load => first | run_loads [kCur, kp, kr] | exact kp | exact kr
        | goto ".LB.Planner.resolve.2" =>
          cfg_goto
          · exact hc.bd.kb.stack (by decide)
          · simp only [Inv, Names.resolve, String.reduceEq, ↓reduceIte, Return]
            exact ⟨r, lo, L.toList, hc.bd.next rfl rfl, hok, hmodel⟩
          · left
            simp only [V, initFullVar, zvar, initVar, Names.resolve, String.reduceEq, ↓reduceIte,
              or_false]
            omega
      · have offSmall : off < r.p.m := BitVec.lt_def.mpr (offBound hd ho)
        have append (u : MachineData)
            (hm : u.dmem = t.dmem.storeInt
              (t.regs.rsp.toBitVec + BitVec.ofNat 64 (8 * (6 + count.toNat))) 8 off.toInt)
            (hsp : u.regs.rsp = t.regs.rsp)
            (h12 : u.regs.r12 = t.regs.r12) (h14 : u.regs.r14 = t.regs.r14)
            (h8 : r8 u = r8 t) (h9 : r9 u = r9 t) :=
          candidate_append hc hcN offSmall hr hm hsp h12 h14 h8 h9
        have step := he.trans (candidates_add hp hd ho hr)
        change candidateStart r s u0 = Flat.candidatesFrom r.M r.current s.regs.r9.toBitVec
          (t.regs.rdx.toBitVec + 1#64) (Flat.put L.candidates count off) (count + 1#64) at step
        rw [put_eq_set _ count off hcN] at step
        have haSlot : slotAt t.regs.rsp.toBitVec count.toNat + 48#64 =
            t.regs.rsp.toBitVec + BitVec.ofNat 64 (8 * (6 + count.toNat)) := by
          simp only [slotAt, Nat.mul_add, BitVec.ofNat_add]
          bv_omega
        kvcgen64
        all_goals try symexec_norm at *
        all_goals try simp only [h8, h12, hbp, fold_slot, slot_8192, rdCur, rp, rr, neg_one_eq_none,
          sub_beq_zero, beq_iff_eq, beq_eq_false_iff_ne, not_false_eq_true, hd, ho, hr, haSlot] at *
        all_goals try contradiction
        vc_by_shape
        | load => first | run_loads [kCur, kp, kr, kslot] | exact kp | exact kr
        | goto ".LB.Planner.resolve.3" =>
          cfg_goto
          · exact hc.bd.kb.stack (by decide)
          · simp only [Inv, initFullPhase, zphase, initPhase, Names.resolve,
              String.reduceEq, ↓reduceIte, Scan]
            refine ⟨lo, { L with candidates := L.candidates.set count.toNat off }, u0,
              count + 1#64, ?_, ?_, hp, ?_, hposnext, ?_⟩
            · apply append
              · rfl
              · rfl
              · rfl
              · rfl
              · exact hc.r8
              · rfl
            · rfl
            · change count.toNat < 1024 at hcN
              change t.regs.rdx.toBitVec.toNat < 1024 at hpN
              change count + 1#64 ≤ t.regs.rdx.toBitVec + 1#64
              bv_omega
            · exact step
          · left
            simp only [V, initFullVar, zvar, initVar, Names.resolve, String.reduceEq, ↓reduceIte, false_or]
            symexec_norm at ⊢
            omega

end Bbu.Unit.ResolveU
