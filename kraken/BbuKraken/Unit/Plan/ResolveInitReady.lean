import BbuKraken.Unit.Plan.ResolveInitDefs

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

set_option experimental.vcgen true

namespace Bbu.Unit.ResolveU
open Bbu.Sep

theorem candidate_pass_frame {P : Addr} {r : RG} {F : MProp 64} {s t u : MachineData}
    {ra : Int64} {lo : List Word} {L : Lc} {count : Word}
    (hb : Bd P r F s ra lo L.toList t)
    (hm : u.dmem = (t.dmem.storeInt (t.regs.rsp.toBitVec + 32#64) 8 0).storeInt
      (t.regs.rsp.toBitVec + 40#64) 8 count.toInt)
    (hsp : u.regs.rsp = t.regs.rsp) :
    Bd P r F s ra lo ({ L with pass := 0#64, count := count }.toList) u := by
  let v : MachineData := { t with dmem := t.dmem.storeInt (t.regs.rsp.toBitVec + 32#64) 8 0 }
  have hv := hb.storeLocal (u := v) (i := 4) (by simp) 0#64 rfl rfl
  rw [L.set_pass] at hv
  have hu := hv.storeLocal (u := u) (i := 5) (by simp) count hm hsp
  rw [Lc.set_count] at hu
  exact hu

theorem candidate_pass_read {P : Addr} {r : RG} {F : MProp 64} {s t u : MachineData}
    {ra : Int64} {lo : List Word} {L : Lc} {count : Word}
    (hb : Bd P r F s ra lo L.toList t)
    (hm : u.dmem = (t.dmem.storeInt (t.regs.rsp.toBitVec + 32#64) 8 0).storeInt
      (t.regs.rsp.toBitVec + 40#64) 8 count.toInt)
    (hsp : u.regs.rsp = t.regs.rsp) :
    rd u.dmem (u.regs.rsp.toBitVec + 32#64) = 0#64 := by
  have hs := candidate_pass_frame hb hm hsp
  obtain ⟨_, hm'⟩ := hs.typedWord 4 (by decide)
  exact Wd.rd hm'

theorem candidate_outer {P : Addr} {r : RG} {F : MProp 64} {s t u : MachineData}
    {ra : Int64} {lo : List Word} {L : Lc} {u0 : Flat.ResolveU} {count : Word}
    (hc : CandidateState P r F s ra lo L u0 count t) (hok : r.Ok) (ha : resolveA r s)
    (he : candidateStart r s u0 = some (L.candidates, count)) (hex : 0#64 < rcx s)
    (hm : u.dmem = (t.dmem.storeInt (t.regs.rsp.toBitVec + 32#64) 8 0).storeInt
      (t.regs.rsp.toBitVec + 40#64) 8 count.toInt)
    (hsp : u.regs.rsp = t.regs.rsp)
    (h12 : u.regs.r12 = t.regs.r12) (h14 : u.regs.r14 = t.regs.r14)
    (h13 : u.regs.r13.toBitVec = u.regs.rsp.toBitVec + 48#64 + 8#64 * count) :
    Outer P r F s ra u := by
  let w : Work := ⟨r.spills, r.dropped, L.droppedNow, L.candidates, count, 0#64⟩
  let L' := { L with pass := 0#64, count := count }
  refine ⟨w, lo, L', ?_, ?_⟩
  · exact ⟨candidate_pass_frame hc.bd hm hsp, rfl, rfl, rfl, rfl, hc.excess,
      ⟨hc.countBound, hex, hc.bounded, hc.live⟩, h12 ▸ hc.r12, h14 ▸ hc.r14, h13⟩
  · exact hc.model hok ha he

theorem b_7 [Host] [FunDecls]
    (P : Addr) (r : RG) (F : MProp 64) (s : MachineData) (ra : Int64)
    (rest : Label → MachineData → Prop) (var : Label → MachineData → Nat)
    (hok : r.Ok) (ha : resolveA r s)
    (h8 : ∀ t, Outer P r F s ra t → rest ".LB.Planner.resolve.8" t)
    (hV : ∀ t, rd t.dmem (t.regs.rsp.toBitVec + 32#64) = 0#64 →
      var ".LB.Planner.resolve.8" t < 67108865) :
    resolveAsm.ForallBlocks fun blk => blk.label = .label ".LB.Planner.resolve.7" →
      Obl P r F s ra (initFullPhase P r F s ra rest) (initFullVar s var) blk := by
  cfg_block [Obl]
  intro t ht
  simp only [Inv, initFullPhase, zphase, initPhase, Names.resolve,
    String.reduceEq, ↓reduceIte, CandidatesDone] at ht
  obtain ⟨lo, L, u0, count, hc, hbp, he⟩ := ht
  obtain ⟨R, hword⟩ := hc.bd.typedWord 3 (by decide)
  have kex := Wd.isSome hword
  have rex := Wd.rd hword
  change (t.dmem.loadInt (t.regs.rsp.toBitVec + 24#64) 8).isSome = true at kex
  change rd t.dmem (t.regs.rsp.toBitVec + 24#64) = L.excess at rex
  rw [hc.excess] at rex
  change BitVec.ofInt 64 (t.dmem.loadInt (t.regs.rsp.toBitVec + 24#64) 8).get! = rcx s at rex
  obtain ⟨_, hp⟩ := hc.bd.typedWord 4 (by decide)
  have kp := Wd.isSome hp
  obtain ⟨_, hn⟩ := hc.bd.typedWord 5 (by decide)
  have kn := Wd.isSome hn
  change (t.dmem.loadInt (t.regs.rsp.toBitVec + 32#64) 8).isSome = true at kp
  change (t.dmem.loadInt (t.regs.rsp.toBitVec + 40#64) 8).isSome = true at kn
  let v : MachineData := { t with dmem := t.dmem.storeInt (t.regs.rsp.toBitVec + 32#64) 8 0 }
  have hv := hc.bd.storeLocal (u := v) (i := 4) (by simp) 0#64 rfl rfl
  rw [Lc.set_pass] at hv
  obtain ⟨_, hn'⟩ := hv.typedWord 5 (by decide)
  have kn' := Wd.isSome hn'
  change ((t.dmem.storeInt (t.regs.rsp.toBitVec + 32#64) 8 0).loadInt
    (t.regs.rsp.toBitVec + 40#64) 8).isSome = true at kn'
  kvcgen64
  all_goals try symexec_norm at ⊢
  vc_by_shape
  | load => first | exact kex | exact kp | exact kn | exact kn'
  | goto ".LB.Planner.resolve.17" =>
    rename_i hj
    symexec_norm at hj
    rw [rex] at hj
    have hx : rcx s = 0#64 := by
      have hh := hj
      simp only [sub_beq_zero, beq_iff_eq] at hh
      exact hh
    cfg_goto
    · exact hc.bd.kb.stack (by decide)
    · simp only [Inv, Names.resolve, String.reduceEq, ↓reduceIte, Return]
      refine ⟨r, lo, L.toList, hc.bd.next rfl rfl, hok, ?_⟩
      intro u
      simp only [hx]
      have hmodel := hc.model hok ha he u
      rw [hx] at hmodel
      have hp0 := pass_done (p := r.p.fl) (M := r.M) (cand := L.candidates)
        (count := count) (excess := 0#64) (k := 0#64)
        (s := ⟨r.spills, r.dropped, L.droppedNow⟩) (by decide)
      rw [hp0] at hmodel
      exact ⟨congrArg Prod.fst hmodel, by
        have hsp := congrArg (fun q => q.2.1) hmodel
        have hdr := congrArg (fun q => q.2.2) hmodel
        change _ = r.spills at hsp
        change _ = r.dropped at hdr
        rw [hsp, hdr]⟩
    · left
      simp only [V, initFullVar, zvar, initVar, Names.resolve, String.reduceEq, ↓reduceIte,
        true_or, or_true, false_or, or_false]
      decide
  | other =>
    rename_i hj
    have hx : 0#64 < rcx s := by
      symexec_norm at hj
      rw [rex] at hj
      have hh : rcx s ≠ 0#64 := by simpa only [sub_beq_zero, beq_eq_false_iff_ne] using hj
      bv_omega
    first
    | (simp only [Inv, initFullPhase, zphase, initPhase, Names.resolve,
         String.reduceEq, ↓reduceIte]
       apply h8
       apply candidate_outer hc hok ha he hx
       · simp only [hbp]
       · rfl
       · rfl
       · rfl
       · change t.regs.rsp.toBitVec + t.regs.rbp.toBitVec * 8#64 + 48#64 = _
         rw [hbp]; bv_omega)
    | (left
       simp only [V, initFullVar, zvar, initVar, Names.resolve, String.reduceEq, ↓reduceIte, false_or]
       apply Nat.add_lt_add_right
       apply hV
       apply candidate_pass_read (count := count) hc.bd
       · simp only [hbp]
       · rfl)

end Bbu.Unit.ResolveU
