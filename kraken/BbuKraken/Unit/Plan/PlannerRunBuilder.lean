import BbuKraken.Unit.Plan.PlannerRunBuilderDefs
import BbuKraken.Unit.Plan.PlannerRunBuilderTail
import Kraken.X64.Parser

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

set_option experimental.vcgen true

namespace Bbu.Unit.PlannerRunU
open Bbu.Sep

theorem status_ne_of_al_eq {t : MachineData} {st : Flat.Status}
    (ha : al t = code st) (hn : al t ≠ 0#8) : st ≠ .done := by
  apply code_ne_zero
  intro he
  exact hn (ha.trans he)

theorem status_eq_of_al_eq {t : MachineData} {st : Flat.Status}
    (ha : al t = code st) (hz : al t = 0#8) : st = .done := by
  apply code_eq_zero
  exact ha.symm.trans hz

def BuildFailed (P : Addr) (g : PlannerRunG) (F : MProp 64) (s : MachineData) (ra : Int64)
    (M0 : Flat.Mapping) (t : MachineData) : Prop :=
  ∃ lo locals, LoopLI P g F s ra lo locals t ∧
    M0.init g.p.m g.p.n = M0 ∧
    Flat.buildMapping (plannerBuilder g s M0 0#8).fl M0 = none

def BuildDone (P : Addr) (g : PlannerRunG) (F : MProp 64) (s : MachineData) (ra : Int64)
    (t : MachineData) : Prop :=
  ∃ M0 M saw lo locals,
    AttemptLI P (withSaw g (mergeSaw g.p.saw saw)) M F s ra lo locals t ∧
    MapInv g.p.m g.p.n M ∧ M0.init g.p.m g.p.n = M0 ∧
    Flat.buildMapping (plannerBuilder g s M0 0#8).fl M0 = some (M, saw != 0#8) ∧
    Flat.targetsFrom g.p.fl g.spills 0 = true

set_option maxRecDepth 4096 in
theorem b_9_calls [Host] [FunDecls] (P : Addr) (g : PlannerRunG) (F : MProp 64)
    (s : MachineData) (ra : Int64) (hok : g.Ok)
    (hip : BSpec Names.mapInPlace mapInPlaceA 3 mapInPlaceQ)
    (hclosest : BSpec Names.mapClosestCopies mapClosestA 7 mapClosestQ)
    (hwild : BSpec Names.mapWildcardSlotCopies mapWildA 9 mapWildQ)
    (hkeep : BSpec Names.keepWildcardSlots keepWildA 3 keepWildQ)
    (habsorb : BSpec Names.absorbSurplus absorbA 3 absorbQ)
    (K : Unit → MachineData → Prop)
    (I' : CfgLabel → Nat → Unit → MachineData → Prop) (E : Int64 → MachineData → Prop)
    (hbad : ∀ lab, lab ∈ [".LB.Planner.run.19", ".LB.Planner.run.20",
        ".LB.Planner.run.21", ".LB.Planner.run.22", ".LB.Planner.run.23"] →
      ∀ M0 u, BuildFailed P g F s ra M0 u →
        Program.Intercept plannerRunAsm.labels (s.pushRa ra) I' E (label lab) u)
    (hfinish : ∀ M0 M saw lo l u, BuildLI P g F s ra lo l M saw u →
      M0.init g.p.m g.p.n = M0 →
      Flat.buildMapping (plannerBuilder g s M0 0#8).fl M0 = some (M, saw != 0#8) →
      WP.wp builderTail K (Program.Intercept plannerRunAsm.labels (s.pushRa ra) I' E) u) :
    plannerRunAsm.ForallBlocks fun blk => blk.label = .label ".LB.Planner.run.9" →
      ∀ t, InitDone P g F s ra t → WP.wp blk.body K
        (Program.Intercept plannerRunAsm.labels (s.pushRa ra) I' E) t := by
  simp only [Names.mapInPlace] at hip
  simp only [Names.mapClosestCopies] at hclosest
  simp only [Names.mapWildcardSlotCopies] at hwild
  simp only [Names.keepWildcardSlots] at hkeep
  simp only [Names.absorbSurplus] at habsorb
  cfg_block
  intro t ⟨lo, locals, hc, hdest, hpos⟩
  obtain ⟨l, hb⟩ := hc.builderSetup
  obtain ⟨_, hp⟩ := pv hc.kb.vmem
  have hsrc := PView.rd_src hp
  have ksrc := PView.isSome_src hp
  have htgt : rd t.dmem (P + 16#64) = g.p.tgt := rd_of_eq hp (by unfold PView; ecancel)
  have ktgt : (t.dmem.loadInt (P + 16#64) 8).isSome = true :=
    isSome_of_eq g.p.tgt hp (by unfold PView; ecancel)
  have hdrp : rd t.dmem (P + 48#64) = g.p.drp := rd_of_eq hp (by unfold PView; ecancel)
  have kdrp : (t.dmem.loadInt (P + 48#64) 8).isSome = true :=
    isSome_of_eq g.p.drp hp (by unfold PView; ecancel)
  have k0 := hc.builderSome 0 (by decide)
  have k1 := hc.builderSome 1 (by decide)
  have k2 := hc.builderSome 2 (by decide)
  have k3 := hc.builderSome 3 (by decide)
  have k4 := hc.builderSome 4 (by decide)
  have k5 := hc.builderSome 5 (by decide)
  have k6 := hc.builderSome 6 (by decide)
  have k7 := hc.builderSome 7 (by decide)
  dsimp only [builderStores, builderStoreMem, BuilderWrite.mem, List.take,
    List.foldl_cons, List.foldl_nil] at k0 k1 k2 k3 k4 k5 k6 k7
  simp only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceEqDiff, or_true,
    or_false, ite_false, ite_true] at k0 k1 k2 k3 k4 k5 k6 k7
  unfold rd at hsrc htgt hdrp
  have h14 : t.regs.r14.toBitVec.extractLsb' 0 8 = (Bbu.rsi s).setWidth 8 :=
    (BitVec.setWidth_eq_extractLsb' (by decide)).symm.trans hc.r14
  simp only [Reg64s.get64_rsi] at h14
  kvcgen64 [hip]
  all_goals try symexec_norm at ⊢
  all_goals try simp only [hc.rbx, hc.rdx, hc.rsi, h14, hsrc, htgt, hdrp] at ⊢
  vc_by_shape
  | load =>
    simp only [ksrc, ktgt, kdrp, k0, k1, k2, k3, k4, k5, k6, k7]
  | other =>
    let M0 := localMapping locals hc.localLength
    have hi0 : M0.init g.p.m g.p.n = M0 :=
      localMapping_init locals hc.localLength hok.planner.m hok.planner.n hdest hpos
    let fb := (plannerBuilder g s M0 0#8).fl
    let r1 := Flat.mapInPlace fb M0
    refine BuildLI.callPhase (P := P) (g := g) (F := F) (s := s) (ra := ra)
      (lo := lo) (l := l) (M := M0) (saw := 0#8) ?_ hok (by decide : 3 ≤ 4112) ?_ trivial
      r1.2 0#8 r1.1 ?_ ?_
    · apply hb.next
      · dsimp only [builderStoreMem, builderStores, BuilderWrite.mem, List.foldl_cons, List.foldl_nil]
        simp only [Nat.reduceMul, BitVec.toInt_zero]
      all_goals rfl
    · exact hc.r13
    · intro b' u hq
      exact hq
    · intro u lo1 h1 ha1 hag1
      kvcgen64 [hclosest]
      all_goals try symexec_norm at ⊢
      vc_by_shape
      | goto ".LB.Planner.run.19" =>
        rename_i af hj
        symexec_norm at hj
        have hs := status_ne_of_al_eq ha1 (al_ne (t := u) (by with_reducible exact hj))
        dsimp only [r1, fb] at hs
        apply hbad ".LB.Planner.run.19" (by simp) M0
        refine ⟨lo1, l.toList (plannerBuilder g s r1.2 0#8), ?_, hi0, ?_⟩
        · exact h1.toLoopLI.next rfl rfl rfl rfl rfl rfl rfl
        · unfold Flat.buildMapping
          dsimp only
          rw [ite_eq_left hs]
      | other =>
        rename_i af hj
        symexec_norm at hj
        have hs1 := status_eq_of_al_eq ha1 (al_zero (t := u) (by with_reducible exact hj))
        dsimp only [r1, fb] at hs1
        let r2 := Flat.mapClosestCopies fb r1.2
        refine BuildLI.callPhase (P := P) (g := g) (F := F) (s := s) (ra := ra) (lo := lo1) (l := l) (M := r1.2) (saw := 0#8) ?_ hok
          (by decide : 7 ≤ 4112) h1.r13 trivial r2.2 0#8 r2.1 ?_ ?_
        · exact h1.next rfl rfl rfl rfl rfl rfl rfl rfl
        · intro b' u hq
          exact hq
        · intro v lo2 h2 ha2 hag2
          kvcgen64 [hwild]
          all_goals try symexec_norm at ⊢
          vc_by_shape
          | goto ".LB.Planner.run.20" =>
            rename_i af hj
            symexec_norm at hj
            have hs := status_ne_of_al_eq ha2 (al_ne (t := v) (by with_reducible exact hj))
            dsimp only [r2, r1, fb] at hs
            apply hbad ".LB.Planner.run.20" (by simp) M0
            refine ⟨lo2, l.toList (plannerBuilder g s r2.2 0#8), ?_, hi0, ?_⟩
            · exact h2.toLoopLI.next rfl rfl rfl rfl rfl rfl rfl
            · unfold Flat.buildMapping
              dsimp only
              rw [ite_eq_right (fun hn => hn hs1), ite_eq_left hs]
          | other =>
            rename_i af hj
            symexec_norm at hj
            have hs2 := status_eq_of_al_eq ha2 (al_zero (t := v) (by with_reducible exact hj))
            dsimp only [r2, r1, fb] at hs2
            let r3 := Flat.mapWildcardSlotCopies fb r2.2 false
            let sw := sawB (plannerBuilder g s r2.2 0#8) r3.2.2
            refine BuildLI.callPhase (P := P) (g := g) (F := F) (s := s) (ra := ra) (lo := lo2) (l := l) (M := r2.2) (saw := 0#8) ?_ hok
              (by decide : 9 ≤ 4112) h2.r13 trivial r3.2.1 sw r3.1 ?_ ?_
            · exact h2.next rfl rfl rfl rfl rfl rfl rfl rfl
            · intro b' u hq
              exact hq
            · intro w lo3 h3 ha3 hag3
              kvcgen64 [hkeep]
              all_goals try symexec_norm at ⊢
              vc_by_shape
              | goto ".LB.Planner.run.21" =>
                rename_i af hj
                symexec_norm at hj
                have hs := status_ne_of_al_eq ha3 (al_ne (t := w) (by with_reducible exact hj))
                dsimp only [r3, r2, r1, fb] at hs
                apply hbad ".LB.Planner.run.21" (by simp) M0
                refine ⟨lo3, l.toList (plannerBuilder g s r3.2.1 sw), ?_, hi0, ?_⟩
                · exact h3.toLoopLI.next rfl rfl rfl rfl rfl rfl rfl
                · unfold Flat.buildMapping
                  dsimp only
                  rw [ite_eq_right (fun hn => hn hs1), ite_eq_right (fun hn => hn hs2), ite_eq_left hs]
              | other =>
                rename_i af hj
                symexec_norm at hj
                have hs3 := status_eq_of_al_eq ha3 (al_zero (t := w) (by with_reducible exact hj))
                dsimp only [r3, r2, r1, fb] at hs3
                let r4 := Flat.keepWildcardSlots fb r3.2.1
                refine BuildLI.callPhase (P := P) (g := g) (F := F) (s := s) (ra := ra) (lo := lo3) (l := l) (M := r3.2.1) (saw := sw) ?_ hok
                  (by decide : 3 ≤ 4112) h3.r13 trivial r4.2 sw r4.1 ?_ ?_
                · exact h3.next rfl rfl rfl rfl rfl rfl rfl rfl
                · intro b' u hq
                  exact hq
                · intro x lo4 h4 ha4 hag4
                  kvcgen64 [habsorb]
                  all_goals try symexec_norm at ⊢
                  vc_by_shape
                  | goto ".LB.Planner.run.22" =>
                    rename_i af hj
                    symexec_norm at hj
                    have hs := status_ne_of_al_eq ha4 (al_ne (t := x) (by with_reducible exact hj))
                    dsimp only [r4, r3, r2, r1, fb] at hs
                    apply hbad ".LB.Planner.run.22" (by simp) M0
                    refine ⟨lo4, l.toList (plannerBuilder g s r4.2 sw), ?_, hi0, ?_⟩
                    · exact h4.toLoopLI.next rfl rfl rfl rfl rfl rfl rfl
                    · unfold Flat.buildMapping
                      dsimp only
                      rw [ite_eq_right (fun hn => hn hs1), ite_eq_right (fun hn => hn hs2),
                        ite_eq_right (fun hn => hn hs3), ite_eq_left hs]
                  | other =>
                    rename_i af hj
                    symexec_norm at hj
                    have hs4 := status_eq_of_al_eq ha4 (al_zero (t := x) (by with_reducible exact hj))
                    dsimp only [r4, r3, r2, r1, fb] at hs4
                    let r5 := Flat.absorbSurplus fb r4.2
                    refine BuildLI.callPhase (P := P) (g := g) (F := F) (s := s) (ra := ra) (lo := lo4) (l := l) (M := r4.2) (saw := sw) ?_ hok
                      (by decide : 3 ≤ 4112) h4.r13 trivial r5.2 sw r5.1 ?_ ?_
                    · exact h4.next rfl rfl rfl rfl rfl rfl rfl rfl
                    · intro b' u hq
                      exact hq
                    · intro y lo5 h5 ha5 hag5
                      vcgen until (parse("
                        movzbl 56(%rbx), %eax
                        testb %al, %al
                        movzbl 88(%rsp), %edx
                        cmove %edx, %eax
                        movb %al, 56(%rbx)
                        cmpq $0, 8(%rbx)
                        je .LB.Planner.run.32
                        movl $0, %eax
                      "))
                      all_goals try symexec_norm at ⊢
                      vc_by_shape
                      | goto ".LB.Planner.run.23" =>
                        rename_i af hj
                        symexec_norm at hj
                        have hs := status_ne_of_al_eq ha5 (al_ne (t := y) (by with_reducible exact hj))
                        dsimp only [r5, r4, r3, r2, r1, fb] at hs
                        apply hbad ".LB.Planner.run.23" (by simp) M0
                        refine ⟨lo5, l.toList (plannerBuilder g s r5.2 sw), ?_, hi0, ?_⟩
                        · exact h5.toLoopLI.next rfl rfl rfl rfl rfl rfl rfl
                        · unfold Flat.buildMapping
                          dsimp only
                          rw [ite_eq_right (fun hn => hn hs1), ite_eq_right (fun hn => hn hs2),
                            ite_eq_right (fun hn => hn hs3), ite_eq_right (fun hn => hn hs4),
                            ite_eq_left hs]
                      | other =>
                        rename_i af hj
                        symexec_norm at hj
                        have hs5 := status_eq_of_al_eq ha5 (al_zero (t := y) (by with_reducible exact hj))
                        dsimp only [r5, r4, r3, r2, r1, fb] at hs5
                        apply hfinish M0 r5.2 sw lo5 l
                        · exact h5.next rfl rfl rfl rfl rfl rfl rfl rfl
                        · exact hi0
                        · have hsw : (sw != 0#8) = r3.2.2 := by
                            change ((bif r3.2.2 then 1#8 else 0#8) != 0#8) = r3.2.2
                            cases r3.2.2 <;> rfl
                          unfold Flat.buildMapping
                          dsimp only
                          rw [ite_eq_right (fun hn => hn hs1), ite_eq_right (fun hn => hn hs2),
                            ite_eq_right (fun hn => hn hs3), ite_eq_right (fun hn => hn hs4),
                            ite_eq_right (fun hn => hn hs5)]
                          change some (r5.2, r3.2.2) = some (r5.2, sw != 0#8)
                          rw [hsw]

set_option maxRecDepth 4096 in
theorem b_9 [Host] [FunDecls] (P : Addr) (g : PlannerRunG) (F : MProp 64)
    (s : MachineData) (ra : Int64) (hok : g.Ok)
    (hip : BSpec Names.mapInPlace mapInPlaceA 3 mapInPlaceQ)
    (hclosest : BSpec Names.mapClosestCopies mapClosestA 7 mapClosestQ)
    (hwild : BSpec Names.mapWildcardSlotCopies mapWildA 9 mapWildQ)
    (hkeep : BSpec Names.keepWildcardSlots keepWildA 3 keepWildQ)
    (habsorb : BSpec Names.absorbSurplus absorbA 3 absorbQ)
    (K : Unit → MachineData → Prop)
    (I' : CfgLabel → Nat → Unit → MachineData → Prop) (E : Int64 → MachineData → Prop)
    (hbad : ∀ lab, lab ∈ [".LB.Planner.run.19", ".LB.Planner.run.20",
        ".LB.Planner.run.21", ".LB.Planner.run.22", ".LB.Planner.run.23"] →
      ∀ M0 u, BuildFailed P g F s ra M0 u →
        Program.Intercept plannerRunAsm.labels (s.pushRa ra) I' E (label lab) u)
    (hzero : ∀ u, g.p.m = 0#64 → BuildDone P g F s ra u →
      Program.Intercept plannerRunAsm.labels (s.pushRa ra) I' E (label ".LB.Planner.run.32") u)
    (hnonzero : ∀ u, g.p.m ≠ 0#64 → rax u = 0#64 → BuildDone P g F s ra u → K () u) :
    plannerRunAsm.ForallBlocks fun blk => blk.label = .label ".LB.Planner.run.9" →
      ∀ t, InitDone P g F s ra t → WP.wp blk.body K
        (Program.Intercept plannerRunAsm.labels (s.pushRa ra) I' E) t := by
  apply b_9_calls P g F s ra hok hip hclosest hwild hkeep habsorb K I' E hbad
  intro M0 M saw lo l u hb hinit hmodel
  have hstart : MapInv g.p.m g.p.n M0 := by
    rw [← hinit]
    exact mapInv_init M0 hok.planner.m hok.planner.n
  have hm : MapInv g.p.m g.p.n M := mapInv_buildMapping hstart hmodel
  apply builder_tail P g F s ra hok M saw lo l u hb K I' E
  · intro v hz hv
    exact hzero v hz ⟨M0, M, saw, lo, _, hv, hm, hinit, hmodel, hb.targets⟩
  · intro v hn hax hv
    exact hnonzero v hn hax ⟨M0, M, saw, lo, _, hv, hm, hinit, hmodel, hb.targets⟩

end Bbu.Unit.PlannerRunU
