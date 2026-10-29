import BbuKraken.Fn.PushDup

/-!
The body triple of `push` (`c/bbu/push.S`). `push` saves three registers, calls
`positionOf`, and then writes the new slot and the operation.
-/

open Std.WP Lean.Order
open scoped Program.WP

set_option experimental.vcgen true

namespace Bbu

namespace PushFn
open PushDup

section
variable (s : MachineData) (ra : Int64)

-- `.LB22`: `positionOf` found a slot for the destination.
def At22 (t : MachineData) : Prop :=
  Fm s ra t.dmem ∧ t.regs.rsp.toBitVec = rsp s - 32#64 ∧ t.regs.r13 = s.regs.r13
    ∧ t.regs.r14 = s.regs.r14 ∧ t.regs.r15 = s.regs.r15
    ∧ add (st s) (rsi s) (rdx s).toNat (.push (rsi s)) = .error .assertion

-- `.LB20`: the result is in `rax` and in memory.
def At20 (t : MachineData) : Prop :=
  Fm s ra t.dmem ∧ t.regs.rsp.toBitVec = rsp s - 32#64 ∧ t.regs.r13 = s.regs.r13
    ∧ t.regs.r14 = s.regs.r14 ∧ t.regs.r15 = s.regs.r15 ∧ pushR s t

end

variable {s : MachineData} {ra : Int64}

theorem at20_ok {c t : MachineData} (hpre : Pre 40 pushA s) (hA : After s ra c)
    (hnone : positionOf (st s) (rdx s).toNat = none)
    (hm : t.dmem = stores c.dmem (rdi s) (rsi s) (rdx s) 2 (rsi s))
    (hax : t.regs.rax.toBitVec = 0#64) (hsp : t.regs.rsp.toBitVec = rsp s - 32#64)
    (h13 : t.regs.r13 = s.regs.r13) (h14 : t.regs.r14 = s.regs.r14) (h15 : t.regs.r15 = s.regs.r15) :
    At20 s ra t := by
  have hl := hA.fm.lay hpre hpre.2.2 hA.mst
  refine ⟨hm ▸ hA.fm.after_stores hpre hl _ _ _ _, hsp, h13, h14, h15, ?_⟩
  simp only [pushR, add, hnone, Option.isSome_none, Bool.false_eq_true, ite_false, Res, Ok]
  refine ⟨by simpa [rax] using hax, ?_⟩
  simp only [st', hm, stOf_stores hl, hA.mst, id]
  rfl

end PushFn

open PushDup PushFn

-- A jump to a label of the cfg: the stack, the invariant and the variant.
local macro "cfg_goto" : tactic => `(tactic| (
  apply Program.Intercept.intro_label
  · repeat ((fail_if_success (apply List.getElem?_cons_zero)); (apply List.getElem?_cons_succ_of))
    apply List.getElem?_cons_zero
  refine Or.inl ⟨?_, ?_, ?_⟩))

theorem push_body [Host] [FunDecls]
    (hpos : Spec "positionOf" positionOfF positionOfA positionOfR) :
    Body pushAsm pushF pushA pushR := by
  intro s ra
  refine ⟨fun s₀ ⟨h₀, hpre⟩ => ?_⟩
  subst h₀
  replace hpre : Pre 40 pushA s := hpre
  refine Program.WP.cfg (fun
      | .entry, t | .label "push", t => t = s.pushRa ra
      | .label ".LB22", t => At22 s ra t
      | .label ".LB20", t => At20 s ra t
      | _, _ => False)
    (fun | "push", _ => 2 | ".LB22", _ => 1 | _, _ => 0) ?_ rfl
  cfg_cases
  case left t ht =>
    subst ht
    kvcgen64
  case right.left t ht =>
    subst ht
    have hle := hpre.2.1.le
    have hmap0 : Mem.Mapped [frame 40 s] (s.pushRa ra).dmem := hpre.2.1.mapped.storeInt _ _ _
    kvcgen64 [hpos]
    case vc1 | vc2 | vc3 | vc4 =>
      refine Mem.Mapped.loadInt_isSome (bs := [frame 40 s]) ?_ (Or.inl ?_)
      · repeat (first | (with_reducible exact hmap0) | apply Mem.Mapped.storeInt)
      · simp only [Reg64s.get64_rsp, MachineData.regs_pushRa, Reg64s.set64_rsp, rsp] at *
        bv_omega
    case vc5 =>
      refine Kit.Fm.pre (k := 32) (by decide) hpre (Kit.Fm.init (rs := regs) (by decide) hpre) rfl ?_ rfl
        trivial
      simp only [rsp, Reg64s.get64_rsp, MachineData.regs_pushRa, Reg64s.set64_rsp]
      bv_omega
    all_goals
      have hp := ‹Post positionOfF positionOfR _ _›
      have hag := ‹(mod positionOfF _).Agree _ _›
      have hA := after hp hag hpre rfl
        (by simp only [rsp, Reg64s.get64_rsp, MachineData.regs_pushRa, Reg64s.set64_rsp]; bv_omega)
        rfl rfl rfl rfl rfl rfl rfl rfl
      clear hp hag
      clear ‹Post positionOfF positionOfR _ _› ‹(mod positionOfF _).Agree _ _›
      have hl := hA.fm.lay hpre hpre.2.2 hA.mst
      have hw := hA.fm.wf
      obtain ⟨h1, h2, h3, h4⟩ := hl.nat
      have hn := hl.nops
      have hln := hl.len
      generalize hnn : nOf _ _ = n at h2 h4 hn
      have h1024 : (st s).len ≤ 1024 := Nat.le_of_lt hpre.2.2.1
      bbu_norm at *
      try simp only [hA.rbx, hA.rbp, hA.r12, hA.r13, hA.r14, hA.r15, hA.ax] at *
      simp only [pos_nz h1024] at *
    case vc6 =>
      cfg_goto
      · apply MachineData.stackAtOrBelow_of_toNat_lt
        have := hA.rsp
        simp only [MachineData.regs_pushRa, Reg64s.get64_rsp, Reg64s.set64_rsp, rsp] at *
        bv_omega
      · exact ⟨hA.fm, hA.rsp, hA.r13, hA.r14, hA.r15,
          by unfold add; simp only [‹(positionOf _ _).isSome = true›, ite_true]⟩
      · simp
    case vc10 | vc14 => decide
    all_goals
      try simp only [shl4] at *
      try bbu_rd
    case vc21 =>
      refine at20_ok hpre hA ?_ rfl rfl hA.rsp rfl rfl rfl
      simpa using ‹(positionOf _ _).isSome = false›
    case vc22 => simp
    all_goals
      refine isSome_of hw ?_ ?_
      · repeat (first | exact hw.mapped | apply Mem.Mapped.storeInt)
      · simp only [writable, readable, opsOf, wordAt, STACK, MAX_N, List.cons_append, Mem.Blocks.Inside,
          Nat.reduceMul, hnn]
        clear hnn
        first
        | (left; bv_omega)
        | (right; left; bv_omega)
        | (right; right; left; bv_omega)
        | (right; right; right; right; left; bv_omega)
  case right.right.left t ht =>
    obtain ⟨hfm, hsp, h13, h14, h15, hR⟩ := ht
    have hle : 40 ≤ s.regs.rsp.toBitVec.toNat := hpre.2.1.le
    have hsp' : t.regs.rsp.toBitVec = s.regs.rsp.toBitVec - 32#64 := hsp
    obtain ⟨h1, h2, h3⟩ := hfm.pops hsp
    kvcgen64
    all_goals simp only [rd_def] at *
    case vc1 | vc2 | vc3 =>
      refine Mem.Mapped.loadInt_isSome hfm.map (Or.inl ?_)
      simp only [Reg64s.get64_rsp, rsp, hsp']
      bv_omega
    case vc4 =>
      simp only [MachineData.retAddr, Option.isSome_map]
      refine Mem.Mapped.loadInt_isSome hfm.map (Or.inl ?_)
      simp only [Reg64s.get64_rsp, rsp, hsp']
      bv_omega
    case vc5 =>
      refine Kit.Fm.ret (by decide) hpre hfm ?_ ?_ fun _ hm hax => res_congr hm hax hR
      · simp only [Reg64s.get64_rsp, rsp, hsp']
        bv_omega
      · intro q hq
        cases q <;> simp_all
  case right.right.right t ht =>
    obtain ⟨hfm, hsp, h13, h14, h15, hadd⟩ := ht
    kvcgen64
    cfg_goto
    · apply MachineData.stackAtOrBelow_of_toNat_lt
      simp only [MachineData.regs_pushRa, Reg64s.get64_rsp, Reg64s.set64_rsp, hsp] at *
      have := hpre.2.1.le
      bv_omega
    · exact ⟨hfm, hsp, h13, h14, h15, by simp only [pushR, hadd, Res]; rfl⟩
    · simp

end Bbu
