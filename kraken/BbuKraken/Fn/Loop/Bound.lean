import BbuKraken.Fn.Loop.BoundLemmas

/-!
The slot bound for `targetOffset` in `buildBottomUp`: `.LB74` (`positionOf`), the search
of a movable copy (`.LB105`, `.LB80`, `.LB78`, `.LB107`, `.LB90`) and the swap of the
dests (`.LB77`).
-/

open Std.WP Lean.Order
open scoped Program.WP

namespace Bbu

namespace Loop

set_option experimental.vcgen true
variable [Host] [FunDecls] {s : MachineData} {ra : Int64}

-- A hypothesis of type `t`, found with reducible unification only.
local macro "hyp% " t:term : term => `((by with_reducible assumption : $t))

-- One form for the model state of `t` in all hypotheses and the goal.
local macro "nrm" : tactic => `(tactic| (try simp only [st', rdi, Reg64s.get64_rdi] at *))

local macro "nomega" : tactic => `(tactic| (nrm; omega))

-- `.LB74`: `positionOf targetOffset` gives the slot bound for `targetOffset`.
theorem lb74 (hpre : Pre loopF loopA s) : OblAt s ra (.label ".LB74") := by
  loop_case
  intro t ht
  have h : At74 s ra t := ht
  obtain ⟨hb, h15, T, h14, hctx, hpd, hst⟩ := h
  have hp : Pos (env s).n (st' s t) := hctx.2.1.1.pos
  obtain ⟨-, hnM, hTl, -⟩ := ctx_bounds hctx
  have hTn : T < (env s).n := hctx.1
  have hM : MAX_N = 1024 := rfl
  have hn := hb.n_env hpre
  have hl := hb.len_le
  have hr14 : t.regs.r14.toBitVec.toNat = T := by rw [h14]; exact toNat_small (by nomega)
  have hpY := hb.pos (x := t.regs.r14.toBitVec) (by nomega)
  rw [hr14] at hpY
  kvcgen64
  all_goals try bbu_norm at *
  all_goals nrm
  all_goals generalize hY : rd t.dmem (t.regs.rbp.toBitVec + t.regs.r14.toBitVec * 8#64 + 8264#64) = Y at *
  case vc1 => exact hb.pos_isSome (by nomega)
  case vc2 =>
    have hz := (hyp% CondCode.z.interp _ = true)
    rw [Kit.z_sub, beq_iff_eq] at hz
    have hnone : positionOf (stOf t.dmem s.regs.rdi.toBitVec) T = none := by
      rw [← hpY, hz]; rfl
    rw [bound_none hnone] at hst
    loop_goto
    · exact stack_mk hb.rsp
    · exact at75_mk hb rfl rfl h14 hctx hpd hst
    · simp only [V, outer_mk rfl]; omega
  case vc3 =>
    have hz := (hyp% CondCode.z.interp _ = false)
    rw [Kit.z_sub, beq_eq_false_iff_ne] at hz
    have hc := (hyp% CondCode.c.interp _ = true)
    simp only [CondCode.interp_c, StatusFlags.cf_from_result] at hc
    rw [Kit.cf_sub, hr14] at hc
    rw [bound_lt (pos_some hpY hz) hc] at hst
    loop_goto
    · exact stack_mk hb.rsp
    · exact ⟨base_mk hb rfl rfl, iter_err ⟨_, hctx, hst⟩⟩
    · simp only [V]; omega
  case vc4 => exact hb.data_isSome
  case vc5 =>
    obtain ⟨-, hYl, -⟩ := bound_y hpY hp (by with_reducible assumption) (by with_reducible assumption) hr14
    nrm
    exact hb.slot_isSome hb.data hYl
  case vc6 =>
    obtain ⟨-, hYl, hTY⟩ := bound_y hpY hp (by with_reducible assumption) (by with_reducible assumption) hr14
    nrm
    exact hb.slot_isSome hb.data (by nomega)
  case vc7 => decide
  case vc8 =>
    obtain ⟨hsome, hYl, hTY⟩ := bound_y hpY hp (by with_reducible assumption) (by with_reducible assumption) hr14
    nrm
    have hv := (hyp% CondCode.nz.interp _ = true)
    rw [nz_res, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq, same hb.data hYl (by nomega),
      hr14] at hv
    rw [bound_pos hsome hTY (fun h => hv h.symm)] at hst
    loop_goto
    · exact stack_mk hb.rsp
    · exact at105_mk hb rfl rfl rfl rfl h15 h14 hctx rfl rfl rfl rfl hYl hst
    · simp only [V, outer_mk rfl]; omega
  case vc9 => exact hb.dest_isSome (by nomega)
  case vc10 =>
    obtain ⟨-, hYl, -⟩ := bound_y hpY hp (by with_reducible assumption) (by with_reducible assumption) hr14
    nrm
    exact hb.dest_isSome (by nomega)
  case vc11 => exact hb.dest8_isSome (by nomega)
  case vc12 =>
    obtain ⟨-, hYl, -⟩ := bound_y hpY hp (by with_reducible assumption) (by with_reducible assumption) hr14
    nrm
    apply loadInt_isSome_store
    exact hb.dest_isSome (by nomega)
  case vc13 =>
    repeat apply loadInt_isSome_store
    exact hb.dest8_isSome (by nomega)
  case vc14 =>
    obtain ⟨-, hYl, hTY⟩ := bound_y hpY hp (by with_reducible assumption) (by with_reducible assumption) hr14
    nrm
    repeat apply loadInt_isSome_store
    exact hb.pos_isSome (hb.m2_lt hpre hp (by nomega) hYl)
  case vc15 =>
    obtain ⟨-, hYl, hTY⟩ := bound_y hpY hp (by with_reducible assumption) (by with_reducible assumption) hr14
    nrm
    have hd := hb.dest (x := t.regs.r14.toBitVec) (by nomega)
    have hd2 := Pos.dest_lt hp (a := t.regs.r14.toBitVec.toNat) (by nomega)
    nrm
    repeat apply loadInt_isSome_store
    exact hb.pos_isSome (by nomega)
  case vc16 =>
    obtain ⟨hsome, hYl, hTY⟩ := bound_y hpY hp (by with_reducible assumption) (by with_reducible assumption) hr14
    nrm
    have hv := (hyp% CondCode.nz.interp _ = false)
    rw [nz_res, Bool.not_eq_false', beq_iff_eq, same hb.data hYl (by nomega), hr14] at hv
    rw [bound_eq hsome hTY hv.symm] at hst
    rw [swapMem_eq]
    exact at64_mk hpre hb hp (by nomega) (by nomega) (by rw [hb.rbp, hr14]) rfl rfl h14 ⟨_, hctx, hst⟩
  case vc17 =>
    obtain ⟨hsome, hYl, hTY⟩ := bound_y hpY hp (by with_reducible assumption) (by with_reducible assumption) hr14
    nrm
    rw [swapMem_eq]
    left
    simp only [V]
    rw [outer_swap (d := swapMem t.dmem t.regs.rbp.toBitVec t.regs.r14.toBitVec.toNat Y.toNat)
      (a := t.regs.r14.toBitVec.toNat) (b := Y.toNat) hpre hb hp
      (by nomega) (by nomega) (by rw [hb.rbp])]
    have h1 : (t.regs.r14.toBitVec + 1#64).toNat = T + 1 := by bv_omega
    simp only [outer, W, h1, env]
    nomega

-- `.LB105`: the slot `sourceForTargetOffset` is bound; the search of a movable copy.
theorem lb105 (_hpre : Pre loopF loopA s) : OblAt s ra (.label ".LB105") := by
  loop_case
  intro t ht
  have h : At105 s ra t := ht
  obtain ⟨T, b, hc, hw, hst⟩ := h
  obtain ⟨hl, -, -, -⟩ := hc.bounds
  have hbl : b < (st' s t).len := hc.2.2.2.2.2.2.1
  have hx : t.regs.r15.toBitVec - t.regs.rax.toBitVec = BitVec.ofNat 64 ((st' s t).len - b) := by
    rw [hc.2.1, hc.2.2.2.1]; exact sub_of (by omega)
  have hsi : t.regs.r15.toBitVec + -1#64 = BitVec.ofNat 64 ((st' s t).len - 1) := by
    rw [hc.2.1]; exact ofNat_pred (by omega)
  kvcgen64
  all_goals try bbu_norm
  all_goals nrm
  case vc1 =>
    have hz := (hyp% CondCode.z.interp _ = true)
    try bbu_norm at hz
    rw [Kit.z_sub, beq_iff_eq, hx] at hz
    have h1 : b + 1 = (st' s t).len := by
      have := ofNat_inj64 (by nomega) (by nomega) hz
      nomega
    nrm
    loop_goto
    · exact stack_mk hc.1.rsp
    · rw [movableCopy_last h1] at hst
      exact at90_mk hc rfl rfl rfl rfl rfl rfl rfl rfl hst
    · simp only [V, outer_mk rfl]
      nomega
  case vc2 =>
    have hz := (hyp% CondCode.z.interp _ = false)
    try bbu_norm at hz
    rw [Kit.z_sub, beq_eq_false_iff_ne, hx] at hz
    have h1 : ¬ (st' s t).len - b = 1 := fun h1 => hz (congrArg (BitVec.ofNat 64) h1)
    nrm
    loop_goto
    · exact stack_mk hc.1.rsp
    · rw [movableCopy_eq hbl] at hst
      exact at80_mk hc hw rfl rfl rfl rfl rfl rfl rfl rfl rfl hsi (by nomega) (by nomega) hst
    · simp only [V, outer_mk rfl]
      left
      rw [hsi, toNat_small (by nomega)]
      nomega

-- `.LB78`: `candidate` is not a movable copy.
theorem lb78 (_hpre : Pre loopF loopA s) : OblAt s ra (.label ".LB78") := by
  loop_case
  intro t ht
  have h : At78 s ra t := ht
  obtain ⟨T, b, c, hc, hw, hsi, hbc, hcl, hst⟩ := h
  obtain ⟨hl, -, -, -⟩ := hc.bounds
  have hx : t.regs.rsi.toBitVec - 1#64 = BitVec.ofNat 64 (c - 1) := by
    rw [hsi]; exact ofNat_sub1 (by omega)
  have hax := hc.2.2.2.1
  kvcgen64
  all_goals try bbu_norm
  all_goals nrm
  case vc1 =>
    have hz := (hyp% CondCode.z.interp _ = true)
    rw [Kit.z_sub, beq_iff_eq, hx, hax] at hz
    have h1 : b = c - 1 := ofNat_inj64 (by nomega) (by nomega) hz
    loop_goto
    · exact stack_mk hc.1.rsp
    · rw [← h1, movFrom_self] at hst
      exact at90_mk hc rfl rfl rfl rfl rfl rfl rfl rfl hst
    · simp only [V, outer_mk rfl]
      nomega
  case vc2 =>
    have hz := (hyp% CondCode.z.interp _ = false)
    rw [Kit.z_sub, beq_eq_false_iff_ne, hx, hax] at hz
    have h1 : b ≠ c - 1 := fun h1 => hz (congrArg (BitVec.ofNat 64) h1)
    exact at80_mk hc hw rfl rfl rfl rfl rfl rfl rfl rfl rfl hx (by omega) (by nomega) hst
  case vc3 =>
    simp only [V, outer_mk rfl]
    left
    rw [hx, hsi, toNat_small (by nomega), toNat_small (by nomega)]
    omega

-- `.LB107`: no copy is movable, so the slot at `sourceForTargetOffset` stays.
theorem lb107 (_hpre : Pre loopF loopA s) : OblAt s ra (.label ".LB107") := by
  loop_case
  intro t ht
  have h : At90 s ra t := ht
  obtain ⟨T, b, hc, hst⟩ := h
  kvcgen64
  all_goals try bbu_norm
  all_goals nrm
  case vc1 => exact at77_mk hc rfl rfl rfl rfl rfl rfl rfl rfl hc.2.2.2.1 hc.2.2.2.2.2.2.1 hst
  case vc2 => simp only [V, outer_mk rfl]; omega

-- `.LB90`: no copy is movable, so the slot at `sourceForTargetOffset` stays.
theorem lb90 (_hpre : Pre loopF loopA s) : OblAt s ra (.label ".LB90") := by
  loop_case
  intro t ht
  have h : At90 s ra t := ht
  obtain ⟨T, b, hc, hst⟩ := h
  kvcgen64
  all_goals try bbu_norm
  all_goals nrm
  loop_goto
  · exact stack_mk hc.1.rsp
  · exact at77_mk hc rfl rfl rfl rfl rfl rfl rfl rfl hc.2.2.2.1 hc.2.2.2.2.2.2.1 hst
  · simp only [V, outer_mk rfl]; omega

-- `.LB80`: the search at `candidate`.
theorem lb80 (_hpre : Pre loopF loopA s) : OblAt s ra (.label ".LB80") := by
  loop_case
  intro t ht
  have h : At80 s ra t := ht
  obtain ⟨T, b, c, hc, hw, hsi, hbc, hcl, hst⟩ := h
  obtain ⟨hl, -, -, -⟩ := hc.bounds
  have hbl : b < (st' s t).len := hc.2.2.2.2.2.2.1
  have hxc : t.regs.rsi.toBitVec.toNat = c := by rw [hsi]; exact toNat_small (by omega)
  have hxl : t.regs.rsi.toBitVec.toNat < (st' s t).len := by rw [hxc]; exact hcl
  have hsame := same_src hc.2.2.2.2.1 hbl hxl
  have hdest := hc.1.dest hxl
  have hload := hc.1.slot_isSome hc.2.2.2.2.1 hxl
  have hdl := hc.1.dest_isSome (x := t.regs.rsi.toBitVec) (by omega)
  kvcgen64
  all_goals try bbu_norm
  all_goals nrm
  case vc1 => exact hload
  case vc2 => decide
  case vc3 =>
    have hz := (hyp% CondCode.nz.interp _ = true)
    bbu_norm at hz
    rw [nz_res, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq, hw, hsame, hxc] at hz
    loop_goto
    · exact stack_mk hc.1.rsp
    · rw [movFrom_no hbc (fun hv => absurd hv.symm hz)] at hst
      exact at78_mk hc hw rfl rfl rfl rfl rfl rfl rfl rfl rfl hsi hbc hcl hst
    · simp only [V, outer_mk rfl]
      omega
  case vc4 => exact hdl
  case vc5 =>
    have hz := (hyp% CondCode.z.interp _ = true)
    bbu_norm at hz
    rw [Kit.z_sub, beq_iff_eq] at hz
    have hd : (st' s t).dest c = c := by nrm; rw [← hxc, ← hdest, hz]
    nrm
    loop_goto
    · exact stack_mk hc.1.rsp
    · rw [movFrom_no hbc (fun _ => hd)] at hst
      exact at78_mk hc hw rfl rfl rfl rfl rfl rfl rfl rfl rfl hsi hbc hcl hst
    · simp only [V, outer_mk rfl]
      omega
  case vc6 => exact hload
  case vc7 => decide
  case vc8 =>
    have hz := (hyp% CondCode.z.interp _ = false)
    have hv := (hyp% CondCode.z.interp _ = true)
    bbu_norm at hz hv
    rw [Kit.z_sub, beq_eq_false_iff_ne] at hz
    rw [z_res, beq_iff_eq, hw, hsame, hxc] at hv
    have hd : (st' s t).dest c ≠ c := by
      nrm; rw [← hxc, ← hdest]; exact fun h => hz (BitVec.eq_of_toNat_eq h)
    nrm
    loop_goto
    · exact stack_mk hc.1.rsp
    · rw [movFrom_yes hbc hv.symm hd] at hst
      exact at77_mk hc rfl rfl rfl rfl rfl rfl rfl rfl hsi hcl hst
    · simp only [V, outer_mk rfl]
      omega
  case vc9 =>
    have h1 := (hyp% CondCode.nz.interp _ = false)
    have h2 := (hyp% CondCode.z.interp _ = false)
    bbu_norm at h1 h2
    rw [nz_res] at h1
    rw [z_res] at h2
    simp only [h2, Bool.not_false, Bool.true_eq_false] at h1

-- The flags of `.LB77` when the jumps to `.LB92` and `.LB81` are not taken.
set_option hygiene false in
local macro "far77" : tactic => `(tactic| (
  have hz1 := (hyp% CondCode.z.interp
    (StatusFlags.from_result (t.regs.r14.toBitVec - t.regs.rsi.toBitVec) _) = false)
  have hz2 := (hyp% CondCode.z.interp
    (StatusFlags.from_result (t.regs.r15.toBitVec + -1#64 - t.regs.rsi.toBitVec) _) = false)
  rw [Kit.z_sub, beq_eq_false_iff_ne] at hz1 hz2
  have hne : t.regs.rsi.toBitVec.toNat ≠ T := fun h => hz1 (BitVec.eq_of_toNat_eq (by omega))
  have hl1 : t.regs.rsi.toBitVec.toNat ≠ (st' s t).len - 1 := fun h =>
    hz2 (by rw [h15]; nrm; bv_omega)
  have hja := (hyp% CondCode.a.interp _ = _)
  rw [Kit.a_sub_imm _ 16 (by decide)] at hja
  simp only [decide_eq_true_eq, decide_eq_false_iff_not, Nat.not_lt] at hja
  have e : t.regs.r15.toBitVec - t.regs.rsi.toBitVec + -1#64
      = BitVec.ofNat 64 ((st' s t).len - t.regs.rsi.toBitVec.toNat - 1) := by
    rw [h15]; nrm; bv_omega
  rw [e, toNat_small (by nomega)] at hja
  nrm))

-- `.LB77`: swap the dests of `pos` and `sourceForTargetOffset`: `.LB92` if `pos` is
-- `targetOffset`, `.LB81` if `pos` is the top, `.LB108` if `pos` is out of reach, else
-- `swapWith pos` and `.LB81` (`.LB61` on an error).
theorem lb77 (hswap : Spec "swapWith" swapWithF swapWithA swapWithR) (hpre : Pre loopF loopA s) :
    OblAt s ra (.label ".LB77") := by
  loop_case
  intro t ht
  have h : At77 s ra t := ht
  obtain ⟨T, b, p, hc, hsi, hpl, hst⟩ := h
  obtain ⟨hl, hTl, hTn, hn⟩ := hc.bounds
  have hb := hc.1
  have hctx : Ctx s T (st' s t) := hc.2.2.2.2.2.2.2
  have hpos : Pos (env s).n (st' s t) := hctx.2.1.1.pos
  have hbl : b < (st' s t).len := hc.2.2.2.2.2.2.1
  have h15 : t.regs.r15.toBitVec = BitVec.ofNat 64 (st' s t).len := hc.2.1
  have h14 : t.regs.r14.toBitVec = BitVec.ofNat 64 T := hc.2.2.1
  have hr14 : t.regs.r14.toBitVec.toNat = T := by rw [h14]; exact toNat_small (by omega)
  have hax : t.regs.rax.toBitVec.toNat = b := by rw [hc.2.2.2.1]; exact toNat_small (by omega)
  have hsx : t.regs.rsi.toBitVec.toNat = p := by rw [hsi]; exact toNat_small (by omega)
  have hr8 : t.regs.r8.toBitVec = t.regs.rax.toBitVec * 8#64 := by
    rw [hc.2.2.2.2.2.1]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_mul, hax]; simp; omega
  have hops : (st' s t).trace.length < cap s := by
    obtain ⟨-, -, -, h⟩ := ctx_bounds hctx
    have : cap s = 6 * (env s).n := by
      show 6 * nOf s.dmem (rdi s) = 6 * (envOf s.dmem (rdi s)).n
      rw [n_envOf]
    omega
  have hfm := (hb.swap hpre hpos (hsx ▸ hpl) (hax ▸ hbl)).1
  subst hsx hax
  kvcgen64 [hswap]
  all_goals try bbu_norm at *
  all_goals nrm
  all_goals try simp only [hr8]
  all_goals try rw [swapMem_eq] at *
  case vc1 => exact hb.dest_isSome (by nomega)
  case vc2 => exact hb.dest_isSome (by nomega)
  case vc3 => exact hb.dest8_isSome (by nomega)
  case vc4 =>
    apply loadInt_isSome_store
    exact hb.dest_isSome (by nomega)
  case vc5 =>
    repeat apply loadInt_isSome_store
    exact hb.dest8_isSome (by nomega)
  case vc6 =>
    repeat apply loadInt_isSome_store
    exact hb.pos_isSome (hb.m2_lt hpre hpos (by nomega) (by nomega))
  case vc7 =>
    have hd := hb.dest (x := t.regs.rsi.toBitVec) (by nomega)
    have hd2 := Pos.dest_lt hpos (a := t.regs.rsi.toBitVec.toNat) (by nomega)
    nrm
    repeat apply loadInt_isSome_store
    exact hb.pos_isSome (by omega)
  case vc8 =>
    have hz := (hyp% CondCode.z.interp _ = true)
    rw [Kit.z_sub, beq_iff_eq] at hz
    have hpT : t.regs.rsi.toBitVec.toNat = T := by rw [← hz, hr14]
    loop_goto
    · exact stack_mk hb.rsp
    · exact at92_mk hpre hb hpos hpl hbl (by rw [hb.rbp]) rfl rfl (by rw [← hz]; exact h14)
        ⟨_, hctx, hst.trans (ap_self hpT)⟩
    · simp only [V]
      left
      rw [outer_swap (d := swapMem t.dmem t.regs.rbp.toBitVec t.regs.rsi.toBitVec.toNat
          t.regs.rax.toBitVec.toNat) hpre hb hpos hpl hbl (by rw [hb.rbp])]
      have h1 : (t.regs.rsi.toBitVec + 1#64).toNat = T + 1 := by bv_omega
      simp only [outer, W, h1, env]
      nomega
  case vc9 =>
    have hz1 := (hyp% CondCode.z.interp _ = false)
    have hz2 := (hyp% CondCode.z.interp _ = true)
    rw [Kit.z_sub, beq_eq_false_iff_ne] at hz1
    rw [Kit.z_sub, beq_iff_eq] at hz2
    have hne : t.regs.rsi.toBitVec.toNat ≠ T := fun h => hz1 (BitVec.eq_of_toNat_eq (by omega))
    have hl1 : t.regs.rsi.toBitVec.toNat = (st' s t).len - 1 := by
      rw [← hz2, h15]; nrm; bv_omega
    loop_goto
    · exact stack_mk hb.rsp
    · exact at81_mk hpre hb hpos hpl hbl (by rw [hb.rbp]) rfl rfl h14
        ⟨_, hctx, hst.trans (ap_top hne hl1)⟩ hops
    · left
      exact v81_swap (outer_swap (d := swapMem t.dmem t.regs.rbp.toBitVec t.regs.rsi.toBitVec.toNat
        t.regs.rax.toBitVec.toNat) hpre hb hpos hpl hbl (by rw [hb.rbp]) _)
  case vc10 =>
    far77
    have hf : MAX_SWAP_DEPTH < (st' s t).len - 1 - t.regs.rsi.toBitVec.toNat := by
      simp only [MAX_SWAP_DEPTH]; nomega
    loop_goto
    · exact stack_mk hb.rsp
    · refine at108_far (base_swap hpre hb hpos hpl hbl (by rw [hb.rbp]) rfl rfl).1 hsi ?_
        (iter_err ⟨_, hctx, hst.trans (ap_far hne hl1 hf)⟩)
      dsimp only
      rw [h15]; simp only [MAX_SWAP_DEPTH]; nrm; bv_omega
    · simp only [V]; omega
  case vc11 =>
    rw [hb.rbp, hb.rsp]
    exact Kit.Mid.call_isSome (k := 80) (by decide) hpre hfm.toMid
  case vc12 => exact swap_pre_mk hpre hb hpos hpl hbl (by rw [hb.rbp]) rfl rfl hops
  all_goals
    rename_i t' af hnz _ _ hP hag
    simp only [hr8] at hP hag
    rw [swapMem_eq] at hP hag
    far77
    have hf : (st' s t).len - 1 - t.regs.rsi.toBitVec.toNat ≤ MAX_SWAP_DEPTH := by
      simp only [MAX_SWAP_DEPTH]; nomega
    have hst' := hst.trans (ap_swap hne hl1 hf)
    obtain ⟨hB, h14', hg⟩ := swap_call_mk hpre hb hpos hpl hbl hP hag
      (by rw [hb.rbp]) rfl rfl rfl rfl rfl
    clear hP hag
    nrm
  case vc13 =>
    rw [nz_and, Bool.not_eq_true', beq_eq_false_iff_ne] at hnz
    loop_goto
    · exact stack_mk hB.rsp
    · exact at61_err hB (fun e he => iter_err ⟨_, hctx, hst'.trans (by rw [he]; rfl)⟩) hg
        (fun _ h => h.1) hnz
    · left; rw [v61]; simp only [V]; omega
  all_goals
    rw [nz_and, Bool.not_eq_false', beq_iff_eq] at hnz
    obtain ⟨q, hq, -, hq'⟩ := res_ok_of_msb hg (by rw [show rax t' = 0#64 from hnz]; rfl)
  case vc14 =>
    obtain ⟨-, -, -, h⟩ := ctx_bounds hctx
    have : cap s = 6 * (env s).n := by
      show 6 * nOf s.dmem (rdi s) = 6 * (envOf s.dmem (rdi s)).n
      rw [n_envOf]
    exact at81_call hB (by rw [h14']; exact h14) hq' ⟨_, hctx, hst'.trans (by rw [hq]; rfl)⟩
      (by rw [(swapWith_shape hq).2.1, (swapDest_shape _ _ _).2.1]; nomega)
      (Pos.swapWith (Pos.swapDest hpos hpl hbl) hq)
  case vc15 =>
    have hpd : (st' s t').pendingGenerations = (st' s t).pendingGenerations := by
      nrm
      rw [hq', (swapWith_shape hq).2.2, (swapDest_shape _ _ _).2.2]
    left
    exact v81_call (outer_call hpd _) h14'

end Loop

end Bbu
