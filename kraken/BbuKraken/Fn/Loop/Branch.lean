import BbuKraken.Fn.Loop.Machine
import BbuKraken.Fn.Loop.Model

/-!
The branch of `buildBottomUp` on the result of the scan: `.LB106` (an urgent slot in
reach goes to `.LB108`), `.LB108` (`generate` of the urgent slot) and `.LB71` (`generate`
of the slot `len` if no slot is bound to it).
-/

open Std.WP Lean.Order
open scoped Program.WP

namespace Bbu

namespace Loop

set_option experimental.vcgen true

/-! ## After `generate` -/

section
variable {s : MachineData} {ra : Int64} {T d : Nat} {st0 : St} {t u : MachineData}

-- A failed `generate` at a loop head gives `.LB65`.
private theorem gen_err (hb : Base s ra t) (hctx : Ctx s T st0)
    (hstep : step (env s) st0 T = (generate (env s) st0 d).map (·, .next T))
    (hg : Res (rdi s) (generate (env s) st0 d) (fun r => rax t = 0#64 ∧ st' s t = r) t)
    (hnz : rax t ≠ 0#64) (hm : u.dmem = t.dmem) (hsp : u.regs.rsp = t.regs.rsp)
    (hax : rax u = rax t) : At65 s ra u := by
  cases hr : generate (env s) st0 d with
  | ok r => rw [hr] at hg; exact absurd hg.1 hnz
  | error e =>
    rw [hr] at hg
    have he := iter_err (s := s) ⟨st0, hctx, by rw [hstep, hr]; rfl⟩
    refine ⟨hm ▸ hb.fm, hsp ▸ hb.rsp, ?_⟩
    unfold loopR
    rw [show loop (env s) (st s) 0 = R0 s from rfl, he]
    cases e with
    | blocked p x =>
      show rax u = _ ∧ _
      rw [hax, hm]; exact hg
    | assertion =>
      show rax u = _
      rw [hax]; exact hg

-- A `generate` that returns at a loop head gives `.LB68` with the same `T`.
private theorem gen_ok (hb : Base s ra u) (hctx : Ctx s T st0) (hpd : st0.pendingGenerations ≠ 0)
    (hstep : step (env s) st0 T = (generate (env s) st0 d).map (·, .next T))
    (hg : Res (rdi s) (generate (env s) st0 d) (fun r => rax t = 0#64 ∧ st' s t = r) t)
    (hz : rax t = 0#64) (hm : u.dmem = t.dmem)
    (h14 : u.regs.r14.toBitVec + 1#64 = BitVec.ofNat 64 T) :
    At68 s ra u ∧ (st' s u).pendingGenerations + 1 = st0.pendingGenerations := by
  obtain ⟨r, hr, -, hst⟩ := res_ok_of_msb hg (by rw [hz]; rfl)
  have hit := iter_next (s := s) ⟨st0, hctx, by rw [hstep, hr]; rfl⟩
  have hsu : st' s u = r := by simp only [st', hm]; exact hst
  refine ⟨⟨hb, T, h14, hsu ▸ hit.1, hsu ▸ hit.2⟩, ?_⟩
  rw [hsu, (generate_shape hr).2.2]
  omega


-- The zero flag of `test v, v`.
private theorem nz_test (v : Word) (r : StatusFlags.from_result.Remaining) :
    CondCode.nz.interp (StatusFlags.from_result (v &&& v) r) = !(v == 0) := by
  simp [CondCode.interp, StatusFlags.from_result]

-- The precondition of `generate` at a loop head.
private theorem gen_pre {c : MachineData} (hpre : Pre loopF loopA s) (hb : Base s ra t)
    (hctx : Ctx s T (st' s t)) (hpd : (st' s t).pendingGenerations ≠ 0) (hc : c.dmem = t.dmem)
    (hdi : rdi c = rdi s) : generateA c := by
  unfold generateA
  rw [st_call hc hdi, cap_call hpre hb hc hdi]
  have h := ctx_genA hctx hpd
  rw [env, n_envOf] at h
  exact h

-- `generate d` with `d` in `rsi`.
private theorem gen_post {c t' : MachineData} (hpre : Pre loopF loopA s) (hb : Base s ra t)
    (hp : Post generateF generateR c t') (hc : c.dmem = t.dmem) (hdi : rdi c = rdi s)
    (hsi : rsi c = BitVec.ofNat 64 d) (hd : d ≤ 1024) :
    Res (rdi s) (generate (env s) (st' s t) d) (fun r => rax t' = 0#64 ∧ st' s t' = r) t' := by
  have h := generate_post hpre hb hp hc hdi
  rwa [hsi, toNat_small (by omega)] at h
-- The variant from `.LB108` or `.LB71` to `.LB68`.
private theorem v_gen {k : Nat}
    (h1 : (u.regs.r14.toBitVec + 1#64).toNat = T) (h2 : t.regs.r14.toBitVec.toNat = T)
    (hp : (st' s u).pendingGenerations + 1 = (st' s t).pendingGenerations) :
    W * outer s u (u.regs.r14.toBitVec + 1#64).toNat + 8100
      < W * outer s t t.regs.r14.toBitVec.toNat + k := by
  rw [h1, h2]
  simp only [outer, W]
  omega

/-! ## `.LB71` -/

-- `setb; setb; testb; je`: the zero flag of the `and` of two borrows.
private theorem z_setb2 (a b c d : Word) (af af1 of1 af2 of2 : Bool) :
    CondCode.z.interp (StatusFlags.from_result
      (BitVec.ofNat 8 (CondCode.c.interp (StatusFlags.from_result (a - b)
          { cf := (((a - b).toNat : Int) != (a.toNat : Int) - (b.toNat : Int)),
            af := af1, of := of1 })).toNat &&&
        BitVec.ofNat 8 (CondCode.c.interp (StatusFlags.from_result (c - d)
          { cf := (((c - d).toNat : Int) != (c.toNat : Int) - (d.toNat : Int)),
            af := af2, of := of2 })).toNat)
      { cf := false, af := af, of := false })
      = !(decide (a.toNat < b.toNat) && decide (c.toNat < d.toNat)) := by
  have e1 : (((a - b).toNat : Int) != (a.toNat : Int) - (b.toNat : Int))
      = decide (a.toNat < b.toNat) := by rw [Bool.eq_iff_iff, Kit.cf_sub, decide_eq_true_iff]
  have e2 : (((c - d).toNat : Int) != (c.toNat : Int) - (d.toNat : Int))
      = decide (c.toNat < d.toNat) := by rw [Bool.eq_iff_iff, Kit.cf_sub, decide_eq_true_iff]
  simp only [CondCode.interp_c, StatusFlags.cf_from_result, e1, e2]
  cases decide (a.toNat < b.toNat) <;> cases decide (c.toNat < d.toNat) <;> rfl

-- `encOpt` is `-1` only for none.
private theorem encOpt_m1 {o : Option Nat} (h : ∀ b, o = some b → b ≤ 1024) :
    encOpt o = -1#64 ↔ o = none := by
  cases o with
  | none => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | some b =>
    refine ⟨fun hb => ?_, fun h => nomatch h⟩
    have := h b rfl
    rw [encOpt, show (-1#64 : Word) = BitVec.ofNat 64 (2 ^ 64 - 1) by decide] at hb
    exact absurd (ofNat_inj64 (by omega) (by decide) hb) (by omega)

-- `positionOf d` with `d` in `rsi`.
private theorem pos_post {c t' : MachineData} (hp : Post positionOfF positionOfR c t')
    (hc : c.dmem = t.dmem) (hdi : rdi c = rdi s) (hsi : rsi c = BitVec.ofNat 64 d) (hd : d ≤ 1024) :
    t'.regs.rax.toBitVec = encOpt (positionOf (st' s t) d) ∧ st' s t' = st' s t := by
  have h := positionOf_post hp hc hdi
  rwa [hsi, toNat_small (by omega)] at h

-- `.LB71` goes to `.LB77` if the second branch of `afterUrgent` is not taken.
private theorem at77_of (hb : Base s ra u)
    (h15 : u.regs.r15.toBitVec = BitVec.ofNat 64 (st' s t).len)
    (h14 : u.regs.r14.toBitVec = BitVec.ofNat 64 T) (hst : st' s u = st' s t)
    (hctx : Ctx s T (st' s t)) (hpd : (st' s t).pendingGenerations ≠ 0) (hd : d = (env s).n ∨ d = T)
    (hstep : step (env s) (st' s t) T = afterUrgent (env s) (st' s t) T d)
    (h2 : ¬ (d = (env s).n ∧ T < (st' s t).len ∧ (st' s t).len < (env s).n
      ∧ positionOf (st' s t) (st' s t).len = none ∧ (st' s t).len < T + MAX_SWAP_DEPTH)) :
    At77 s ra u := by
  refine ⟨hb, by rw [hst]; exact h15, T, h14, by rw [hst]; exact hctx, by rw [hst]; exact hpd, ?_⟩
  rw [hst, hstep, au_bound (fun h => hd.elim h.1 h.2.1) h2]

-- The variant from `.LB71` to `.LB77`.
private theorem v77 (h14 : u.regs.r14.toBitVec = t.regs.r14.toBitVec) (hst : st' s u = st' s t) :
    W * outer s u u.regs.r14.toBitVec.toNat + 2700 < W * outer s t t.regs.r14.toBitVec.toNat + 2800 := by
  unfold outer
  rw [h14, hst]
  omega

end

variable [Host] [FunDecls] {s : MachineData} {ra : Int64}

-- `.LB71` if `u` is none or `T`; `.LB108` if `len - T ≤ 15`; else `.LB77`.
theorem lb106 (hpre : Pre loopF loopA s) : OblAt s ra (.label ".LB106") := by
  loop_case
  intro t ht
  obtain ⟨hb, h13, h15, T, u, h14, hslot, hun, hctx, hpd, hstep⟩ : At106 s ra t := ht
  obtain ⟨hlp, hnN, hTl, -⟩ := ctx_bounds hctx
  have hn : (env s).n ≤ 1024 := hnN
  have hrd : rd t.dmem (t.regs.rsp.toBitVec + 8#64) = encU (env s).n u := by
    rw [hb.rsp, show rsp s - 80#64 + 8#64 = rsp s - 72#64 by bv_omega]; exact hslot
  have hm1 : (18446744073709551615#64 : Word) = -1#64 := by decide
  kvcgen64
  case vc1 =>
    bbu_norm
    refine Mem.Mapped.loadInt_isSome hb.fm.map (Or.inl ?_)
    rw [hb.rsp, show rsp s - 80#64 + 8#64 = rsp s - 72#64 by bv_omega]
    exact (slot_in hpre).elim id False.elim
  case vc2 =>
    rename_i hz
    bbu_norm at hz ⊢
    rw [Kit.z_sub, hrd, hm1, beq_iff_eq, encU_m1 hn hun] at hz
    loop_goto
    · exact stack_of hb.rsp
    · show At71 s ra _
      exact ⟨⟨hb.fm, hb.rsp, hb.rbp⟩, h13, h15, T, u, h14, hslot, hun, Or.inl hz, hctx, hpd, hstep⟩
    · simp only [V, outer, st']
      omega
  case vc3 =>
    rename_i hz1 hz
    bbu_norm at hz1 hz ⊢
    rw [Kit.z_sub, hrd, h14, beq_iff_eq] at hz
    have hu : u = (env s).n ∨ u = T := by
      by_cases h : u = (env s).n
      · exact Or.inl h
      · refine Or.inr (ofNat_inj64 (by omega) (by omega) ?_)
        rw [← hz, encU, ite_eq_right h]
    loop_goto
    · exact stack_of hb.rsp
    · show At71 s ra _
      exact ⟨⟨hb.fm, hb.rsp, hb.rbp⟩, h13, h15, T, u, h14, hslot, hun, hu, hctx, hpd, hstep⟩
    · simp only [V, outer, st']
      omega
  case vc4 =>
    rename_i hz1 hz2 hbe
    bbu_norm at hz1 hz2 hbe ⊢
    rw [Kit.z_sub, hrd, hm1, beq_eq_false_iff_ne, ne_eq, encU_m1 hn hun] at hz1
    have hu : encU (env s).n u = BitVec.ofNat 64 u := by rw [encU, ite_eq_right hz1]
    rw [Kit.z_sub, hrd, h14, hu, beq_eq_false_iff_ne, ne_eq] at hz2
    have hut : u ≠ T := fun h => hz2 (by rw [h])
    rw [Kit.be_sub_imm _ _ (by decide), decide_eq_true_eq, h15, h14, sub_of hTl,
      toNat_small (by omega)] at hbe
    loop_goto
    · exact stack_of hb.rsp
    · show At108 s ra _
      refine ⟨⟨hb.fm, hb.rsp, hb.rbp⟩, T, u, h14, hslot.trans hu, Nat.lt_of_le_of_ne hun hz1, hctx, hpd, ?_⟩
      rw [hstep, au_gen ⟨hz1, hut, by simp only [MAX_SWAP_DEPTH]; omega⟩]
    · simp only [V, outer, st']
      omega
  case vc5 =>
    rename_i hz1 hz2 hbe
    bbu_norm at hz1 hz2 hbe ⊢
    rw [Kit.z_sub, hrd, hm1, beq_eq_false_iff_ne, ne_eq, encU_m1 hn hun] at hz1
    rw [Kit.be_sub_imm _ _ (by decide), decide_eq_false_iff_not, h15, h14, sub_of hTl,
      toNat_small (by omega)] at hbe
    show At77 s ra _
    refine ⟨⟨hb.fm, hb.rsp, hb.rbp⟩, h15, T, h14, hctx, hpd, ?_⟩
    rw [hstep, au_bound (fun h => by simp only [MAX_SWAP_DEPTH] at h; omega) (fun h => hz1 h.1)]
  case vc6 =>
    simp only [V, outer, st']
    omega

-- `generate u`; `.LB65` on an error, else `.LB68` with the same `T`.
theorem lb108 (hgen : Spec "generate" generateF generateA generateR)
    (hpre : Pre loopF loopA s) : OblAt s ra (.label ".LB108") := by
  loop_case
  intro t ht
  obtain ⟨hb, T, u, h14, hslot, hun, hctx, hpd, hstep⟩ : At108 s ra t := ht
  obtain ⟨hlp, hnN, hTl, -⟩ := ctx_bounds hctx
  have hn : (env s).n ≤ 1024 := hnN
  have hrd : rd t.dmem (t.regs.rsp.toBitVec + 8#64) = BitVec.ofNat 64 u := by
    rw [hb.rsp, show rsp s - 80#64 + 8#64 = rsp s - 72#64 by bv_omega]; exact hslot
  kvcgen64 [hgen]
  all_goals clear hgen
  case vc1 =>
    bbu_norm
    refine Mem.Mapped.loadInt_isSome hb.fm.map (Or.inl ?_)
    rw [hb.rsp, show rsp s - 80#64 + 8#64 = rsp s - 72#64 by bv_omega]
    exact (slot_in hpre).elim id False.elim
  case vc2 =>
    bbu_norm
    rw [hb.rsp]
    exact Kit.Mid.call_isSome (k := 80) (by decide) hpre hb.fm.toMid
  case vc3 =>
    refine Kit.Fm.pre (k := 80) (by decide) hpre hb.fm rfl hb.rsp hb.rbp ?_
    apply gen_pre hpre hb hctx hpd
    · rfl
    · exact hb.rbp
  case vc4 =>
    rename_i t' hp hag af hnz
    have hb' := Base.call (by decide) hpre hb hp hag rfl rfl hb.rbp rfl
    have hg := gen_post (d := u) hpre hb hp rfl hb.rbp (by bbu_norm; exact hrd) (by omega)
    bbu_norm at hnz
    rw [nz_test, Bool.not_eq_true', beq_eq_false_iff_ne] at hnz
    loop_goto
    · exact stack_of hb'.rsp
    · show At65 s ra _
      exact gen_err hb' hctx hstep hg hnz rfl rfl rfl
    · simp [V]
  case vc5 =>
    rename_i t' hp hag af hnz
    have hb' := Base.call (by decide) hpre hb hp hag rfl rfl hb.rbp rfl
    have hg := gen_post (d := u) hpre hb hp rfl hb.rbp (by bbu_norm; exact hrd) (by omega)
    have h14' := (call_regs hag).2.2.2.1
    bbu_norm at hnz
    rw [nz_test, Bool.not_eq_false', beq_iff_eq] at hnz
    have hT : t.regs.r14.toBitVec.toNat = T := by rw [h14, toNat_small (by omega)]
    have e14 : t'.regs.r14.toBitVec - 1#64 + 1#64 = BitVec.ofNat 64 T := by
      rw [BitVec.sub_add_cancel, h14']; exact h14
    loop_goto
    · exact stack_of hb'.rsp
    · show At68 s ra _
      refine (gen_ok (u := _) ?_ hctx hpd hstep hg hnz ?_ ?_).1
      · exact ⟨hb'.fm, hb'.rsp, hb'.rbp⟩
      · rfl
      · exact e14
    · simp only [V]
      refine Or.inl (v_gen (k := 2850) ?_ hT ?_)
      · show (t'.regs.r14.toBitVec - 1#64 + 1#64).toNat = T
        rw [e14, toNat_small (by omega)]
      · refine (gen_ok (ra := ra) (u := _) ?_ hctx hpd hstep hg hnz ?_ ?_).2
        · exact ⟨hb'.fm, hb'.rsp, hb'.rbp⟩
        · rfl
        · exact e14

-- The facts after `positionOf` in `.LB71`.
set_option hygiene false in
local macro "pos_setup" : tactic => `(tactic| (
  have hb1 := Base.call (by decide) hpre hb hp1 hag1 rfl rfl hb.rbp rfl
  have hpo := pos_post hp1 rfl hb.rbp h15 (by omega)
  obtain ⟨-, -, -, h14', h15'⟩ := call_regs hag1
  have f14 : t1.regs.r14.toBitVec = t.regs.r14.toBitVec := by rw [h14']
  have f15 : t1.regs.r15.toBitVec = t.regs.r15.toBitVec := by rw [h15']
  bbu_norm at hz hne hnz
  clear hp1 hag1 h14' h15'))

-- If `T < len < n`, `len - T ≤ 15` and no slot is bound to `len`: `generate len` and
-- `.LB68` with the same `T`. Else `.LB77`.
theorem lb71 (hpos : Spec "positionOf" positionOfF positionOfA positionOfR)
    (hgen : Spec "generate" generateF generateA generateR)
    (hpre : Pre loopF loopA s) : OblAt s ra (.label ".LB71") := by
  loop_case
  intro t ht
  obtain ⟨hb, h13, h15, T, u, h14, hslot, hun, hu, hctx, hpd, hstep⟩ : At71 s ra t := ht
  obtain ⟨hlp, hnN, hTl, -⟩ := ctx_bounds hctx
  have hn : (env s).n ≤ 1024 := hnN
  have hrd : rd t.dmem (t.regs.rsp.toBitVec + 8#64) = encU (env s).n u := by
    rw [hb.rsp, show rsp s - 80#64 + 8#64 = rsp s - 72#64 by bv_omega]; exact hslot
  have hm1 : (18446744073709551615#64 : Word) = -1#64 := by decide
  have e13 : t.regs.r13.toBitVec.toNat = (env s).n := by rw [h13, toNat_small (by omega)]
  have e14 : t.regs.r14.toBitVec.toNat = T := by rw [h14, toNat_small (by omega)]
  have e15 : t.regs.r15.toBitVec.toNat = (st' s t).len := by rw [h15, toNat_small (by omega)]
  have hpn : ∀ b, positionOf (st' s t) (st' s t).len = some b → b ≤ 1024 :=
    fun b h => by have := positionOf_some h; omega
  have hL : (st' s t).len ≤ 1024 := by omega
  have hLT : (st' s t).len - T < 2 ^ 64 := by omega
  kvcgen64 [hpos, hgen]
  all_goals clear hpos hgen
  case vc1 =>
    rename_i af hz
    bbu_norm at hz
    rw [z_setb2, e14, e15, e13] at hz
    simp only [Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not] at hz
    loop_goto
    · exact stack_of hb.rsp
    · show At77 s ra _
      exact at77_of ⟨hb.fm, hb.rsp, hb.rbp⟩ h15 h14 rfl hctx hpd hu hstep
        (fun h => hz.elim (· h.2.1) (· h.2.2.1))
    · simp only [V, outer, st']
      omega
  case vc2 =>
    bbu_norm
    refine Mem.Mapped.loadInt_isSome hb.fm.map (Or.inl ?_)
    rw [hb.rsp, show rsp s - 80#64 + 8#64 = rsp s - 72#64 by bv_omega]
    exact (slot_in hpre).elim id False.elim
  case vc3 =>
    rename_i af hz hne
    bbu_norm at hne
    rw [Kit.nz_sub, hrd, hm1, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq, encU_m1 hn hun] at hne
    loop_goto
    · exact stack_of hb.rsp
    · show At77 s ra _
      exact at77_of ⟨hb.fm, hb.rsp, hb.rbp⟩ h15 h14 rfl hctx hpd hu hstep (fun h => hne h.1)
    · simp only [V, outer, st']
      omega
  case vc4 =>
    bbu_norm
    rw [hb.rsp]
    exact Kit.Mid.call_isSome (k := 80) (by decide) hpre hb.fm.toMid
  case vc5 => exact Kit.Fm.pre (k := 80) (by decide) hpre hb.fm rfl hb.rsp hb.rbp trivial
  case vc6 =>
    rename_i af hz hne t1 hp1 hag1 hnz
    pos_setup
    rw [Kit.nz_sub, hpo.1, hm1, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq, encOpt_m1 hpn] at hnz
    loop_goto
    · exact stack_of hb1.rsp
    · show At77 s ra _
      exact at77_of ⟨hb1.fm, hb1.rsp, hb1.rbp⟩ (f15.trans h15) (f14.trans h14) hpo.2 hctx hpd hu
        hstep (fun h => hnz h.2.2.2.1)
    · simp only [V]
      exact Or.inl (v77 f14 hpo.2)
  case vc7 =>
    rename_i af hz hne t1 hp1 hag1 hnz hja
    pos_setup
    bbu_norm at hja
    rw [Kit.a_sub_imm _ _ (by decide), decide_eq_true_eq, f15, f14, h15, h14, sub_of hTl,
      toNat_small hLT] at hja
    loop_goto
    · exact stack_of hb1.rsp
    · show At77 s ra _
      exact at77_of ⟨hb1.fm, hb1.rsp, hb1.rbp⟩ (f15.trans h15) (f14.trans h14) hpo.2 hctx hpd hu
        hstep (fun h => by
          have := h.2.2.2.2; have hja' : 15 < (st' s t).len - T := hja
          simp only [MAX_SWAP_DEPTH] at this; omega)
    · simp only [V]
      exact Or.inl (v77 f14 hpo.2)
  case vc8 =>
    rename_i af hz hne t1 hp1 hag1 hnz hja
    pos_setup
    bbu_norm
    rw [hb1.rsp]
    exact Kit.Mid.call_isSome (k := 80) (by decide) hpre hb1.fm.toMid
  case vc9 =>
    rename_i af hz hne t1 hp1 hag1 hnz hja
    pos_setup
    refine Kit.Fm.pre (k := 80) (by decide) hpre hb1.fm rfl hb1.rsp hb1.rbp ?_
    apply gen_pre hpre hb1 (by rw [hpo.2]; exact hctx) (by rw [hpo.2]; exact hpd)
    · rfl
    · exact hb1.rbp
  all_goals
    rename_i af hz hne t1 hp1 hag1 hnz hja t2 hp2 hag2 af2 hnz2
    pos_setup
    bbu_norm at hja hnz2
    rw [z_setb2, e14, e15, e13] at hz
    simp only [Bool.not_eq_false', Bool.and_eq_true, decide_eq_true_eq] at hz
    rw [Kit.nz_sub, hrd, hm1, Bool.not_eq_false', beq_iff_eq, encU_m1 hn hun] at hne
    rw [Kit.nz_sub, hpo.1, hm1, Bool.not_eq_false', beq_iff_eq, encOpt_m1 hpn] at hnz
    rw [Kit.a_sub_imm _ _ (by decide), decide_eq_false_iff_not, f15, f14, h15, h14, sub_of hTl,
      toNat_small hLT] at hja
    have hstep' := hstep.trans
      (au_top ⟨hne, hz.1, hz.2, hnz, by
        have hja' : ¬ 15 < (st' s t).len - T := hja; simp only [MAX_SWAP_DEPTH]; omega⟩)
    have hb2 := Base.call (by decide) hpre hb1 hp2 hag2 rfl rfl hb1.rbp rfl
    have hg := gen_post (d := (st' s t).len) hpre hb1 hp2 rfl hb1.rbp
      (by show t1.regs.r15.toBitVec = _; rw [f15]; exact h15) hL
    rw [hpo.2] at hg
    have h14'' := (call_regs hag2).2.2.2.1
    clear hp2 hag2
  case vc10 =>
    rw [nz_test, Bool.not_eq_true', beq_eq_false_iff_ne] at hnz2
    loop_goto
    · exact stack_of hb2.rsp
    · show At65 s ra _
      exact gen_err hb2 hctx hstep' hg hnz2 rfl rfl rfl
    · simp [V]
  case vc11 =>
    rw [nz_test, Bool.not_eq_false', beq_iff_eq] at hnz2
    have e14' : t2.regs.r14.toBitVec - 1#64 + 1#64 = BitVec.ofNat 64 T := by
      rw [BitVec.sub_add_cancel, h14'']; exact f14.trans h14
    loop_goto
    · exact stack_of hb2.rsp
    · show At68 s ra _
      refine (gen_ok (u := _) ?_ hctx hpd hstep' hg hnz2 ?_ ?_).1
      · exact ⟨hb2.fm, hb2.rsp, hb2.rbp⟩
      · rfl
      · exact e14'
    · simp only [V]
      refine Or.inl (v_gen (k := 2800) ?_ e14 ?_)
      · show (t2.regs.r14.toBitVec - 1#64 + 1#64).toNat = T
        rw [e14', toNat_small (by omega)]
      · refine (gen_ok (ra := ra) (u := _) ?_ hctx hpd hstep' hg hnz2 ?_ ?_).2
        · exact ⟨hb2.fm, hb2.rsp, hb2.rbp⟩
        · rfl
        · exact e14'

end Loop

end Bbu
