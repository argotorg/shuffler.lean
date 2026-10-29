import BbuKraken.Fn.Loop.Machine
import BbuKraken.Fn.Loop.Model

/-!
The end of an iteration of `buildBottomUp`: `.LB75` (`generate T`), `.LB81` and `.LB83`
(`placeTop`: swap the top into `T`).
-/

open Std.WP Lean.Order
open scoped Program.WP

namespace Bbu

namespace Loop

section
variable {s : MachineData} {ra : Int64} {t : MachineData}

private theorem n_le' (hpre : Pre loopF loopA s) (hb : Base s ra t) : (env s).n ≤ 1024 := by
  rw [show (env s).n = nOf s.dmem (rdi s) from n_envOf, ← hb.fm.n hpre]
  exact hb.fm.wf.n_le

private theorem len_le' (hb : Base s ra t) : (st' s t).len ≤ 1024 := by
  rw [len_stOf]; exact Nat.le_trans hb.fm.wf.len_le hb.fm.wf.n_le

-- The word `len`.
private theorem rd_len (hb : Base s ra t) :
    rd t.dmem t.regs.rbp.toBitVec = BitVec.ofNat 64 (st' s t).len := by
  rw [len_stOf, BitVec.ofNat_toNat, BitVec.setWidth_eq, hb.rbp]
  simp [wordAt]

private theorem iter_lt {T : Nat} {r : M (St × Next)} (h : Iter s T r) : T < (env s).n := by
  obtain ⟨_, ⟨hT, -⟩, -⟩ := h
  exact hT

-- The word of `dest[i]`.
private theorem dest_addr (a w : Word) : a + w * 8#64 + 72#64 = wordAt a (DEST + w.toNat) := by
  simp only [wordAt, DEST_eq]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
  omega

private theorem r14_succ {T : Nat} (hT : t.regs.r14.toBitVec = BitVec.ofNat 64 T)
    (h : T + 1 < 2 ^ 64) : (t.regs.r14.toBitVec + 1#64).toNat = T + 1 := by
  rw [hT, ← BitVec.ofNat_add, toNat_small h]

/- The lemmas below take a state literal as `MachineData.mk r z f d`. The kernel then
compares the fields one by one and does not unfold the bit-vector terms. -/

private theorem rdi_mk {r : Reg64s} {z f d} (hb : Base s ra t)
    (h : r.rdi.toBitVec = t.regs.rbp.toBitVec) : rdi (MachineData.mk r z f d) = rdi s := by
  simp only [rdi, Reg64s.get64_rdi]
  rw [h]
  exact hb.rbp

private theorem swap_pre {c : MachineData} (hpre : Pre loopF loopA s) (hb : Base s ra t)
    (hpos : Pos (env s).n (st' s t)) (hops : (st' s t).trace.length < cap s)
    (hc : c.dmem = t.dmem) (hdi : rdi c = rdi s) : swapWithA c := by
  unfold swapWithA
  rw [st_call hc hdi, cap_call hpre hb hc hdi, env_call hpre hb hc hdi]
  exact ⟨hpos, hops⟩

private theorem swap_pre_mk {r : Reg64s} {z f} (hpre : Pre loopF loopA s) (hb : Base s ra t)
    (hpos : Pos (env s).n (st' s t)) (hops : (st' s t).trace.length < cap s)
    (hsp : r.rsp = t.regs.rsp) (hdi : r.rdi.toBitVec = t.regs.rbp.toBitVec) :
    Pre swapWithF swapWithA (MachineData.mk r z f t.dmem) := by
  have hd := rdi_mk (z := z) (f := f) (d := t.dmem) hb hdi
  refine Kit.Fm.pre (k := 80) (by decide) hpre hb.fm rfl ?_ hd (swap_pre hpre hb hpos hops rfl hd)
  simp only [rsp, Reg64s.get64_rsp]
  rw [hsp]
  exact hb.rsp

-- The call of `swapWith`.
private theorem swap_call {t' : MachineData} {r : Reg64s} {z f}
    (hpre : Pre loopF loopA s) (hb : Base s ra t)
    (hp : Post swapWithF swapWithR (MachineData.mk r z f t.dmem) t')
    (hag : (mod swapWithF (MachineData.mk r z f t.dmem)).Agree (MachineData.mk r z f t.dmem) t')
    (hsp : r.rsp = t.regs.rsp) (hbp : r.rbp = t.regs.rbp)
    (hdi : r.rdi.toBitVec = t.regs.rbp.toBitVec) (hsi : r.rsi.toBitVec = t.regs.r14.toBitVec)
    (h14 : r.r14 = t.regs.r14) :
    Base s ra t' ∧ t'.regs.r14 = t.regs.r14
      ∧ Res (rdi s) (swapWith (st' s t) t.regs.r14.toBitVec.toNat)
          (fun q => rax t' = 0#64 ∧ st' s t' = q) t' := by
  have hd := rdi_mk (z := z) (f := f) (d := t.dmem) hb hdi
  refine ⟨Base.call (by decide) hpre hb hp hag rfl hsp hd hbp,
    (call_regs hag).2.2.2.1.trans h14, ?_⟩
  have h := swapWith_post hp rfl hd
  simp only [rsi, Reg64s.get64_rsi] at h
  rwa [hsi] at h

private theorem at64_mk {r : Reg64s} {z f} {T' : Nat} (hb : Base s ra t)
    (hsp : r.rsp = t.regs.rsp) (hbp : r.rbp = t.regs.rbp) (h14 : r.r14 = t.regs.r14)
    (hT : t.regs.r14.toBitVec + 1#64 = BitVec.ofNat 64 T')
    (hi : InvL (env s) (st' s t) T' ∧ loop (env s) (st' s t) T' = R0 s) :
    At64 s ra (MachineData.mk r z f t.dmem) :=
  ⟨⟨hb.fm, by rw [hsp]; exact hb.rsp, by rw [hbp]; exact hb.rbp⟩, T',
    by rw [h14]; exact hT, hi⟩

private theorem at109_mk {r : Reg64s} {z f} {c k : Nat} (hb : Base s ra t)
    (hsp : r.rsp = t.regs.rsp) (hbp : r.rbp = t.regs.rbp) (h14 : r.r14 = t.regs.r14)
    (hc : t.regs.r14.toBitVec = BitVec.ofNat 64 c) (hk : r.rax.toBitVec - 17#64 = BitVec.ofNat 64 k)
    (hR : R0 s = .error (.blocked c k)) : At109 s ra (MachineData.mk r z f t.dmem) :=
  ⟨⟨hb.fm, by rw [hsp]; exact hb.rsp, by rw [hbp]; exact hb.rbp⟩, c, k, by rw [h14]; exact hc,
    hk, hR⟩

-- The variant at `.LB64` after the slot `T`.
private theorem v64_lt {r : Reg64s} {z f d} {T : Nat} (hT : T < (env s).n)
    (h14 : r.r14 = t.regs.r14) (hu : (t.regs.r14.toBitVec + 1#64).toNat = T + 1)
    (ht : t.regs.r14.toBitVec.toNat = T)
    (hp : (stOf d (rdi s)).pendingGenerations ≤ (stOf t.dmem (rdi s)).pendingGenerations) :
    V s ".LB64" (MachineData.mk r z f d) < W * outer s t t.regs.r14.toBitVec.toNat := by
  simp only [V, outer, W, st']
  rw [h14, hu, ht]
  omega

private theorem v61 {u : MachineData} : V s ".LB61" u = 0 := by
  simp [V]

-- An error of a callee gives `.LB61`.
private theorem at61_of {α : Type} {r : M α} {Q : α → Prop} {t' : MachineData} {z f}
    (hb : Base s ra t') (hR : ∀ e, r = .error e → R0 s = .error e) (h : Res (rdi s) r Q t')
    (hok : ∀ a, Q a → rax t' = 0#64) (hne : rax t' ≠ 0#64) :
    At61 s ra (MachineData.mk t'.regs z f t'.dmem) := by
  cases r with
  | ok a => exact absurd (hok a h) hne
  | error e =>
    refine ⟨hb.fm, hb.rsp, ?_⟩
    unfold loopR
    rw [show loop (env s) (st s) 0 = R0 s from rfl, hR e rfl]
    cases e <;> exact h


private theorem cap_n : cap s = 6 * (env s).n := by
  show 6 * nOf s.dmem (rdi s) = 6 * (envOf s.dmem (rdi s)).n
  rw [n_envOf]

private theorem gen_pre_mk {r : Reg64s} {z f} {T : Nat} (hpre : Pre loopF loopA s)
    (hb : Base s ra t) (hctx : Ctx s T (st' s t)) (hpd : (st' s t).pendingGenerations ≠ 0)
    (hsp : r.rsp = t.regs.rsp) (hdi : r.rdi.toBitVec = t.regs.rbp.toBitVec) :
    Pre generateF generateA (MachineData.mk r z f t.dmem) := by
  have hd := rdi_mk (z := z) (f := f) (d := t.dmem) hb hdi
  refine Kit.Fm.pre (k := 80) (by decide) hpre hb.fm rfl ?_ hd ?_
  · simp only [rsp, Reg64s.get64_rsp]
    rw [hsp]
    exact hb.rsp
  · unfold generateA
    rw [st_call rfl hd, cap_call (c := MachineData.mk r z f t.dmem) hpre hb rfl hd, cap_n,
      env_call (c := MachineData.mk r z f t.dmem) hpre hb rfl hd]
    have := (ctx_bounds hctx).1
    exact ⟨hctx.2.1.1.pos, show (st' s t).len < _ by omega, (ctx_genA hctx hpd).2⟩

-- The call of `generate`.
private theorem gen_call {t' : MachineData} {r : Reg64s} {z f}
    (hpre : Pre loopF loopA s) (hb : Base s ra t)
    (hp : Post generateF generateR (MachineData.mk r z f t.dmem) t')
    (hag : (mod generateF (MachineData.mk r z f t.dmem)).Agree (MachineData.mk r z f t.dmem) t')
    (hsp : r.rsp = t.regs.rsp) (hbp : r.rbp = t.regs.rbp)
    (hdi : r.rdi.toBitVec = t.regs.rbp.toBitVec) (hsi : r.rsi.toBitVec = t.regs.r14.toBitVec)
    (h14 : r.r14 = t.regs.r14) :
    Base s ra t' ∧ t'.regs.r14 = t.regs.r14
      ∧ Res (rdi s) (generate (env s) (st' s t) t.regs.r14.toBitVec.toNat)
          (fun q => rax t' = 0#64 ∧ st' s t' = q) t' := by
  have hd := rdi_mk (z := z) (f := f) (d := t.dmem) hb hdi
  refine ⟨Base.call (by decide) hpre hb hp hag rfl hsp hd hbp,
    (call_regs hag).2.2.2.1.trans h14, ?_⟩
  have h := generate_post hpre hb hp rfl hd
  simp only [rsi, Reg64s.get64_rsi] at h
  rwa [hsi] at h

-- The variant at `.LB83` after `.LB75`.
private theorem v83_lt {r : Reg64s} {z f d} (h14 : r.r14 = t.regs.r14)
    (hp : (stOf d (rdi s)).pendingGenerations ≤ (stOf t.dmem (rdi s)).pendingGenerations) :
    V s ".LB83" (MachineData.mk r z f d) < V s ".LB75" t := by
  simp only [V, outer, W, st']
  rw [h14]
  omega

end

set_option experimental.vcgen true

variable [Host] [FunDecls] {s : MachineData} {ra : Int64}

-- `generate T`; `.LB61` on an error, `.LB93` if `len ≤ T`, `.LB64` if the slot at `T` is
-- final, else `.LB83`.
theorem lb75 (hgen : Spec "generate" generateF generateA generateR)
    (hpre : Pre loopF loopA s) : OblAt s ra (.label ".LB75") := by
  loop_case
  intro t ht
  have h : At75 s ra t := ht
  clear ht
  obtain ⟨hb, T, hT, hctx, hpd, hstep⟩ := h
  have hn := n_le' hpre hb
  have hL := len_le' hb
  have hTn := hctx.1
  have hr14 : t.regs.r14.toBitVec.toNat = T := by rw [hT, toNat_small (by omega)]
  kvcgen64 [hgen]
  all_goals clear hgen
  all_goals try bbu_norm
  case vc1 =>
    rw [hb.rsp]
    exact hb.fm.call_isSome (k := 80) (by decide) hpre
  case vc2 =>
    exact gen_pre_mk hpre hb hctx hpd rfl rfl
  case vc3 =>
    rename_i t' hp hag af hnz
    obtain ⟨hb', h14', hres⟩ := gen_call hpre hb hp hag rfl rfl rfl rfl rfl
    clear hp hag
    rw [hr14] at hres
    bbu_norm at hnz
    simp only [CondCode.interp_nz, StatusFlags.zf_from_result, BitVec.and_self,
      Bool.not_eq_true', beq_eq_false_iff_ne, BitVec.zero_eq] at hnz
    loop_goto
    · exact stack_mk hb'.rsp
    · show At61 s ra _
      refine at61_of hb' (fun e he => ?_) hres (fun _ h => h.1) hnz
      exact iter_err ⟨_, hctx, by rw [hstep, he]; rfl⟩
    · left
      rw [v61]
      simp only [V]
      omega
  case vc4 =>
    rename_i t' hp hag af hnz
    obtain ⟨hb', -, -⟩ := gen_call hpre hb hp hag rfl rfl rfl rfl rfl
    rw [hb'.rbp]
    exact hb'.fm.wf.isSome_struct (by simp [WORDS_eq])
  case' vc7 | vc8 =>
    rename_i hz
    revert hz
  all_goals rename_i t' hp hag af hnz hf
  all_goals obtain ⟨hb', h14', hres⟩ := gen_call hpre hb hp hag rfl rfl rfl rfl rfl
  all_goals clear hp hag
  all_goals rw [hr14] at hres
  all_goals bbu_norm at hnz hf
  all_goals simp only [CondCode.interp_nz, StatusFlags.zf_from_result, BitVec.and_self,
    Bool.not_eq_false', beq_iff_eq, BitVec.zero_eq] at hnz
  all_goals obtain ⟨q, hq, -, hst⟩ :=
    res_ok_of_msb hres (by rw [show rax t' = 0#64 from hnz] <;> rfl)
  all_goals subst hst
  all_goals have hs2 : step (env s) (st' s t) T = afterGen T (st' s t') := by rw [hstep, hq]; rfl
  all_goals have hlen := rd_len hb'
  all_goals have hL' := len_le' hb'
  all_goals have hlen' : (BitVec.ofNat 64 (st' s t').len).toNat = (st' s t').len :=
    toNat_small (by omega)
  all_goals have hr14' : t'.regs.r14.toBitVec.toNat = T := by rw [h14', hr14]
  case vc5 =>
    simp only [CondCode.interp_nc, StatusFlags.cf_from_result, Bool.not_eq_true', Kit.cf_sub'] at hf
    simp only [hlen, hlen', hr14'] at hf
    rw [ag_top (fun h => absurd h.1 (by omega)), pt_ge hf] at hs2
    loop_goto
    · exact stack_mk hb'.rsp
    · exact ⟨⟨hb'.fm, hb'.rsp, hb'.rbp⟩, iter_err ⟨_, hctx, hs2⟩⟩
    · left
      simp only [V]
      omega
  all_goals simp only [CondCode.interp_nc, StatusFlags.cf_from_result, Bool.not_eq_false',
    Kit.cf_sub] at hf
  all_goals simp only [hlen, hlen', hr14'] at hf
  case vc6 =>
    rw [dest_addr, hb'.rbp, hr14']
    exact hb'.fm.wf.word_isSome hb'.fm.wf.mapped (by simp only [WORDS_eq, DEST_eq]; omega)
  all_goals intro hz
  all_goals bbu_norm at hz
  all_goals have hpq := (generate_shape hq).2.2
  case vc7 =>
    rw [Kit.nz_sub, Bool.not_eq_true', beq_eq_false_iff_ne, dest_addr, hb'.rbp, hr14'] at hz
    have hd : (st' s t').dest T ≠ T := by
      rw [dest_stOf (by rw [← len_stOf]; exact hf)]
      intro he
      exact hz (BitVec.eq_of_toNat_eq (he.trans hr14'.symm))
    rw [ag_top (fun h => hd h.2)] at hs2
    have hops := gen_ops hctx hq
    rw [← cap_n] at hops
    loop_goto
    · exact stack_mk hb'.rsp
    · show At83 s ra _
      exact ⟨⟨hb'.fm, hb'.rsp, hb'.rbp⟩, hlen, T, by rw [h14']; exact hT, ⟨_, hctx, hs2⟩,
        hops, hf, hd, hctx.2.1.1.pos.generate hq⟩
    · left
      exact v83_lt h14'
        (by show (st' s t').pendingGenerations ≤ (st' s t).pendingGenerations; omega)
  case vc8 =>
    rw [Kit.nz_sub, Bool.not_eq_false', beq_iff_eq, dest_addr, hb'.rbp, hr14'] at hz
    have hd : (st' s t').dest T = T := by
      rw [dest_stOf (by rw [← len_stOf]; exact hf), hz, hr14']
    rw [ag_done ⟨hf, hd⟩] at hs2
    have hi := iter_next ⟨_, hctx, hs2⟩
    loop_goto
    · exact stack_mk hb'.rsp
    · show At64 s ra _
      exact at64_mk hb' rfl rfl rfl (by rw [h14', hT, BitVec.ofNat_add]) hi
    · left
      refine Nat.lt_of_lt_of_le (m := W * outer s t t.regs.r14.toBitVec.toNat) ?_ ?_
      · exact v64_lt hTn h14' (r14_succ hT (by omega)) hr14
          (by show (st' s t').pendingGenerations ≤ (st' s t).pendingGenerations; omega)
      · simp only [V]
        exact Nat.le_add_right _ _

-- `.LB94` if `len ≤ T`, `.LB95` if the slot at `T` is final, else `.LB83`.
theorem lb81 (hpre : Pre loopF loopA s) : OblAt s ra (.label ".LB81") := by
  loop_case
  intro t ht
  have h : At81 s ra t := ht
  clear ht
  obtain ⟨hb, T, hT, hit, hops, hpos⟩ := h
  have hTn := iter_lt hit
  have hn := n_le' hpre hb
  have hL := len_le' hb
  have hlen := rd_len hb
  have hr14 : t.regs.r14.toBitVec.toNat = T := by rw [hT, toNat_small (by omega)]
  have hlen' : (BitVec.ofNat 64 (st' s t).len).toNat = (st' s t).len := toNat_small (by omega)
  kvcgen64
  all_goals bbu_norm
  · rw [hb.rbp]
    exact hb.fm.wf.isSome_struct (by simp [WORDS_eq])
  · rename_i hf
    bbu_norm at hf
    simp only [CondCode.interp_nc, StatusFlags.cf_from_result, Bool.not_eq_true', Kit.cf_sub'] at hf
    simp only [hlen,
      hlen', hr14] at hf
    rw [pt_ge hf] at hit
    loop_goto
    · exact stack_of hb.rsp
    · exact ⟨⟨hb.fm, hb.rsp, hb.rbp⟩, iter_err hit⟩
    · simp [V]
  · rename_i hf
    bbu_norm at hf
    simp only [CondCode.interp_nc, StatusFlags.cf_from_result, Bool.not_eq_false', Kit.cf_sub] at hf
    simp only [hlen,
      hlen', hr14] at hf
    rw [dest_addr, hb.rbp, hr14]
    exact hb.fm.wf.word_isSome hb.fm.wf.mapped (by simp only [WORDS_eq, DEST_eq]; omega)
  · rename_i hf hz
    bbu_norm at hz hf
    simp only [CondCode.interp_nc, StatusFlags.cf_from_result, Bool.not_eq_false', Kit.cf_sub] at hf
    simp only [hlen,
      hlen', hr14] at hf
    rw [Kit.z_sub, beq_iff_eq, dest_addr, hb.rbp, hr14] at hz
    have hd : (st' s t).dest T = T := by
      rw [dest_stOf (by rw [← len_stOf]; exact hf), hz, hr14]
    rw [pt_fixed hd] at hit
    loop_goto
    · exact stack_of hb.rsp
    · exact ⟨⟨hb.fm, hb.rsp, hb.rbp⟩, iter_err hit⟩
    · simp [V]
  · rename_i hf hz
    bbu_norm at hz hf
    simp only [CondCode.interp_nc, StatusFlags.cf_from_result, Bool.not_eq_false', Kit.cf_sub] at hf
    simp only [hlen,
      hlen', hr14] at hf
    rw [Kit.z_sub, beq_eq_false_iff_ne, dest_addr, hb.rbp, hr14] at hz
    have hd : (st' s t).dest T ≠ T := by
      rw [dest_stOf (by rw [← len_stOf]; exact hf)]
      intro he
      exact hz (BitVec.eq_of_toNat_eq (he.trans hr14.symm))
    show At83 s ra _
    exact ⟨⟨hb.fm, hb.rsp, hb.rbp⟩, hlen, T, hT, hit, hops, hf, hd, hpos⟩
  · simp only [V, outer, st']
    omega

-- `.LB64` if `T` is the top, `.LB109` if the top is out of reach, else `swapWith T`, then
-- `.LB64` or `.LB61` on an error.
theorem lb83 (hswap : Spec "swapWith" swapWithF swapWithA swapWithR)
    (hpre : Pre loopF loopA s) : OblAt s ra (.label ".LB83") := by
  loop_case
  intro t ht
  have h : At83 s ra t := ht
  clear ht
  obtain ⟨hb, hax, T, hT, hit, hops, hTl, hd, hpos⟩ := h
  have hTn := iter_lt hit
  have hn := n_le' hpre hb
  have hL := len_le' hb
  have hr14 : t.regs.r14.toBitVec.toNat = T := by rw [hT, toNat_small (by omega)]
  kvcgen64 [hswap]
  all_goals clear hswap
  all_goals try bbu_norm
  case vc1 =>
    rename_i hz
    bbu_norm at hz
    rw [Kit.z_sub, beq_iff_eq, hax, hT, ofNat_pred (by omega)] at hz
    have hl := ofNat_inj64 (by omega) (by omega) hz
    rw [pt_last hTl hd (by omega)] at hit
    have hi := iter_next hit
    loop_goto
    · exact stack_mk hb.rsp
    · show At64 s ra _
      exact at64_mk hb rfl rfl rfl (by rw [hT, BitVec.ofNat_add]) hi
    · left
      refine Nat.lt_of_lt_of_le (m := W * outer s t t.regs.r14.toBitVec.toNat) ?_ ?_
      · exact v64_lt hTn rfl (r14_succ hT (by omega)) hr14 (Nat.le_refl _)
      · simp only [V]
        exact Nat.le_add_right _ _
  case vc2 =>
    rename_i hz ha
    bbu_norm at hz ha
    rw [Kit.z_sub, beq_eq_false_iff_ne, hax, hT, ofNat_pred (by omega)] at hz
    rw [Kit.a_sub_imm _ _ (by decide), decide_eq_true_eq, hax, hT, sub_of (by omega),
      ofNat_pred (by omega), toNat_small (by omega)] at ha
    have hne : T ≠ (st' s t).len - 1 := fun h => hz (by rw [h])
    rw [pt_far hTl hd hne (by simp only [MAX_SWAP_DEPTH]; omega)] at hit
    have hR := iter_err hit
    loop_goto
    · exact stack_mk hb.rsp
    · show At109 s ra _
      refine at109_mk hb rfl rfl rfl hT ?_ hR
      show t.regs.rax.toBitVec - t.regs.r14.toBitVec - 17#64 = _
      have hk : (st' s t).len - T - 17 = (st' s t).len - 1 - T - MAX_SWAP_DEPTH := by
        simp only [MAX_SWAP_DEPTH]; omega
      rw [hax, hT, sub_of (by omega), sub_of (by omega), hk]
    · left
      simp only [V]
      omega
  case vc3 =>
    rw [hb.rsp]
    exact hb.fm.call_isSome (k := 80) (by decide) hpre
  case vc4 =>
    exact swap_pre_mk hpre hb hpos hops rfl rfl
  all_goals rename_i hz ha t' hp hag af hnz
  all_goals obtain ⟨hb', h14', hres⟩ := swap_call hpre hb hp hag rfl rfl rfl rfl rfl
  all_goals clear hp hag
  all_goals rw [hr14] at hres
  all_goals bbu_norm at hz ha hnz
  all_goals rw [Kit.z_sub, beq_eq_false_iff_ne, hax, hT, ofNat_pred (by omega)] at hz
  all_goals rw [Kit.a_sub_imm _ _ (by decide), decide_eq_false_iff_not, hax, hT, sub_of (by omega),
      ofNat_pred (by omega), toNat_small (by omega)] at ha
  all_goals have hne : T ≠ (st' s t).len - 1 := fun h => hz (by rw [h])
  all_goals rw [pt_swap hTl hd hne (by simp only [MAX_SWAP_DEPTH]; omega)] at hit
  all_goals simp only [CondCode.interp_z, StatusFlags.zf_from_result, BitVec.and_self, beq_iff_eq,
    beq_eq_false_iff_ne, BitVec.zero_eq] at hnz
  case vc5 =>
    obtain ⟨q, hq, -, hst⟩ := res_ok_of_msb hres (by rw [show rax t' = 0#64 from hnz]; rfl)
    rw [hq] at hit
    have hi := iter_next hit
    rw [← hst] at hi
    loop_goto
    · exact stack_mk hb'.rsp
    · show At64 s ra _
      exact at64_mk hb' rfl rfl rfl (by rw [h14', hT, BitVec.ofNat_add]) hi
    · obtain ⟨-, -, hpd⟩ := swapWith_shape hq
      left
      refine Nat.lt_of_lt_of_le (m := W * outer s t t.regs.r14.toBitVec.toNat) ?_ ?_
      · refine v64_lt hTn h14' (r14_succ hT (by omega)) hr14 (Nat.le_of_eq ?_)
        show (st' s t').pendingGenerations = (st' s t).pendingGenerations
        rw [hst, hpd]
      · simp only [V]
        exact Nat.le_add_right _ _
  case vc6 =>
    loop_goto
    · exact stack_mk hb'.rsp
    · show At61 s ra _
      refine at61_of hb' (fun e he => ?_) hres (fun _ h => h.1) hnz
      rw [he] at hit
      exact iter_err hit
    · left
      rw [v61]
      simp only [V]
      omega

end Loop

end Bbu
