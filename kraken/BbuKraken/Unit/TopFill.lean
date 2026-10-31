import BbuKraken.Unit.TopInv

/-!
# `build_bottom_up`: the fill blocks

The entry block `build_bottom_up` (the guard, `subq $32872`) and the loops that fill `PD[0..m)` and
`PP[0..n)` with `-1` (`.LB.build_bottom_up.0`, `.LB.build_bottom_up.2`), with `.LB.build_bottom_up.18` and `.LB.build_bottom_up.1`. `init_mem` splits the
memory at the entry into the struct `Em`, the locals `Lc` and the rest `R0`.
-/

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

namespace Bbu.Unit
open Bbu.Sep
namespace Top
set_option experimental.vcgen true

section
variable {s : MachineData} {ra : Int64}

-- The struct and the locals at the entry are mapped.
theorem loc_mapped (hp : TopPre s) : Mem.Mapped [(topS s, offLoc)] (s.pushRa ra).dmem := by
  intro b hb
  have hb' : In (topS s) offOps b := by
    simp only [Mem.Blocks.Inside, or_false, offLoc, offOps] at hb ⊢; unfold In; omega
  exact frame0 hp b (by
    have := in_frame_of_S hp hb'; unfold In at this
    simp only [Mem.Blocks.Inside, or_false]; omega)

theorem Lc.cut {m : Mem 64} {S : Addr} {L : Loc} (hm : Mem.Mapped [(S, offLoc)] m)
    (h0 : rd m (S + BitVec.ofNat 64 offPM) = L.pm) (h1 : rd m (S + BitVec.ofNat 64 offPad) = L.pad)
    (h2 : ∀ i (hi : i < MAX_N), rd m (S + BitVec.ofNat 64 offPD + BitVec.ofNat 64 (8 * i)) = L.pd[i])
    (h3 : ∀ i (hi : i < MAX_N), rd m (S + BitVec.ofNat 64 offPP + BitVec.ofNat 64 (8 * i)) = L.pp[i]) :
    (Lc S L).get (Sep.cut m (Rng S offPM (offLoc - offPM))) := by
  unfold Lc
  have w0 := Wd.cut_rng (o := offPM) hm (by decide) h0
  have w1 := Wd.cut_rng (o := offPad) hm (by decide) h1
  have w2 := Arr.cut_rng (o := offPD) hm (by decide) h2
  have w3 := Arr.cut_rng (o := offPP) hm (by decide) h3
  have w := sep_rng w0 (sep_rng w1 (sep_rng w2 w3 rfl) rfl) rfl
  exact w

-- The memory at the entry: the struct, the locals and the rest.
theorem init_mem (hp : TopPre s) (_hg : TopGuard s) :
    (Em (topS s) (hdr0 s ra) ∗ Lc (topS s) (loc0 s ra) ∗ R0 s ra).get (s.pushRa ra).dmem := by
  have hm := loc_mapped (ra := ra) hp
  have hE := Em.cut (h := hdr0 s ra) (fun b hb => hm b (by
      simp only [Mem.Blocks.Inside, or_false, EmSize, offLoc] at hb ⊢; omega))
    rfl rfl rfl rfl rfl rfl rfl (fun i hi => by simp [hdr0]) (fun i hi => by simp [hdr0]) rfl rfl rfl
  have hL := Lc.cut (L := loc0 s ra) hm rfl rfl (fun i hi => by simp [loc0]) (fun i hi => by simp [loc0])
  have hR : (R0 s ra).get (Sep.cut (s.pushRa ra).dmem fun b => ¬In (topS s) offLoc b) := by
    unfold R0; rw [MProp.get_mk]
  have h1 := sep_cut (R := fun b => ¬In (topS s) EmSize b) hL hR
    (fun b h1 h2 => h2 (by unfold Rng at h1; unfold In; simp only [EmSize, offPM, offLoc] at *; omega))
    (fun b => by unfold Rng In; simp only [EmSize, offPM, offLoc]; omega)
  have h2 := sep_cut (R := fun _ => True) hE h1 (fun b h1 h2 => h2 h1)
    (fun b => by simp only [true_iff]; exact Classical.em _)
  rwa [cut_univ _ (fun _ => trivial)] at h2

end

theorem locA_m0 {s ra} (h : mArg s = 0) : locA s ra (mArg s) = loc0 s ra := by
  simp only [locA, h, Flat.clearPos_zero]

theorem locB_m0 {s ra} (hm : mArg s = 0) (hn : nArg s = 0) : locB s ra = loc0 s ra := by
  simp only [locB, hm, hn, Flat.clearPos_zero, Flat.bindDest_zero, Flat.bindPos_zero]

theorem b_18 [Host] [FunDecls] (s ra) (_hpre : TopPre s) :
    Program.ForallBlocks buildBottomUpAsm fun blk => blk.label = .label ".LB.build_bottom_up.18" →
      Obl s ra blk := by
  pm_block [Obl]
  intro t ht
  simp only [LInv, Names.build_bottom_up, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨hm0, hs, ha⟩ := ht
  kvcgen64
  all_goals try symexec_norm
  vc_by_shape
  | goto ".LB.build_bottom_up.1" =>
    rename_i hc
    have hn := ha.n_pos (by simpa only [Bool.not_eq_true'] using hc)
    cfg_goto
    · exact hs.stack_of rfl
    · simp only [LInv, Names.build_bottom_up, String.reduceEq, ↓reduceIte]
      refine ⟨hn, TS.cast ?_ rfl (locA_m0 hm0).symm, ha.next rfl rfl rfl rfl rfl rfl⟩
      exact hs.next rfl rfl rfl rfl rfl rfl rfl rfl
    · top_dec
  | other =>
    rename_i hc
    have hn := ha.n0 (by simpa only [Bool.not_eq_false'] using hc)
    first
      | (simp only [LInv, Names.build_bottom_up, String.reduceEq, ↓reduceIte]
         refine ⟨hm0, TS.cast ?_ rfl (locB_m0 hm0 hn).symm, ha.next rfl rfl rfl rfl rfl rfl⟩
         exact hs.next rfl rfl rfl rfl rfl rfl rfl rfl)
      | top_dec

theorem locA_succ {s ra k} (hk : k < MAX_N) :
    locA s ra (k + 1) = { locA s ra k with pd := (locA s ra k).pd.set k Flat.NONE } := by
  simp only [locA, Flat.clearPos_succ, put_ofNat _ hk]

theorem locK_0_n0 {s ra} (hn : nArg s = 0) : locK s ra 0 = locA s ra (mArg s) := by
  simp only [locK, locA, hn, Flat.clearPos_zero, Flat.bindDest_zero, Flat.bindPos_zero]

-- `movq $-1, PD[k]` with `rax = k`.
theorem TS.fill_pd {s ra t k} (hs : TS s ra (hdr0 s ra) (locA s ra k) t)
    (hax : t.regs.rax.toBitVec = BitVec.ofNat 64 k) (hk : k < MAX_N) :
    (Em (topS s) (hdr0 s ra) ∗ Lc (topS s) (locA s ra (k + 1)) ∗ R0 s ra).get
      (t.dmem.storeInt (t.regs.rsp.toBitVec + t.regs.rax.toBitVec * 8#64 + 16480#64) 8 (-1)) := by
  rw [locA_succ hk, ← NONE_toInt]; exact hs.st_pdk hax hk _

theorem b_0 [Host] [FunDecls] (s ra) (_hpre : TopPre s) :
    Program.ForallBlocks buildBottomUpAsm fun blk => blk.label = .label ".LB.build_bottom_up.0" →
      Obl s ra blk := by
  pm_block [Obl]
  intro t ht
  simp only [LInv, Names.build_bottom_up, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨k, hk, hs, ha, hax⟩ := ht
  have hkN := hs.m_lt hk
  have hdi := congrArg (·.toBitVec) ha.rdi
  kvcgen64
  all_goals try symexec_norm
  all_goals try simp only [add_ofInt_neg_one] at *
  all_goals try exact hs.isSome_pdk hax hkN
  vc_by_shape
  | goto ".LB.build_bottom_up.0" =>
    rename_i hc
    have hk1 := succ_lt_of_jne hc hdi hax hk
    cfg_goto
    · exact hs.stack_of rfl
    · simp only [LInv, Names.build_bottom_up, String.reduceEq, ↓reduceIte]
      exact ⟨k + 1, hk1, hs.step (hs.fill_pd hax hkN) rfl rfl rfl rfl rfl rfl rfl,
        ha.next rfl rfl rfl rfl rfl rfl, succ_ofNat hax⟩
    · top_dec
      rw [succ_ofNat hax, hax, toNat_ofNat_lt hkN, toNat_ofNat_lt (hs.m_lt hk1)]
      omega
  | goto ".LB.build_bottom_up.3" =>
    rename_i hc _ hz
    have he : k + 1 = mArg s := succ_eq_of_jne hc hdi hax hk
    have hn := ha.n0 hz
    cfg_goto
    · exact hs.stack_of rfl
    · simp only [LInv, Names.build_bottom_up, String.reduceEq, ↓reduceIte]
      refine ⟨by omega, TS.cast ?_ rfl (by rw [locK_0_n0 hn, ← he]), ha.next rfl rfl rfl rfl rfl rfl⟩
      exact hs.step (hs.fill_pd hax hkN) rfl rfl rfl rfl rfl rfl rfl
    · top_dec
  | other =>
    rename_i hc _ hz
    have he : k + 1 = mArg s := succ_eq_of_jne hc hdi hax hk
    have hn := ha.n_pos hz
    first
      | (simp only [LInv, Names.build_bottom_up, String.reduceEq, ↓reduceIte]
         refine ⟨hn, TS.cast ?_ rfl (by rw [← he]), ha.next rfl rfl rfl rfl rfl rfl⟩
         exact hs.step (hs.fill_pd hax hkN) rfl rfl rfl rfl rfl rfl rfl)
      | top_dec

theorem locF_0 {s ra} : locF s ra 0 = locA s ra (mArg s) := by
  simp only [locF, locA, Flat.clearPos_zero]

theorem locF_n {s ra} : locF s ra (nArg s) = locK s ra 0 := by
  simp only [locF, locK, Flat.bindDest_zero, Flat.bindPos_zero]

theorem locF_succ {s ra j} (hj : j < MAX_N) :
    locF s ra (j + 1) = { locF s ra j with pp := (locF s ra j).pp.set j Flat.NONE } := by
  simp only [locF, Flat.clearPos_succ, put_ofNat _ hj]

-- `movq $-1, 8192(%rax)` with `rax = S + offPD + 8j`.
theorem TS.fill_pp {s ra t j} (hs : TS s ra (hdr0 s ra) (locF s ra j) t)
    (hax : t.regs.rax.toBitVec = topS s + BitVec.ofNat 64 offPD + BitVec.ofNat 64 (8 * j))
    (hj : j < MAX_N) :
    (Em (topS s) (hdr0 s ra) ∗ Lc (topS s) (locF s ra (j + 1)) ∗ R0 s ra).get
      (t.dmem.storeInt (t.regs.rax.toBitVec + 8192#64) 8 (-1)) := by
  rw [locF_succ hj, ← NONE_toInt,
    show t.regs.rax.toBitVec + 8192#64 = topS s + BitVec.ofNat 64 offPP + BitVec.ofNat 64 (8 * j) by
      rw [hax]; simp only [offPD, offPP, MAX_N] at hj ⊢; bv_omega]
  exact Lc.st_pp hs.mem hj _

theorem TS.pp_addr {s ra h L t j} (_hs : TS s ra h L t)
    (hax : t.regs.rax.toBitVec = topS s + BitVec.ofNat 64 offPD + BitVec.ofNat 64 (8 * j))
    (hj : j < MAX_N) :
    t.regs.rax.toBitVec + 8192#64 = topS s + BitVec.ofNat 64 offPP + BitVec.ofNat 64 (8 * j) := by
  rw [hax]; simp only [offPD, offPP, MAX_N] at hj ⊢; bv_omega

theorem b_1 [Host] [FunDecls] (s ra) (_hpre : TopPre s) :
    Program.ForallBlocks buildBottomUpAsm fun blk => blk.label = .label ".LB.build_bottom_up.1" →
      Obl s ra blk := by
  pm_block [Obl]
  intro t ht
  simp only [LInv, Names.build_bottom_up, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨hn, hs, ha⟩ := ht
  have hsi := congrArg (·.toBitVec) ha.rsi
  have hnN := hs.g.n_le'
  kvcgen64
  all_goals try symexec_norm
  case vc1 =>
    simp only [LInv, Names.build_bottom_up, String.reduceEq, ↓reduceIte]
    refine ⟨0, hn, TS.cast (L := locA s ra (mArg s)) ?_ rfl locF_0.symm,
      ha.next rfl rfl rfl rfl rfl rfl, ?_, ?_⟩
    · exact hs.next rfl rfl rfl rfl rfl rfl rfl rfl
    · rw [hs.sp]; simp only [offPD]; bv_omega
    · rw [hs.sp, hsi]; simp only [nArg, rsi, Reg64s.get64_rsi, offPD] at hnN ⊢; bv_omega
  case vc2 =>
    top_dec

theorem b_2 [Host] [FunDecls] (s ra) (_hpre : TopPre s) :
    Program.ForallBlocks buildBottomUpAsm fun blk => blk.label = .label ".LB.build_bottom_up.2" →
      Obl s ra blk := by
  pm_block [Obl]
  intro t ht
  simp only [LInv, Names.build_bottom_up, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨j, hj, hs, ha, hax, hdx⟩ := ht
  have hnN := hs.g.n_le'
  have hjN : j < MAX_N := by simp only [MAX_N]; omega
  kvcgen64
  all_goals try symexec_norm
  all_goals try (rw [hs.pp_addr hax hjN]; exact Lc.isSome_pp hs.mem hjN)
  vc_by_shape
  | goto ".LB.build_bottom_up.2" =>
    rename_i hc
    have hj1 := succ_lt_of_je (by simpa only [Bool.not_eq_true'] using hc) hax hdx hj
    cfg_goto
    · exact hs.stack_of rfl
    · simp only [LInv, Names.build_bottom_up, String.reduceEq, ↓reduceIte]
      exact ⟨j + 1, hj1, hs.step (hs.fill_pp hax hjN) rfl rfl rfl rfl rfl rfl rfl,
        ha.next rfl rfl rfl rfl rfl rfl, add8 hax, hdx⟩
    · top_dec
      exact Or.inl (by have := sub8_lt hax hdx hj1 hnN; omega)
  | goto ".LB.build_bottom_up.19" =>
    rename_i hc _ hz
    have he : j + 1 = nArg s :=
      succ_eq_of_je (by simpa only [Bool.not_eq_false'] using hc) hax hdx hj hnN
    have hm := ha.m0 hz
    cfg_goto
    · exact hs.stack_of rfl
    · simp only [LInv, Names.build_bottom_up, String.reduceEq, ↓reduceIte]
      refine ⟨hm, TS.cast (L := locF s ra (j + 1)) ?_ rfl
        (by rw [he, locF_n, ← locK_m, hm]), ha.next rfl rfl rfl rfl rfl rfl⟩
      exact hs.step (hs.fill_pp hax hjN) rfl rfl rfl rfl rfl rfl rfl
    · top_dec
  | other =>
    rename_i hc _ hz
    have he : j + 1 = nArg s :=
      succ_eq_of_je (by simpa only [Bool.not_eq_false'] using hc) hax hdx hj hnN
    have hm := ha.m_pos hz
    first
      | (simp only [LInv, Names.build_bottom_up, String.reduceEq, ↓reduceIte]
         refine ⟨hm, TS.cast (L := locF s ra (j + 1)) ?_ rfl (by rw [he, locF_n]),
           ha.next rfl rfl rfl rfl rfl rfl⟩
         exact hs.step (hs.fill_pp hax hjN) rfl rfl rfl rfl rfl rfl rfl)
      | top_dec

theorem locA_zero {s ra} : locA s ra 0 = loc0 s ra := by
  simp only [locA, Flat.clearPos_zero]

section
variable {s : MachineData} {ra : Int64} {t : MachineData}

-- The state after `subq $32872, %rsp` in the entry block.
theorem TS.init (hp : TopPre s) (hg : TopGuard s) (hm : t.dmem = (s.pushRa ra).dmem)
    (hsp : t.regs.rsp.toBitVec = (s.pushRa ra).regs.rsp.toBitVec - 32872#64)
    (e4 : t.regs.rbx = s.regs.rbx) (e5 : t.regs.rbp = s.regs.rbp) (e6 : t.regs.r12 = s.regs.r12)
    (e7 : t.regs.r13 = s.regs.r13) (e8 : t.regs.r14 = s.regs.r14) (e9 : t.regs.r15 = s.regs.r15) :
    TS s ra (hdr0 s ra) (loc0 s ra) t :=
  ⟨hm ▸ init_mem hp hg, hsp.trans (pushRa_sp s ra), e4, e5, e6, e7, e8, e9, hg⟩

end

theorem b_fn [Host] [FunDecls] (s ra) (hpre : TopPre s) :
    Program.ForallBlocks buildBottomUpAsm fun blk => blk.label = .label Names.build_bottom_up →
      Obl s ra blk := by
  pm_block [Obl, Names.build_bottom_up]
  intro t ht
  simp only [LInv, Names.build_bottom_up, ↓reduceIte] at ht
  subst ht
  kvcgen64
  all_goals try symexec_norm
  vc_by_shape
  | goto ".LB.build_bottom_up.14" =>
    first
      | (rename_i hc
         have hng := not_guard_of_cf (s := s) (by simp only [Idioms.cf_sub] at hc; exact hc)
         cfg_goto
         · exact MachineData.stackAtOrBelow_of_toNat_lt (by simp)
         · simp only [LInv, Names.build_bottom_up, String.reduceEq, ↓reduceIte]
           exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hng⟩
         · top_dec)
      | (rename_i hc
         have hng := not_guard_of_ja (s := s) (by exact hc)
         cfg_goto
         · exact MachineData.stackAtOrBelow_of_toNat_lt (by simp)
         · simp only [LInv, Names.build_bottom_up, String.reduceEq, ↓reduceIte]
           exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hng⟩
         · top_dec)
  | goto ".LB.build_bottom_up.18" =>
    rename_i h1 _ hz h2
    have hg := guard_of (s := s) (by simp only [Idioms.cf_sub] at h1; exact h1) (by exact h2)
    cfg_goto
    · exact MachineData.stackAtOrBelow_of_toNat_lt (by
        simp only [MachineData.regs_pushRa, Reg64s.get64_rsp, Reg64s.set64_rsp]
        have := hpre.rsp_ge; simp only [rsp] at this; bv_omega)
    · simp only [LInv, Names.build_bottom_up, String.reduceEq, ↓reduceIte]
      exact ⟨zero_of_test hz, TS.init hpre hg rfl rfl rfl rfl rfl rfl rfl rfl,
        ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
    · top_dec
  | other =>
    rename_i h1 _ hz h2
    have hg := guard_of (s := s) (by simp only [Idioms.cf_sub] at h1; exact h1) (by exact h2)
    first
      | (simp only [LInv, Names.build_bottom_up, String.reduceEq, ↓reduceIte]
         refine ⟨0, pos_of_test hz, TS.cast (L := loc0 s ra) ?ts rfl locA_zero.symm,
           ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
         case ts => exact TS.init hpre hg rfl rfl rfl rfl rfl rfl rfl rfl)
      | (top_dec; done)
      | (top_dec; bv_omega)

end Top
end Bbu.Unit
