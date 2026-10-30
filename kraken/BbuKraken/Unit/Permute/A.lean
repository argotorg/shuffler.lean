import BbuKraken.Unit.Permute.ML

/-!
# `permute`: the blocks of phase A and B, and the epilogue

`entry`, the prologue, `.LB.Emission.permute.0`, `.LB.Emission.permute.1`, `.LB.Emission.permute.2` and `.LB.Emission.permute.3`. The fall of `.LB.Emission.permute.3` makes the
model vectors of `.LB.Emission.permute.14` (`start`).
-/

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit
set_option experimental.vcgen true

namespace Bbu.Unit
open Bbu.Sep
namespace Permute

section
variable {S : Addr} {g : G} {F : MProp 64} {s : MachineData} {ra : Int64} {L : Lc}

theorem isSome_at {P R : MProp 64} {m : Mem 64} (a : Addr) (v : Word) (h : P.get m)
    (e : P = Wd a v ∗ R) : (m.loadInt a 8).isSome = true :=
  Wd.isSome (e ▸ h)

-- The six `pushq` from the entry stack (`r` is `rsp` after the call): the loads before the
-- stores, and the memory after them.
theorem pushes {m : Mem 64} {x0 x1 x2 x3 x4 x5 : Word}
    (hm : (View S g ∗ Stk (rsp s) (L.toList ++ [x0, x1, x2, x3, x4, x5]) ra.toBitVec ∗ F).get m)
    {r a b c d e f : Word} (hr : r = rsp s - 8#64) (ha : a = s.regs.r15.toBitVec)
    (hb : b = s.regs.r14.toBitVec) (hc : c = s.regs.r13.toBitVec) (hd : d = s.regs.r12.toBitVec)
    (he : e = s.regs.rbp.toBitVec) (hf : f = s.regs.rbx.toBitVec) :
    (m.loadInt (r - 8#64) 8).isSome = true
    ∧ ((m.storeInt (r - 8#64) 8 a.toInt).loadInt (r - 8#64 - 8#64) 8).isSome = true
    ∧ (((m.storeInt (r - 8#64) 8 a.toInt).storeInt (r - 8#64 - 8#64) 8 b.toInt).loadInt
        (r - 8#64 - 8#64 - 8#64) 8).isSome = true
    ∧ ((((m.storeInt (r - 8#64) 8 a.toInt).storeInt (r - 8#64 - 8#64) 8 b.toInt).storeInt
        (r - 8#64 - 8#64 - 8#64) 8 c.toInt).loadInt (r - 8#64 - 8#64 - 8#64 - 8#64) 8).isSome = true
    ∧ (((((m.storeInt (r - 8#64) 8 a.toInt).storeInt (r - 8#64 - 8#64) 8 b.toInt).storeInt
        (r - 8#64 - 8#64 - 8#64) 8 c.toInt).storeInt (r - 8#64 - 8#64 - 8#64 - 8#64) 8 d.toInt).loadInt
        (r - 8#64 - 8#64 - 8#64 - 8#64 - 8#64) 8).isSome = true
    ∧ ((((((m.storeInt (r - 8#64) 8 a.toInt).storeInt (r - 8#64 - 8#64) 8 b.toInt).storeInt
        (r - 8#64 - 8#64 - 8#64) 8 c.toInt).storeInt (r - 8#64 - 8#64 - 8#64 - 8#64) 8 d.toInt).storeInt
        (r - 8#64 - 8#64 - 8#64 - 8#64 - 8#64) 8 e.toInt).loadInt
        (r - 8#64 - 8#64 - 8#64 - 8#64 - 8#64 - 8#64) 8).isSome = true
    ∧ (View S g ∗ Loc (base s) L ∗ Sv s ra F).get
        ((((((m.storeInt (r - 8#64) 8 a.toInt).storeInt (r - 8#64 - 8#64) 8 b.toInt).storeInt
        (r - 8#64 - 8#64 - 8#64) 8 c.toInt).storeInt (r - 8#64 - 8#64 - 8#64 - 8#64) 8 d.toInt).storeInt
        (r - 8#64 - 8#64 - 8#64 - 8#64 - 8#64) 8 e.toInt).storeInt
        (r - 8#64 - 8#64 - 8#64 - 8#64 - 8#64 - 8#64) 8 f.toInt) := by
  subst ha hb hc hd he hf
  have hm6 := (Fm.push (c := { s with dmem := _, regs := { s.regs with
      rsp := UInt64.ofBitVec (r - 8#64 - 8#64 - 8#64 - 8#64 - 8#64 - 8#64 - 16408#64) } })
    hm hr rfl rfl).mem
  subst hr
  simp only [sub_sub_ofNat, Nat.reduceAdd] at hm6 ⊢
  rw [stk_frame] at hm
  have h1 : (View S g ∗ Loc (rsp s - 16464#64) L
      ∗ Top (rsp s) x0 x1 x2 x3 x4 s.regs.r15.toBitVec ra.toBitVec F).get _ :=
    wd_store (a := rsp s - 16#64) hm (by unfold Top; ecancel) (by unfold Top; ecancel)
  have h2 : (View S g ∗ Loc (rsp s - 16464#64) L
      ∗ Top (rsp s) x0 x1 x2 x3 s.regs.r14.toBitVec s.regs.r15.toBitVec ra.toBitVec F).get _ :=
    wd_store (a := rsp s - 24#64) h1 (by unfold Top; ecancel) (by unfold Top; ecancel)
  have h3 : (View S g ∗ Loc (rsp s - 16464#64) L
      ∗ Top (rsp s) x0 x1 x2 s.regs.r13.toBitVec s.regs.r14.toBitVec s.regs.r15.toBitVec
        ra.toBitVec F).get _ :=
    wd_store (a := rsp s - 32#64) h2 (by unfold Top; ecancel) (by unfold Top; ecancel)
  have h4 : (View S g ∗ Loc (rsp s - 16464#64) L
      ∗ Top (rsp s) x0 x1 s.regs.r12.toBitVec s.regs.r13.toBitVec s.regs.r14.toBitVec
        s.regs.r15.toBitVec ra.toBitVec F).get _ :=
    wd_store (a := rsp s - 40#64) h3 (by unfold Top; ecancel) (by unfold Top; ecancel)
  have h5 : (View S g ∗ Loc (rsp s - 16464#64) L
      ∗ Top (rsp s) x0 s.regs.rbp.toBitVec s.regs.r12.toBitVec s.regs.r13.toBitVec
        s.regs.r14.toBitVec s.regs.r15.toBitVec ra.toBitVec F).get _ :=
    wd_store (a := rsp s - 48#64) h4 (by unfold Top; ecancel) (by unfold Top; ecancel)
  exact ⟨isSome_at _ x5 hm (by unfold Top; ecancel), isSome_at _ x4 h1 (by unfold Top; ecancel),
    isSome_at _ x3 h2 (by unfold Top; ecancel), isSome_at _ x2 h3 (by unfold Top; ecancel),
    isSome_at _ x1 h4 (by unfold Top; ecancel), isSome_at _ x0 h5 (by unfold Top; ecancel), hm6⟩

end

theorem b_entry [Host] [FunDecls] (S g F s ra) :
    Program.ForallBlocks finishAsm fun blk => blk.label = .entry → Obl S g F s ra blk := by
  pm_block [Obl]
  intro t ht
  kvcgen64
  simp only [LInv, Names.permute, ↓reduceIte]
  exact ht

theorem b_fn [Host] [FunDecls] (S g F s ra) (hpre : Sep.Pre S g F permuteA 2058 s) :
    Program.ForallBlocks finishAsm fun blk => blk.label = .label Names.permute →
      Obl S g F s ra blk := by
  pm_block [Obl, Names.permute]
  intro t ht
  simp only [LInv, Names.permute, ↓reduceIte] at ht
  subst ht
  obtain ⟨fr, v, hfr, hm⟩ := hpre.mem
  obtain ⟨L, x0, x1, x2, x3, x4, x5, rfl⟩ := split2058 hfr
  have hk0 : Kp S g F s ra _ (s.pushRa ra) := Kp.init hm
  have hS : (s.pushRa ra).regs.rdi.toBitVec = S := by simpa [MachineData.pushRa] using hpre.rdi
  have hr : (s.pushRa ra).regs.rsp.toBitVec = rsp s - 8#64 := by simp [MachineData.pushRa]
  obtain ⟨p1, p2, p3, p4, p5, p6, hm6⟩ := pushes (r := (s.pushRa ra).regs.rsp.toBitVec)
    (a := (s.pushRa ra).regs.r15.toBitVec) (b := (s.pushRa ra).regs.r14.toBitVec)
    (c := (s.pushRa ra).regs.r13.toBitVec) (d := (s.pushRa ra).regs.r12.toBitVec)
    (e := (s.pushRa ra).regs.rbp.toBitVec) (f := (s.pushRa ra).regs.rbx.toBitVec)
    hk0.mem hr rfl rfl rfl rfl rfl rfl
  kvcgen64
  all_goals try symexec_norm
  vc_by_shape
  | load =>
    first
    | with_reducible exact p1 | with_reducible exact p2 | with_reducible exact p3
    | with_reducible exact p4 | with_reducible exact p5 | with_reducible exact p6
    | (rw [hS, Fld.fold_stack_size]; exact View.isSome_len hm6)
  all_goals clear p1 p2 p3 p4 p5 p6 hm hfr
  case vc8 _ hz =>
    simp only [hS, rd_len' hm6, BitVec.and_self, BitVec.zero_eq, beq_iff_eq] at hz ⊢
    have hp : Flat.permute (flat g) = (.done, flat g) := by
      simp only [Flat.permute, show (flat g).size = 0 from hz, ↓reduceIte]
    cfg_goto
    · exact (Fm.push hk0.mem hr rfl rfl).stack
    · simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte]
      refine ⟨g, L, Fm.push hk0.mem hr rfl rfl, hpre.ok, Keep.refl g, ?_, ?_⟩
      · rw [hp]
      · rw [hp]; rfl
    · left; simp [V, Names.permute]
  case vc9 _ hz =>
    simp only [hS, rd_len' hm6, BitVec.and_self, BitVec.zero_eq, beq_eq_false_iff_ne, LInv,
      Names.permute, String.reduceEq, ↓reduceIte] at hz ⊢
    refine ⟨L, Fm.push hk0.mem hr rfl rfl, hS, rfl, ?_, fun i (hi : i < 0#64) => absurd hi (by bv_omega)⟩
    show 0#64 < g.h.len
    bv_omega
  case vc10 =>
    left; simp [V, Names.permute]

theorem b_57 [Host] [FunDecls] (S g F s ra) (hpre : Sep.Pre S g F permuteA 2058 s) :
    Program.ForallBlocks finishAsm fun blk => blk.label = .label ".LB.Emission.permute.0" →
      Obl S g F s ra blk := by
  pm_block [Obl]
  intro t ht
  simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨L, hF, h15, hbx, hlt, hag⟩ := ht
  have hx := lt_max hpre.ok hlt
  have hne := dest_ne_none hpre.args.2 hlt
  kvcgen64
  all_goals try symexec_norm
  vc_by_shape
  | load => rw [h15]; exact isSome_dest' hF.mem hx
  all_goals try simp only [h15, rd_dest_get hF.mem hx]
  case vc2 =>
    cfg_goto
    · exact (hF.next rfl rfl).stack
    · simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte]
      exact ⟨L, hF.next rfl rfl, h15, hbx, hlt, hag, rfl⟩
    · pm_dec
  all_goals rename_i hz; simp [h15, rd_dest_get hF.mem hx] at hz; exact absurd hz hne

-- The six loads of the epilogue, in the form of the VCs.
theorem Fm.isSome_pops {S : Addr} {g : G} {F : MProp 64} {s : MachineData} {ra : Int64} {L : Lc}
    {t : MachineData} (h : Fm S g F s ra L t) :
    (t.dmem.loadInt (16408#64 + t.regs.rsp.toBitVec) 8).isSome = true
    ∧ (t.dmem.loadInt (16408#64 + t.regs.rsp.toBitVec + 8#64) 8).isSome = true
    ∧ (t.dmem.loadInt (16408#64 + t.regs.rsp.toBitVec + 8#64 + 8#64) 8).isSome = true
    ∧ (t.dmem.loadInt (16408#64 + t.regs.rsp.toBitVec + 8#64 + 8#64 + 8#64) 8).isSome = true
    ∧ (t.dmem.loadInt (16408#64 + t.regs.rsp.toBitVec + 8#64 + 8#64 + 8#64 + 8#64) 8).isSome
      = true
    ∧ (t.dmem.loadInt (16408#64 + t.regs.rsp.toBitVec + 8#64 + 8#64 + 8#64 + 8#64 + 8#64)
      8).isSome = true := by
  have e : ∀ (k : Nat) (a : Addr), a = 16408#64 + t.regs.rsp.toBitVec + BitVec.ofNat 64 (8 * k) →
      k < 6 → (t.dmem.loadInt a 8).isSome = true := fun k a ha hk => ha ▸ h.isSome_pop hk
  exact ⟨e 0 _ (by bv_omega) (by decide), e 1 _ (by bv_omega) (by decide),
    e 2 _ (by bv_omega) (by decide), e 3 _ (by bv_omega) (by decide),
    e 4 _ (by bv_omega) (by decide), e 5 _ (by bv_omega) (by decide)⟩

theorem b_54 [Host] [FunDecls] (S g F s ra) :
    Program.ForallBlocks finishAsm fun blk => blk.label = .label ".LB.Emission.permute.1" →
      Obl S g F s ra blk := by
  pm_block [Obl]
  intro t ht
  simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨g', L, hF, hok, hQ⟩ := ht
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := hF.isSome_pops
  kvcgen64
  all_goals try symexec_norm
  vc_by_shape
  | load =>
    first
    | with_reducible exact p1 | with_reducible exact p2 | with_reducible exact p3
    | with_reducible exact p4 | with_reducible exact p5 | with_reducible exact p6
  | retAddr =>
    refine (congrArg Option.isSome (hF.pop ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_).retAddr).trans rfl
    all_goals rfl
  | ret =>
    refine Kp.ret (hF.pop ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) (by simp [Lc.length_toList]) hok
      fun t' _ hax => ⟨hQ.1, hQ.2.1, by show (rax t').setWidth 8 = _; rw [hax]; exact hQ.2.2⟩
    all_goals rfl

theorem b_56 [Host] [FunDecls] (S g F s ra) (hpre : Sep.Pre S g F permuteA 2058 s) :
    Program.ForallBlocks finishAsm fun blk => blk.label = .label ".LB.Emission.permute.2" →
      Obl S g F s ra blk := by
  pm_block [Obl]
  intro t ht
  simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨L, hF, h15, hbx, hlt, hag, hdx⟩ := ht
  have hx := lt_max hpre.ok hlt
  have hn := Nat.le_trans hpre.ok.len hpre.ok.n
  simp only [MAX_N] at hx hn
  have ha : t.regs.rsp.toBitVec + t.regs.rax.toBitVec * 8#64 + 8208#64
      = base s + 8208#64 + BitVec.ofNat 64 (8 * t.regs.rax.toBitVec.toNat) := by
    rw [hF.sp, idx8d]
  have hag' := agB_step hag hx
  rw [← hdx, BitVec.add_comm] at hag'
  have h1 : (1#64 + t.regs.rax.toBitVec).toNat = t.regs.rax.toBitVec.toNat + 1 := by bv_omega
  kvcgen64
  all_goals try symexec_norm
  vc_by_shape
  | load => exact hF.isSomeP hx ha
  case vc2 _ hz =>
    simp only [Bool.not_eq_true', beq_eq_false_iff_ne, hbx, BitVec.zero_eq] at hz
    cfg_goto
    · exact Fm.stack (hF.storeP hx ha _ rfl rfl)
    · simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte]
      exact ⟨_, hF.storeP hx ha _ rfl rfl, h15, hbx,
        by show 1#64 + t.regs.rax.toBitVec < g.h.len; bv_omega, hag'⟩
    · pm_dec
  case vc3 _ hz =>
    simp only [Bool.not_eq_false', beq_iff_eq, hbx, BitVec.zero_eq] at hz
    have hl : g.h.len = 1#64 + t.regs.rax.toBitVec := by bv_omega
    simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte]
    refine ⟨_, 0, hF.storeP hx ha _ rfl rfl, h15, hbx, ?_, ?_, ?_,
      fun i hi => absurd hi (Nat.not_lt_zero _), ?_⟩
    · bv_omega
    · show t.regs.rsp.toBitVec + 16#64 = _
      rw [hF.sp]; bv_omega
    · show t.regs.rsp.toBitVec + 16#64 + t.regs.rbx.toBitVec * 8#64 = _
      rw [hF.sp, hbx, idx8]
    · show AgB g.h.len _ g.h.dest
      rw [hl]; exact hag'
  case vc4 =>
    left
    have hd : (t.regs.rsp.toBitVec + 16#64 + t.regs.rbx.toBitVec * 8#64
        - (t.regs.rsp.toBitVec + 16#64)).toNat ≤ 8192 := by
      rw [hbx]; bv_omega
    pm_dec

theorem b_58 [Host] [FunDecls] (S g F s ra) (hpre : Sep.Pre S g F permuteA 2058 s) :
    Program.ForallBlocks finishAsm fun blk => blk.label = .label ".LB.Emission.permute.3" →
      Obl S g F s ra blk := by
  pm_block [Obl]
  intro t ht
  simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨L, k, hF, h15, hbx, hk, hax, hdx, hD, hag⟩ := ht
  have hn := Nat.le_trans hpre.ok.len hpre.ok.n
  simp only [MAX_N] at hn
  have hk' : k < MAX_N := by simp only [MAX_N]; omega
  -- The three stores: `desiredBy[k]`, `c1` and `c0`.
  have hF1 : Fm S g F s ra { L with D := L.D.set k Flat.NONE hk' }
      { t with dmem := Mem.storeInt t.dmem t.regs.rax.toBitVec 8 (-1) } :=
    hF.storeD hk' hax Flat.NONE (by rw [none_toInt]) rfl
  have ha1 : t.regs.rsp.toBitVec + 8#64 = base s + 8#64 := by rw [hF.sp]
  have h8 : (8#64).toInt = 8 := by decide
  have h1 : (1#64).toInt = 1 := by decide
  have hF2 : Fm S g F s ra { L with D := L.D.set k Flat.NONE hk', c1 := 8#64 }
      { t with dmem := ((Mem.storeInt t.dmem t.regs.rax.toBitVec 8 (-1)).storeInt
        (t.regs.rsp.toBitVec + 8#64) 8 8) } :=
    hF1.storeC1 ha1 8#64 (by rw [h8]) rfl
  kvcgen64
  all_goals try symexec_norm
  vc_by_shape
  | load =>
    first
    | with_reducible exact hF.isSomeD hk' hax
    | with_reducible exact hF1.isSomeC1 ha1
    | with_reducible exact hF2.isSomeC0 hF.sp
  case vc2 _ hz =>
    simp only [Bool.not_eq_true', beq_eq_false_iff_ne, BitVec.zero_eq] at hz
    have hd1 : (t.regs.rdx.toBitVec - (8#64 + t.regs.rax.toBitVec)).toNat
        < (t.regs.rdx.toBitVec - t.regs.rax.toBitVec).toNat := by
      rw [hax, hdx]; bv_omega
    rw [hax, hdx] at hz
    cfg_goto
    · exact Fm.stack (hF1.next rfl rfl)
    · simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte]
      refine ⟨_, k + 1, hF1.next rfl rfl, h15, hbx, by bv_omega, ?_, hdx, none_step hk' hD, hag⟩
      show 8#64 + t.regs.rax.toBitVec = _
      rw [hax]; bv_omega
    · pm_dec
  case vc5 _ hz =>
    simp only [Bool.not_eq_false', beq_iff_eq, BitVec.zero_eq] at hz
    rw [hax, hdx] at hz
    have hlen : g.h.len.toNat = k + 1 := by bv_omega
    obtain ⟨p0, hrg, hP0, hD0, hlt0⟩ := start hpre.ok hpre.args.2 hag
      (fun i hi => none_step hk' hD i (by rw [← hlen]; exact BitVec.lt_def.mp hi))
    have hF3 : Fm S g F s ra { L with D := L.D.set k Flat.NONE hk', c1 := 8#64, c0 := 1#64 }
        { t with dmem := (((Mem.storeInt t.dmem t.regs.rax.toBitVec 8 (-1)).storeInt
          (t.regs.rsp.toBitVec + 8#64) 8 8).storeInt t.regs.rsp.toBitVec 8 1) } :=
      hF2.storeC0 hF.sp 1#64 (by rw [h1]) rfl
    cfg_goto
    · exact Fm.stack (hF3.next rfl rfl)
    · simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte]
      refine ⟨_, 0, p0, _, ⟨hF3.next rfl rfl, by bv_omega, rfl,
        by show (1#64 : Word) = 0 + 1; decide, by show (8#64 : Word) = (0 + 1) * 8#64; decide,
        by show t.regs.rsp.toBitVec + 16#64 = _; rw [hF.sp], h15, hbx⟩, hrg, hP0, hD0, hlt0⟩
    · pm_dec

end Permute
end Bbu.Unit
