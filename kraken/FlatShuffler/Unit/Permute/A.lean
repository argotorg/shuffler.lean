module

public import FlatShuffler.Unit.Permute.ML
import all FlatShuffler.Unit.Permute.ML

@[expose] public section

/-!
# `permute`: the prologue, the loop `.LB.Emission.permute.0` and the epilogue

`entry`, the prologue, `.LB.Emission.permute.0` (`desiredBy[i] = NONE`), the epilogue
`.LB.Emission.permute.16` and the `ret` `.LB.Emission.permute.25` if the size is 0. The fall of
`.LB.Emission.permute.0` makes the model vectors of `.LB.Emission.permute.11` (`start`).
-/

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit
set_option experimental.vcgen true

namespace FlatShuffler.Unit
open FlatShuffler.Sep
namespace Permute

section
variable {S : Addr} {g : G} {F : MProp 64} {s : MachineData} {ra : Int64} {L : Lc}

theorem isSome_at {P R : MProp 64} {m : Mem 64} (a : Addr) (v : Word) (h : P.get m)
    (e : P = Wd a v ∗ R) : (m.loadInt a 8).isSome = true :=
  Wd.isSome (e ▸ h)

-- The loads of the six `pushq` from the entry stack (`r` is `rsp` after the call).
theorem pushes {m : Mem 64} {x0 x1 x2 x3 x4 x5 : Word}
    (hm : (View S g ∗ Stk (rsp s) (L.toList ++ [x0, x1, x2, x3, x4, x5]) ra.toBitVec ∗ F).get m)
    {r a b c d e : Word} (hr : r = rsp s - 8#64) (ha : a = s.regs.r15.toBitVec)
    (hb : b = s.regs.r14.toBitVec) (hc : c = s.regs.r13.toBitVec) (hd : d = s.regs.r12.toBitVec)
    (he : e = s.regs.rbp.toBitVec) :
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
        (r - 8#64 - 8#64 - 8#64 - 8#64 - 8#64 - 8#64) 8).isSome = true := by
  subst ha hb hc hd he hr
  simp only [sub_sub_ofNat, Nat.reduceAdd]
  rw [stk_frame] at hm
  have h1 : (View S g ∗ Loc (rsp s - 8272#64) L
      ∗ Top (rsp s) x0 x1 x2 x3 x4 s.regs.r15.toBitVec ra.toBitVec F).get _ :=
    wd_store (a := rsp s - 16#64) hm (by unfold Top; ecancel) (by unfold Top; ecancel)
  have h2 : (View S g ∗ Loc (rsp s - 8272#64) L
      ∗ Top (rsp s) x0 x1 x2 x3 s.regs.r14.toBitVec s.regs.r15.toBitVec ra.toBitVec F).get _ :=
    wd_store (a := rsp s - 24#64) h1 (by unfold Top; ecancel) (by unfold Top; ecancel)
  have h3 : (View S g ∗ Loc (rsp s - 8272#64) L
      ∗ Top (rsp s) x0 x1 x2 s.regs.r13.toBitVec s.regs.r14.toBitVec s.regs.r15.toBitVec
        ra.toBitVec F).get _ :=
    wd_store (a := rsp s - 32#64) h2 (by unfold Top; ecancel) (by unfold Top; ecancel)
  have h4 : (View S g ∗ Loc (rsp s - 8272#64) L
      ∗ Top (rsp s) x0 x1 s.regs.r12.toBitVec s.regs.r13.toBitVec s.regs.r14.toBitVec
        s.regs.r15.toBitVec ra.toBitVec F).get _ :=
    wd_store (a := rsp s - 40#64) h3 (by unfold Top; ecancel) (by unfold Top; ecancel)
  have h5 : (View S g ∗ Loc (rsp s - 8272#64) L
      ∗ Top (rsp s) x0 s.regs.rbp.toBitVec s.regs.r12.toBitVec s.regs.r13.toBitVec
        s.regs.r14.toBitVec s.regs.r15.toBitVec ra.toBitVec F).get _ :=
    wd_store (a := rsp s - 48#64) h4 (by unfold Top; ecancel) (by unfold Top; ecancel)
  exact ⟨isSome_at _ x5 hm (by unfold Top; ecancel), isSome_at _ x4 h1 (by unfold Top; ecancel),
    isSome_at _ x3 h2 (by unfold Top; ecancel), isSome_at _ x2 h3 (by unfold Top; ecancel),
    isSome_at _ x1 h4 (by unfold Top; ecancel), isSome_at _ x0 h5 (by unfold Top; ecancel)⟩

-- The entry memory with the array `permutation` out of `permW`: the locals `L` hold its values.
theorem entry_mem {fr : List Word} {v : Word} (hfr : fr.length = 1034)
    (hm : (View S g ∗ Stk (rsp s) fr v ∗ (permW s ∗ F)).get s.dmem) :
    ∃ L : Lc, ∃ x0 x1 x2 x3 x4 x5, fr = L.toList ++ [x0, x1, x2, x3, x4, x5]
      ∧ (View S g ∗ Stk (rsp s) fr v ∗ (Arr (rsi s) L.P.toList ∗ F)).get s.dmem
      ∧ ∀ i < MAX_N, rd s.dmem (rsi s + BitVec.ofNat 64 (8 * i)) = L.P.toList[i]! := by
  have e : ∀ X : MProp 64, View S g ∗ Stk (rsp s) fr v ∗ (X ∗ F)
      = X ∗ (View S g ∗ Stk (rsp s) fr v ∗ F) := fun X => by ac_rfl
  rw [e] at hm
  obtain ⟨vs, hvs, hm⟩ := ExArr.elim hm
  obtain ⟨L, hLP, x0, x1, x2, x3, x4, x5, hfrL⟩ := split1034 hfr ⟨vs.toArray, by simpa using hvs⟩
  have hP : L.P.toList = vs := by rw [hLP]; simp
  refine ⟨L, x0, x1, x2, x3, x4, x5, hfrL, by rw [e, hP]; exact hm, fun i hi => ?_⟩
  rw [hP, Arr.rd hm (by rw [hvs]; exact hi)]
  simp [hvs ▸ hi]

end

theorem v0_lt (x : Word) : 2 ^ 33 + x.toNat < 2 ^ 66 := by have := x.isLt; omega

theorem b_entry [Host] [FunDecls] (S g p0 F s ra) :
    Program.ForallBlocks finishAsm fun blk => blk.label = .entry → Obl S g p0 F s ra blk := by
  pm_block [Obl]
  intro t ht
  kvcgen64
  simp only [LInv, Names.permute, ↓reduceIte]
  exact ht

theorem b_fn [Host] [FunDecls] (S g p0 F s ra) (hpre : Sep.Pre S g (permW s ∗ F) (permuteA p0) 1034 s) :
    Program.ForallBlocks finishAsm fun blk => blk.label = .label Names.permute →
      Obl S g p0 F s ra blk := by
  pm_block [Obl, Names.permute]
  intro t ht
  simp only [LInv, Names.permute, ↓reduceIte] at ht
  subst ht
  obtain ⟨fr, v, hfr, hm⟩ := hpre.mem
  have hk25 : Kp S g (permW s ∗ F) s ra fr (s.pushRa ra) := Kp.init hm
  obtain ⟨L, x0, x1, x2, x3, x4, x5, rfl, hmL, hrdP⟩ := entry_mem hfr hm
  have hk0 : Kp S g (Arr (rsi s) L.P.toList ∗ F) s ra _ (s.pushRa ra) := Kp.init hmL
  have hS : (s.pushRa ra).regs.rdi.toBitVec = S := by simpa [MachineData.pushRa] using hpre.rdi
  have hr : (s.pushRa ra).regs.rsp.toBitVec = rsp s - 8#64 := by simp [MachineData.pushRa]
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := pushes (r := (s.pushRa ra).regs.rsp.toBitVec)
    (a := (s.pushRa ra).regs.r15.toBitVec) (b := (s.pushRa ra).regs.r14.toBitVec)
    (c := (s.pushRa ra).regs.r13.toBitVec) (d := (s.pushRa ra).regs.r12.toBitVec)
    (e := (s.pushRa ra).regs.rbp.toBitVec) hk0.mem hr rfl rfl rfl rfl rfl
  kvcgen64
  all_goals try symexec_norm
  vc_by_shape
  | load =>
    first
    | with_reducible exact p1 | with_reducible exact p2 | with_reducible exact p3
    | with_reducible exact p4 | with_reducible exact p5 | with_reducible exact p6
    | (rw [hS, Fld.fold_stack_size]; exact View.isSome_len hk0.mem)
  all_goals clear p1 p2 p3 p4 p5 p6
  case vc2 _ hz =>
    simp only [hS, rd_len' hk0.mem, BitVec.and_self, BitVec.zero_eq, beq_iff_eq] at hz
    have hp : Flat.permute (flat g) p0 = (.done, flat g) := by
      simp only [Flat.permute, show (flat g).size = 0 from hz, ↓reduceIte]
    cfg_goto
    · exact hk25.stack
    · simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte]
      exact ⟨_, hk25.next rfl rfl rfl rfl rfl rfl rfl rfl, hfr, hpre.ok, hp⟩
    · left; simp [V, Names.permute]
  case vc9 _ hz =>
    simp only [hS, rd_len' hk0.mem, BitVec.and_self, BitVec.zero_eq, beq_eq_false_iff_ne, LInv,
      Names.permute, String.reduceEq, ↓reduceIte] at hz ⊢
    refine ⟨L, 0, Fm.push hk0.mem hr rfl rfl, hS, rfl, by bv_omega, ?_, ?_,
      fun i hi => absurd hi (Nat.not_lt_zero _), fun i hi => ?_⟩
    · dsimp only; rw [hr]; unfold base; rw [show rsp s = s.regs.rsp.toBitVec from rfl]; bv_omega
    · dsimp only; rw [hr]; unfold base; rw [show rsp s = s.regs.rsp.toBitVec from rfl]; bv_omega
    · have hx := lt_max hpre.ok hi
      have h1 := hpre.args.2.2.2 i.toNat (BitVec.lt_def.mp hi)
      rw [show rsi s = s.regs.rsi.toBitVec from rfl, hrdP _ hx, BitVec.ofNat_toNat,
        BitVec.setWidth_eq] at h1
      rw [← h1, get_eq _ _ hx]; simp [hx]
  case vc10 =>
    left; simp only [V, Names.permute, String.reduceEq, ↓reduceIte]; exact v0_lt _

theorem b_0 [Host] [FunDecls] (S g p0 F s ra) (hpre : Sep.Pre S g (permW s ∗ F) (permuteA p0) 1034 s) :
    Program.ForallBlocks finishAsm fun blk => blk.label = .label ".LB.Emission.permute.0" →
      Obl S g p0 F s ra blk := by
  pm_block [Obl]
  intro t ht
  simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨L, k, hF, h13, h14, hk, hax, hdx, hD, hag⟩ := ht
  have hn := Nat.le_trans hpre.ok.len hpre.ok.xs
  simp only [MAX_N] at hn
  have hk' : k < MAX_N := by simp only [MAX_N]; omega
  -- The store `desiredBy[k]`.
  have hF1 : Fm S g F s ra { L with D := L.D.set k Flat.NONE hk' }
      { t with dmem := Mem.storeInt t.dmem t.regs.rax.toBitVec 8 (-1) } :=
    hF.storeD hk' hax Flat.NONE (by rw [none_toInt]) rfl
  kvcgen64
  all_goals try symexec_norm
  vc_by_shape
  | load =>
    with_reducible exact hF.isSomeD hk' hax
  case vc2 _ hz =>
    simp only [Bool.not_eq_true', beq_eq_false_iff_ne, BitVec.zero_eq] at hz
    have hd1 : (t.regs.rdx.toBitVec - (8#64 + t.regs.rax.toBitVec)).toNat
        < (t.regs.rdx.toBitVec - t.regs.rax.toBitVec).toNat := by
      rw [hax, hdx]; bv_omega
    rw [hax, hdx] at hz
    cfg_goto
    · exact Fm.stack (hF1.next rfl rfl)
    · simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte]
      refine ⟨_, k + 1, hF1.next rfl rfl, h13, h14, by bv_omega, ?_, hdx, none_step hk' hD, hag⟩
      show 8#64 + t.regs.rax.toBitVec = _
      rw [hax]; bv_omega
    · pm_dec
  case vc3 _ hz =>
    simp only [Bool.not_eq_false', beq_iff_eq, BitVec.zero_eq] at hz
    rw [hax, hdx] at hz
    have hlen : g.h.len.toNat = k + 1 := by bv_omega
    obtain ⟨hrg, hP0, hD0, hlt0⟩ := start hpre.ok hpre.args.2.2.1 hag
      (fun i hi => none_step hk' hD i (by rw [← hlen]; exact BitVec.lt_def.mp hi))
    cfg_goto
    · exact Fm.stack (hF1.next rfl rfl)
    · simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte]
      refine ⟨_, 0, p0, _, ⟨hF1.next rfl rfl, by bv_omega, rfl,
        by show (1#64 : Word) = 0 + 1; decide,
        by show t.regs.rsp.toBitVec + 16#64 = _; rw [hF.sp], h13, h14⟩, hrg, hP0, hD0, hlt0⟩
    · pm_dec

-- The six loads of the epilogue, in the form of the VCs.
theorem Fm.isSome_pops {S : Addr} {g : G} {F : MProp 64} {s : MachineData} {ra : Int64} {L : Lc}
    {t : MachineData} (h : Fm S g F s ra L t) :
    (t.dmem.loadInt (8216#64 + t.regs.rsp.toBitVec) 8).isSome = true
    ∧ (t.dmem.loadInt (8216#64 + t.regs.rsp.toBitVec + 8#64) 8).isSome = true
    ∧ (t.dmem.loadInt (8216#64 + t.regs.rsp.toBitVec + 8#64 + 8#64) 8).isSome = true
    ∧ (t.dmem.loadInt (8216#64 + t.regs.rsp.toBitVec + 8#64 + 8#64 + 8#64) 8).isSome = true
    ∧ (t.dmem.loadInt (8216#64 + t.regs.rsp.toBitVec + 8#64 + 8#64 + 8#64 + 8#64) 8).isSome
      = true
    ∧ (t.dmem.loadInt (8216#64 + t.regs.rsp.toBitVec + 8#64 + 8#64 + 8#64 + 8#64 + 8#64)
      8).isSome = true := by
  have e : ∀ (k : Nat) (a : Addr), a = 8216#64 + t.regs.rsp.toBitVec + BitVec.ofNat 64 (8 * k) →
      k < 6 → (t.dmem.loadInt a 8).isSome = true := fun k a ha hk => ha ▸ h.isSome_pop hk
  exact ⟨e 0 _ (by bv_omega) (by decide), e 1 _ (by bv_omega) (by decide),
    e 2 _ (by bv_omega) (by decide), e 3 _ (by bv_omega) (by decide),
    e 4 _ (by bv_omega) (by decide), e 5 _ (by bv_omega) (by decide)⟩

theorem b_6 [Host] [FunDecls] (S g p0 F s ra) :
    Program.ForallBlocks finishAsm fun blk => blk.label = .label ".LB.Emission.permute.16" →
      Obl S g p0 F s ra blk := by
  pm_block [Obl]
  intro t ht
  simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨g', L, hF, hok, hQ⟩ := ht
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := hF.isSome_pops
  have hP : L.P.toList.length = MAX_N := by simp
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
    refine intercept_mono_exit
      (E := fun a t => a = ra ∧ Sep.Post S (permW s ∗ F) 1034
        (fun g' t => permuteQ p0 g g' s t) s t ∧ Sep.mod.Agree s t) ?_ Or.inl
    · refine Kp.ret ((hF.pop ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_).exArr hP) (by simp [Lc.length_toList]) hok
        fun _ _ hax => hQ.of_returnRegister_eq hax
      all_goals rfl

theorem b_25 [Host] [FunDecls] (S g p0 F s ra) :
    Program.ForallBlocks finishAsm fun blk => blk.label = .label ".LB.Emission.permute.25" →
      Obl S g p0 F s ra blk := by
  pm_block [Obl]
  intro t ht
  simp only [LInv, Names.permute, String.reduceEq, ↓reduceIte] at ht
  obtain ⟨fr, hk, hfr, hok, hp⟩ := ht
  kvcgen64
  all_goals try symexec_norm
  vc_by_shape
  | retAddr => exact (congrArg Option.isSome hk.retAddr).trans rfl
  | ret =>
    refine intercept_mono_exit
      (E := fun a t => a = ra ∧ Sep.Post S (permW s ∗ F) 1034
        (fun g' t => permuteQ p0 g g' s t) s t ∧ Sep.mod.Agree s t) ?_ Or.inl
    · exact Kp.ret (hk.next rfl rfl rfl rfl rfl rfl rfl rfl) hfr hok
        fun t' _ hax => ⟨⟨Keep.refl g, by dsimp only; rw [hp],
          by dsimp only; rw [hp]; show (rax t').setWidth 8 = _; rw [hax]; rfl⟩,
          by show (rax t').setWidth 8 ≠ _; rw [hax]; change 0#8 ≠ 2#8; decide⟩

end Permute
end FlatShuffler.Unit
