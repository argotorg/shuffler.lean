import BbuKraken.Contracts
import BbuKraken.ModelLemmas
import BbuKraken.Kit
import BbuKraken.Fn.ProduceLemmas

/-!
The body triple of `produce` (`c/bbu/produce.S`). The saved registers `rbx`,
`rbp`, `r14`, `r13`, `r15` and `r12` hold the struct, the offset `d`, `8 * d`, the
target slot of `d`, its kind and the encoded copy of the slot. The byte at
`rsp s - 57` holds the opcode of the slot. Every call is at `rsp s - 64`.
-/

open Std.WP Lean.Order
open scoped Program.WP

set_option experimental.vcgen true
-- `notq r`: Kraken has no spec for it. It does not change the flags.
@[spec] theorem not_reg_spec [Host] [FunDecls] (asz : Width) (r : Reg64)
    {Q : PUnit → MachineData → Prop} {E : Int64 → MachineData → Prop} :
    ⦃ fun s => Q () { s with regs := s.regs.set64 r (~~~(s.regs.get64 r)) } ⦄
      (Directive.instr (.regular asz .W64 (.not (.reg (.low r .W64)))))
    ⦃ Q; E ⦄ := by
  refine ⟨fun s hpre => ?_⟩
  refine Program.wp_single fun _ _ _ _ hn _ => ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, RegOrMem.interp, MachineData.set,
    MachineData.setReg, Reg64s.get_low_W64, Reg64s.set_low_W64, Effects.All]
  exact hn _ hpre

namespace Bbu
namespace Produce

section

variable (s : MachineData) (ra : Int64)
-- `.LB32` and `.LB39`: `emit` pushes the slot.
def At32 (t : MachineData) : Prop :=
  Lp s ra t ∧ emit (env s) (st s) (dd s) = add (st s) (sl s) (dd s) (.push (sl s))
-- `.LB40`: `emit` dups the copy `c` in `r12`.
def At40 (t : MachineData) : Prop :=
  Lp s ra t ∧ isJunk (sl s) = false ∧ ∃ c, cp s = some c ∧ (st s).len - 1 - c ≤ MAX_DUP_DEPTH
    ∧ t.regs.r12.toBitVec = BitVec.ofNat 64 c
-- `.LB31`: no copy is in reach; the opcode is in the local byte.
def At31 (t : MachineData) : Prop :=
  Lp s ra t ∧ isJunk (sl s) = false ∧ Far (st s) (sl s) ∧ t.regs.r12.toBitVec = encOpt (cp s)
    ∧ rdb t.dmem (rsp s - 57#64) = (sl s).valueOpcode
-- `.LB41`: the slot is not free.
def At41 (t : MachineData) : Prop :=
  Lp s ra t ∧ isJunk (sl s) = false ∧ Far (st s) (sl s) ∧ t.regs.r12.toBitVec = encOpt (cp s)
    ∧ canBeFreelyGenerated (sl s) = false
-- `.LB30`: the result of `emit`.
def At30 (t : MachineData) : Prop :=
  Hold s ra t ∧ Res (rdi s) (emit (env s) (st s) (dd s))
    (fun st' => rax t = 0#64 ∧ stOf t.dmem (rdi s) = st') t
-- `.LB35` and `.LB37`: `produce` fails an assertion.
def Asrt (t : MachineData) : Prop :=
  Base s ra t ∧ produce (env s) (st s) (dd s) = .error .assertion
-- `.LB28`: the result of `produce`.
def At28 (t : MachineData) : Prop :=
  Base s ra t ∧ Res (rdi s) (produce (env s) (st s) (dd s))
    (fun st' => rax t = 0#64 ∧ stOf t.dmem (rdi s) = st') t

def V : Label → MachineData → Nat
  | ".LB28", _ => 0
  | ".LB35", _ | ".LB37", _ => 1
  | ".LB30", _ => 2
  | ".LB32", _ | ".LB39", _ | ".LB40", _ => 3
  | ".LB41", _ => 4
  | ".LB31", _ => 5
  | _, _ => 6

end

end Produce

-- A jump to a label of the cfg: the stack, the invariant and the variant.
local macro "cfg_goto" : tactic => `(tactic| (
  apply Program.Intercept.intro_label
  · repeat ((fail_if_success (apply List.getElem?_cons_zero)); (apply List.getElem?_cons_succ_of))
    apply List.getElem?_cons_zero
  refine Or.inl ⟨?_, ?_, ?_⟩))

open Produce in
theorem produce_body [Host] [FunDecls]
    (hcopy : Spec "shallowestCopyPosition" shallowestCopyF shallowestCopyA shallowestCopyR)
    (hspill : Spec "isSpilled" isSpilledF isSpilledA isSpilledR)
    (hpush : Spec "push" pushF pushA pushR)
    (hdup : Spec "dup" dupF dupA dupR) :
    Body produceAsm produceF produceA produceR := by
  intro s ra
  refine ⟨fun s₀ ⟨h₀, hpre⟩ => ?_⟩
  subst h₀
  replace hpre : Pre 72 produceA s := hpre
  have hle : 72 ≤ s.regs.rsp.toBitVec.toNat := hpre.2.1.le
  refine Program.WP.cfg (fun
      | .entry, t | .label "produce", t => t = s.pushRa ra
      | .label ".LB31", t => At31 s ra t
      | .label ".LB32", t | .label ".LB39", t => At32 s ra t
      | .label ".LB30", t => At30 s ra t
      | .label ".LB28", t => At28 s ra t
      | .label ".LB40", t => At40 s ra t
      | .label ".LB41", t => At41 s ra t
      | .label ".LB35", t | .label ".LB37", t => Asrt s ra t
      | _, _ => False)
    V ?_ rfl
  cfg_cases
  case left t ht =>
    subst ht
    kvcgen64
  case right.left t ht =>
    subst ht
    clear hspill hpush hdup
    kvcgen64 [hcopy]
    all_goals bbu_norm at *
    all_goals try simp only [pushes_eq] at *
    all_goals try simp only [a64, a57, a72, tw_eq, kind_eq hpre, opc_eq hpre, take_setWidth] at *
    case vc1 | vc2 | vc3 | vc4 | vc5 | vc6 =>
      exact fr_ld (by (repeat apply Mem.Mapped.storeInt); exact map0 hpre) (by bv_omega)
    case vc7 => exact tg_isSome hpre
    case vc8 => exact tw_isSome hpre
    case vc9 => exact kind_isSome hpre
    case vc10 => exact opc_isSome hpre
    case vc11 => exact byte_isSome hpre
    case vc12 => exact fr_ld ((fm0 hpre).map.storeInt _ _ _) (by bv_omega)
    case vc13 =>
      exact Kit.Fm.pre (k := 64) (by decide) hpre (fm1 hpre) rfl rfl rfl trivial
    case vc14 =>
      rename_i t hz _ hp hag
      obtain ⟨hL, -, -⟩ := after_copy hpre hp hag rfl rfl rfl rfl rfl rfl rfl rfl rfl
      cfg_goto
      · exact stack_of hL.rsp
      · exact ⟨hL.mov rfl rfl rfl rfl rfl rfl rfl, emit_junk (junk_of hL hz)⟩
      · exact Or.inl (by simp [V])
    case vc15 =>
      rename_i t h15 hz _ hp hag
      obtain ⟨hL, hax, hb⟩ := after_copy hpre hp hag rfl rfl rfl rfl rfl rfl rfl rfl rfl
      have hn := cp_of hax hz
      cfg_goto
      · exact stack_of hL.rsp
      · refine ⟨hL.mov rfl rfl rfl rfl rfl rfl rfl, junk_of hL h15, fun c hc => ?_, hax, hb⟩
        simp [hc] at hn
      · exact Or.inl (by simp [V])
    case vc16 =>
      rename_i t _ _ _ hp hag
      obtain ⟨hL, -, -⟩ := after_copy hpre hp hag rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rw [hL.rbx]
      simpa [wordAt] using hL.fm.wf.word_isSome hL.fm.wf.mapped (k := 0) (by decide)
    case vc17 =>
      rename_i t h15 hz _ hbe hp hag
      obtain ⟨hL, hax, -⟩ := after_copy hpre hp hag rfl rfl rfl rfl rfl rfl rfl rfl rfl
      obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp (by simpa using cp_of hax hz)
      have h1 := copy_lt hc
      have h2 : (st s).len < 2 ^ 64 := len_lt
      rw [dist hL hax hc, Kit.be_sub_imm _ 15 (by decide)] at hbe
      simp only [decide_eq_true_eq, BitVec.toNat_ofNat] at hbe
      cfg_goto
      · exact stack_of hL.rsp
      · refine ⟨hL.mov rfl rfl rfl rfl rfl rfl rfl, junk_of hL h15, c, hc, ?_, ?_⟩
        · simp only [MAX_DUP_DEPTH]; omega
        · simpa [rax, hc, encOpt] using hax
      · exact Or.inl (by simp [V])
    case vc18 =>
      rename_i t h15 hz _ hbe hp hag
      obtain ⟨hL, hax, hb⟩ := after_copy hpre hp hag rfl rfl rfl rfl rfl rfl rfl rfl rfl
      obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp (by simpa using cp_of hax hz)
      have h1 := copy_lt hc
      have h2 : (st s).len < 2 ^ 64 := len_lt
      rw [dist hL hax hc, Kit.be_sub_imm _ 15 (by decide)] at hbe
      simp only [decide_eq_false_iff_not, BitVec.toNat_ofNat] at hbe
      refine ⟨hL.mov rfl rfl rfl rfl rfl rfl rfl, junk_of hL h15, fun c' hc' => ?_, hax, hb⟩
      obtain rfl : c' = c := Option.some.inj (hc'.symm.trans hc)
      simp only [MAX_DUP_DEPTH]; omega
    case vc19 => exact Or.inl (by simp [V])
  case right.right.left t ht =>
    clear hcopy hspill hpush hdup
    kvcgen64
    all_goals bbu_norm at *
    all_goals obtain ⟨hL, hj, hf, h12, hb⟩ := ht
    case vc1 => exact byte_ld hpre hL.toBase
    case vc2 =>
      rename_i hz _
      cfg_goto
      · exact stack_of hL.rsp
      · refine ⟨hL.mov rfl rfl rfl rfl rfl rfl rfl, emit_push hj hf ?_⟩
        rw [free_eq, lit_of hL.toBase hb hz]; rfl
      · exact Or.inl (by simp only [V]; decide)
    case vc3 =>
      rename_i hz hk _
      cfg_goto
      · exact stack_of hL.rsp
      · refine ⟨hL.mov rfl rfl rfl rfl rfl rfl rfl, hj, hf, h12, ?_⟩
        rw [free_eq, lit_of hL.toBase hb hz, hj, ret_of hL hk]; rfl
      · exact Or.inl (by simp only [V]; decide)
    case vc4 =>
      rename_i hz hk _
      refine ⟨hL.mov rfl rfl rfl rfl rfl rfl rfl, emit_push hj hf ?_⟩
      rw [free_eq, ret_of hL hk]; simp
    case vc5 => exact Or.inl (by simp only [V]; decide)
  case right.right.right.left t ht =>
    clear hcopy hspill hdup
    kvcgen64 [hpush]
    all_goals bbu_norm at *
    all_goals obtain ⟨hL, he⟩ := ht
    case vc1 => exact ra_ld hpre hL.toBase
    case vc2 => exact push_pre hpre hL rfl rfl rfl rfl
    case vc3 =>
      rename_i t' hp hag _
      refine ⟨Hold.call (by decide) hpre hL.toHold hp hag rfl rfl rfl rfl rfl rfl, ?_⟩
      rw [he]; exact push_res hpre hL hp.2.2 rfl rfl rfl rfl
    case vc4 => exact Or.inl (by simp only [V]; decide)
  case right.right.right.right.left t ht =>
    clear hcopy hspill hpush hdup
    kvcgen64
    all_goals bbu_norm at *
    all_goals obtain ⟨hH, hR⟩ := ht
    all_goals
      replace hR : Res (rdi s) (emit (env s) (st s) (dd s))
        (fun st' => rax t = 0#64 ∧ stOf t.dmem (rdi s) = st') t := hR
    all_goals obtain ⟨hlen, hpos, h8⟩ := at30_rd hpre hH
    all_goals obtain ⟨hl0, hl1, hl2⟩ := at30_isSome hpre hH
    case vc1 =>
      rename_i hx _
      rw [nz_test] at hx
      cfg_goto
      · exact stack_of hH.rsp
      · refine ⟨⟨hH.fm, hH.rsp⟩, ?_⟩
        rw [produce_eq]
        exact Res.bind_err hR (fun _ h => h.1) (by simpa [rax] using hx)
      · exact Or.inl (by simp only [V]; decide)
    case vc2 => exact hl0
    case vc3 => exact hl1
    case vc4 =>
      rename_i hx _ hc
      rw [nz_test] at hx
      rw [Kit.nz_sub] at hc
      obtain ⟨st', he, hax, rfl⟩ := Res.ok_of hR (by simpa [rax] using hx)
      cfg_goto
      · exact stack_of hH.rsp
      · refine ⟨⟨hH.fm, hH.rsp⟩, ?_⟩
        rw [produce_of_emit he]
        refine tail_bad fun hp => ?_
        have := emit_len he
        rw [← hpos, ← pos_iff hlen (by omega)] at hp
        simp [hp] at hc
      · exact Or.inl (by simp only [V]; decide)
    case vc5 | vc7 => exact hl2
    case vc6 =>
      rename_i hx _ hz _ hc
      rw [nz_test] at hx
      rw [Kit.z_test] at hz
      rw [Kit.nz_sub] at hc
      obtain ⟨st', he, hax, rfl⟩ := Res.ok_of hR (by simpa [rax] using hx)
      have hp : positionOf (stOf t.dmem (rdi s)) (dd s) = some ((stOf t.dmem (rdi s)).len - 1) := by
        have := emit_len he
        rw [← hpos, ← pos_iff hlen (by omega)]; simpa using hc
      cfg_goto
      · exact stack_of hH.rsp
      · refine ⟨⟨hH.fm, hH.rsp⟩, ?_⟩
        rw [produce_of_emit he, tail_ok hp, pending_zero]
        · exact ⟨hax, rfl⟩
        · simp only [beq_iff_eq] at hz
          show (rd t.dmem (wordAt (rdi s) 1)).toNat = 0
          rw [← h8, hz]; rfl
      · exact Or.inl (by simp only [V]; decide)
    case vc8 =>
      rename_i hx _ hz _ hc
      rw [nz_test] at hx
      rw [Kit.z_test] at hz
      rw [Kit.nz_sub] at hc
      obtain ⟨st', he, hax, rfl⟩ := Res.ok_of hR (by simpa [rax] using hx)
      have hp : positionOf (stOf t.dmem (rdi s)) (dd s) = some ((stOf t.dmem (rdi s)).len - 1) := by
        have := emit_len he
        rw [← hpos, ← pos_iff hlen (by omega)]; simpa using hc
      simp only [h8] at hz ⊢
      refine ⟨⟨Fm.pend hpre hH.fm _, hH.rsp⟩, ?_⟩
      rw [produce_of_emit he, tail_ok hp]
      refine ⟨hax, ?_⟩
      show stOf _ (rdi s) = _
      rw [stOf_pend hH.fm.wf]
      have : rd t.dmem (wordAt (rdi s) 1) ≠ 0#64 := by simpa using hz
      have h1 : (rd t.dmem (wordAt (rdi s) 1) - 1#64).toNat
          = (rd t.dmem (wordAt (rdi s) 1)).toNat - 1 := by bv_omega
      rw [h1]; rfl
    case vc9 => exact Or.inl (by simp only [V]; decide)
  case right.right.right.right.right.left t ht =>
    clear hcopy hspill hpush hdup
    obtain ⟨hb, hR⟩ := ht
    have hsp : t.regs.rsp.toBitVec = s.regs.rsp.toBitVec - 64#64 := hb.rsp
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hb.fm.pops (a := 8#64 + t.regs.rsp.toBitVec) (by rw [hsp]; rfl)
    kvcgen64
    all_goals bbu_norm at *
    case vc1 | vc2 | vc3 | vc4 | vc5 | vc6 => exact fr_ld hb.fm.map (by rw [hsp]; bv_omega)
    case vc7 =>
      simp only [MachineData.retAddr, Option.isSome_map, Reg64s.get64_rsp]
      exact fr_ld hb.fm.map (by rw [hsp]; bv_omega)
    case vc8 =>
      refine Kit.Fm.ret (by decide) hpre hb.fm ?_ ?_ fun u hm hax => res_out hm hax hR
      · simp only [rsp, Reg64s.get64_rsp, hsp]; bv_omega
      · intro q hq
        cases q <;> simp_all
  case right.right.right.right.right.right.left t ht =>
    clear hcopy hspill hdup
    kvcgen64 [hpush]
    all_goals bbu_norm at *
    all_goals obtain ⟨hL, he⟩ := ht
    case vc1 => exact ra_ld hpre hL.toBase
    case vc2 => exact push_pre hpre hL rfl rfl rfl rfl
    case vc3 =>
      rename_i t' hp hag _
      have hH := Hold.call (by decide) hpre hL.toHold hp hag rfl rfl rfl rfl rfl rfl
      cfg_goto
      · exact stack_of hH.rsp
      · refine ⟨hH, ?_⟩
        rw [he]; exact push_res hpre hL hp.2.2 rfl rfl rfl rfl
      · exact Or.inl (by simp only [V]; decide)
  case right.right.right.right.right.right.right.left t ht =>
    clear hcopy hspill hpush
    kvcgen64 [hdup]
    all_goals bbu_norm at *
    all_goals obtain ⟨hL, hj, c, hc, hb, h12⟩ := ht
    case vc1 => exact ra_ld hpre hL.toBase
    case vc2 => exact dup_pre hpre hL hc rfl rfl rfl h12 rfl
    case vc3 =>
      rename_i t' hp hag _
      have hH := Hold.call (by decide) hpre hL.toHold hp hag rfl rfl rfl rfl rfl rfl
      cfg_goto
      · exact stack_of hH.rsp
      · refine ⟨hH, ?_⟩
        rw [emit_dup hj hc hb]; exact dup_res hpre hL hp.2.2 hc rfl rfl h12 rfl
      · exact Or.inl (by simp only [V]; decide)
  case right.right.right.right.right.right.right.right.left t ht =>
    clear hcopy hpush hdup
    kvcgen64 [hspill]
    all_goals bbu_norm at *
    all_goals obtain ⟨hL, hj, hf, h12, hfree⟩ := ht
    case vc1 => exact ra_ld hpre hL.toBase
    case vc2 => exact spill_pre hpre hL rfl rfl rfl rfl
    case vc3 =>
      rename_i t' hp hag _ hx _
      obtain ⟨hL', hax, -⟩ := spill_res hpre hL hp hag rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      cfg_goto
      · exact stack_of hL'.rsp
      · refine ⟨hL'.mov rfl rfl rfl rfl rfl rfl rfl, emit_push hj hf ?_⟩
        rw [hfree, spill_of hax hx]; rfl
      · exact Or.inl (by simp only [V]; decide)
    case vc4 =>
      rename_i t' hp hag _ hx hz _
      obtain ⟨hL', hax, h12'⟩ := spill_res hpre hL hp hag rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      have hs : (canBeFreelyGenerated (sl s) || isSpilled (env s) (sl s)) = false := by
        rw [hfree, spill_of hax hx]; rfl
      have hn := cp_isNone (by rw [h12']; exact h12) hz
      cfg_goto
      · exact stack_of hL'.rsp
      · exact ⟨⟨hL'.fm, hL'.rsp⟩, produce_err (emit_none hj hs (Option.isNone_iff_eq_none.mp hn))⟩
      · exact Or.inl (by simp only [V]; decide)
    case vc5 =>
      rename_i t' hp hag _ hx hz _
      obtain ⟨hL', -, -⟩ := spill_res hpre hL hp hag rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      have := hL'.fm.wf.word_isSome hL'.fm.wf.mapped (k := 0) (by decide)
      rw [hL'.rbx]; simpa [wordAt] using this
    case vc6 =>
      rename_i t' hp hag _ hx hz _ hzz
      obtain ⟨hL', -, h12'⟩ := spill_res hpre hL hp hag rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      have hn := cp_isNone (by rw [h12']; exact h12) hz
      cases hc : cp s with
      | none => rw [hc] at hn; cases hn
      | some c =>
        have h12c : t'.regs.r12.toBitVec = BitVec.ofNat 64 c := by rw [h12', h12, hc]; rfl
        have hfar := hf c hc
        have h1 := copy_lt hc
        have h2 := len_lt (s := s)
        have h3 : MAX_DUP_DEPTH = 15 := rfl
        rw [far_val hL' hfar h12c, far_nz (by omega) (by omega)] at hzz
        cases hzz
    case vc7 =>
      rename_i t' hp hag _ hx hz _ hzz
      obtain ⟨hL', -, -⟩ := spill_res hpre hL hp hag rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rw [ptr_addr hL'.toHold]
      exact hL'.fm.wf.word_isSome hL'.fm.wf.mapped (k := 7) (by decide)
    case vc8 =>
      rename_i t' hp hag _ hx hz _ hzz
      obtain ⟨hL', -, -⟩ := spill_res hpre hL hp hag rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rw [ptr_addr hL'.toHold, blkOf_def]
      simpa [wordAt] using hL'.fm.wf.blk_isSome hL'.fm.wf.mapped (k := 0) (by decide)
    case vc9 =>
      rename_i t' hp hag _ hx hz _ hzz
      obtain ⟨hL', -, -⟩ := spill_res hpre hL hp hag rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rw [ptr_addr hL'.toHold]
      exact hL'.fm.wf.word_isSome (by apply Mem.Mapped.storeInt; exact hL'.fm.wf.mapped)
        (k := 7) (by decide)
    case vc10 =>
      rename_i t' hp hag _ hx hz _ hzz
      obtain ⟨hL', -, -⟩ := spill_res hpre hL hp hag rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      exact blk1_isSome hL'.toHold _
    case vc11 =>
      rename_i t' hp hag _ hx hz _ hzz
      obtain ⟨hL', hax, h12'⟩ := spill_res hpre hL hp hag rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      have hs : (canBeFreelyGenerated (sl s) || isSpilled (env s) (sl s)) = false := by
        rw [hfree, spill_of hax hx]; rfl
      have hn := cp_isNone (by rw [h12']; exact h12) hz
      cases hc : cp s with
      | none => rw [hc] at hn; cases hn
      | some c =>
        have h12c : t'.regs.r12.toBitVec = BitVec.ofNat 64 c := by rw [h12', h12, hc]; rfl
        have hfar := hf c hc
        cfg_goto
        · exact stack_of hL'.rsp
        · exact blocked_of hpre hL' (produce_err (emit_blocked hj hf hs hc)) h12c
            (far_val hL' hfar h12c) rfl rfl rfl
        · exact Or.inl (by simp only [V]; decide)
  case right.right.right.right.right.right.right.right.right.left t ht =>
    clear hcopy hspill hpush hdup
    kvcgen64
    all_goals bbu_norm at *
    obtain ⟨hB, hP⟩ := ht
    cfg_goto
    · exact stack_of hB.rsp
    · exact ⟨⟨hB.fm, hB.rsp⟩, by rw [hP]; rfl⟩
    · exact Or.inl (by simp only [V]; decide)
  case right.right.right.right.right.right.right.right.right.right t ht =>
    clear hcopy hspill hpush hdup
    kvcgen64
    all_goals bbu_norm at *
    obtain ⟨hB, hP⟩ := ht
    cfg_goto
    · exact stack_of hB.rsp
    · exact ⟨⟨hB.fm, hB.rsp⟩, by rw [hP]; rfl⟩
    · exact Or.inl (by simp only [V]; decide)

end Bbu
