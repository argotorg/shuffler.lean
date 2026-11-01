module

public import BbuKraken.Sep.Contract
import all BbuKraken.Sep.Contract
public import BbuKraken.Sep.Stores
import all BbuKraken.Sep.Stores
public import ProofKit.Cfg
import all ProofKit.Cfg
public import Kraken.X64.Parser
import all Kraken.X64.Parser

@[expose] public section

/-!
Tests of the contract: a body that pushes and pops a callee-saved register (`rbx_t`, one free stack
word), and a caller that calls it through its `Spec` (`cal`, two free stack words).
-/

open Std.WP Lean.Order
open scoped Program.WP
open Kraken.X64.Parser
open ProofKit

set_option experimental.vcgen true

namespace Bbu.Sep.ContractTest

open Bbu.Sep

/-! ## A pushed callee-saved register -/

def rbxAsm : Program := parse("
rbx_t:
  pushq %rbx
  movq %rdi, %rbx
  movq 32(%rbx), %rax
  popq %rbx
  ret
")

theorem rbx_body [Host] [FunDecls] (S : Addr) (g : G) (F : MProp 64) :
    Body rbxAsm (Pre S g F (fun _ _ => True) 1)
      (fun s t => Post S F 1 (fun g' t => g' = g ∧ rax t = g.h.len) s t) := by
  intro s ra
  refine ⟨fun s₀ ⟨h₀, hpre⟩ => ?_⟩
  subst h₀
  obtain ⟨fr, v, hfr, hm⟩ := hpre.mem
  match fr, hfr with
  | [x], _ =>
  have hk0 : Kp S g F s ra [x] (s.pushRa ra) := Kp.init hm
  have h0 := Stk.top_eq (rsp s) x ra.toBitVec (View S g) F ▸ hk0.mem
  have h1 := Wd.store h0 s.regs.rbx.toBitVec
  have hk1 := (Stk.top_eq (rsp s) s.regs.rbx.toBitVec ra.toBitVec (View S g) F).symm ▸ h1
  have hdi : (s.pushRa ra).regs.rdi.toBitVec + 32#64 = Fld.stack_size S := by
    rw [show (s.pushRa ra).regs.rdi.toBitVec = S by simpa [MachineData.pushRa] using hpre.rdi]; rfl
  have hk5 : Kp S g F s ra [s.regs.rbx.toBitVec] { (s.pushRa ra) with
      regs := { (s.pushRa ra).regs with
        rax := ⟨BitVec.ofInt 64 ((Mem.storeInt (s.pushRa ra).dmem ((s.pushRa ra).regs.rsp.toBitVec - 8#64) 8
          (s.pushRa ra).regs.rbx.toBitVec.toInt).loadInt ((s.pushRa ra).regs.rdi.toBitVec + 32#64) 8).get!⟩
        rbx := ⟨BitVec.ofInt 64 ((Mem.storeInt (s.pushRa ra).dmem ((s.pushRa ra).regs.rsp.toBitVec - 8#64) 8
          (s.pushRa ra).regs.rbx.toBitVec.toInt).loadInt ((s.pushRa ra).regs.rsp.toBitVec - 8#64) 8).get!⟩
        rsp := ⟨(s.pushRa ra).regs.rsp.toBitVec - 8#64 + 8#64⟩ }
      dmem := Mem.storeInt (s.pushRa ra).dmem ((s.pushRa ra).regs.rsp.toBitVec - 8#64) 8
        (s.pushRa ra).regs.rbx.toBitVec.toInt } :=
    ⟨hk1, by simp, UInt64.toBitVec_inj.mp (Wd.rd h1), rfl, rfl, rfl, rfl, rfl⟩
  refine Program.WP.cfg (fun
      | .entry, t | .label "rbx_t", t => t = s.pushRa ra
      | _, _ => False)
    (fun | _, _ => 0) ?_ rfl
  cfg_blocks
  case entry t ht =>
    subst ht; kvcgen64
  case rbx_t t ht =>
    subst ht
    kvcgen64
    all_goals try symexec_norm
    case vc1 => exact Wd.isSome h0
    case vc2 => rw [hdi]; exact View.isSome_len hk1
    case vc3 => exact Wd.isSome h1
    case vc4 => exact Option.isSome_iff_exists.mpr ⟨ra, hk5.retAddr⟩
    case vc5 =>
      refine Kp.ret hk5 rfl hpre.ok fun t' _ hr => ⟨rfl, hr.trans ?_⟩
      show rd _ ((s.pushRa ra).regs.rdi.toBitVec + 32#64) = _
      rw [hdi]; exact View.rd_len hk1

/-! ## A call through a `Spec` -/

def calAsm : Program := parse("
cal:
  call rbx_t
  ret
")

-- The result of `rbx_t`: the same ghost, and `rax` is the stack size.
abbrev rbxQ : G → G → MachineData → MachineData → Prop := fun g g' _ t => g' = g ∧ rax t = g.h.len

-- `cal` gives the top free word to `rbx_t` for its return address, and the other free word as the
-- free word of `rbx_t`. The frame of `rbx_t` is the return address of `cal` and `F`.
theorem cal_body [Host] [FunDecls] (hrbx : Spec "rbx_t" (fun _ _ => True) 1 rbxQ) (S : Addr) (g : G)
    (F : MProp 64) :
    Body calAsm (Pre S g F (fun _ _ => True) 2)
      (fun s t => Post S F 2 (fun g' t => rbxQ g g' s t) s t) := by
  intro s ra
  refine ⟨fun s₀ ⟨h₀, hpre⟩ => ?_⟩
  subst h₀
  obtain ⟨fr, v, hfr, hm⟩ := hpre.mem
  obtain ⟨x, w, rfl⟩ : ∃ x w, fr = [x, w] := by
    match fr, hfr with
    | [x, w], _ => exact ⟨x, w, rfl⟩
  have hk0 : Kp S g F s ra [x, w] (s.pushRa ra) := Kp.init hm
  have hcall : ∀ (g' : G) (x' v' : Word),
      View S g' ∗ Stk (rsp s) [x', v'] ra.toBitVec ∗ F
        = View S g' ∗ Stk (rsp (s.pushRa ra)) [x'] v' ∗ (Wd (rsp s - 8#64) ra.toBitVec ∗ F) := by
    intro g' x' v'
    rw [show rsp (s.pushRa ra) = rsp s - 8#64 from hk0.sp64]
    exact congrArg _ (Stk.call (rsp s) [x'] v' ra.toBitVec F)
  refine Program.WP.cfg (fun
      | .entry, t | .label "cal", t => t = s.pushRa ra
      | _, _ => False)
    (fun | _, _ => 0) ?_ rfl
  cfg_blocks
  case entry t ht =>
    subst ht; kvcgen64
  case cal t ht =>
    subst ht
    kvcgen64 [hrbx]
    -- The call: give the callee its ghost, its stack and its frame.
    refine ⟨S, g, Wd (rsp s - 8#64) ra.toBitVec ∗ F,
      ⟨by simp [MachineData.pushRa]; exact hpre.rdi, hpre.ok,
        ⟨[x], w, rfl, by rw [← hcall g x w]; exact hk0.mem⟩, trivial⟩, fun s' hpost hag => ?_⟩
    -- The return: take back the ghost and the stack.
    obtain ⟨g', fr', v', ⟨hg, hax⟩, hok, hfr', hm'⟩ := hpost
    subst hg
    obtain ⟨x', rfl⟩ : ∃ x', fr' = [x'] := by
      match fr', hfr' with
      | [x'], _ => exact ⟨x', rfl⟩
    have hk : Kp S g' F s ra [x', v'] s' := Kp.agree hk0 hag (by rw [hcall]; exact hm')
    kvcgen64
    · simp [hk.retAddr]
    · exact Kp.ret hk rfl hok fun t' _ hr => ⟨rfl, hr.trans hax⟩

/-! ## `ExArr` -/

-- A store into an owned array keeps the ownership.
example {a : Addr} {n i : Nat} {P : MProp 64} {m : Mem 64} (h : (ExArr a n ∗ P).get m)
    (hi : i < n) (w : Word) :
    (ExArr a n ∗ P).get (m.storeInt (a + BitVec.ofNat 64 (8 * i)) 8 w.toInt) := by
  obtain ⟨vs, hn, h⟩ := ExArr.elim h
  exact ExArr.intro (by simpa using hn) (Arr.store h (hn ▸ hi) w)

-- Every word below `n` is loadable.
example {a : Addr} {n i : Nat} {P : MProp 64} {m : Mem 64} (h : (ExArr a n ∗ P).get m)
    (hi : i < n) : (m.loadInt (a + BitVec.ofNat 64 (8 * i)) 8).isSome = true := by
  obtain ⟨vs, hn, h⟩ := ExArr.elim h
  exact Arr.isSome h (hn ▸ hi)

-- `elim` after `intro` gives an array of the same length, with the same values below it.
example {a : Addr} {vs : List Word} {P : MProp 64} {m : Mem 64} (h : (Arr a vs ∗ P).get m)
    {i : Nat} (hi : i < vs.length) :
    ∃ ws : List Word, ws.length = vs.length ∧ ∃ hw : i < ws.length, ws[i] = vs[i] := by
  obtain ⟨ws, hn, h'⟩ := ExArr.elim (ExArr.intro rfl h)
  exact ⟨ws, hn, hn ▸ hi, by rw [← Arr.rd h' (hn ▸ hi), Arr.rd h hi]⟩

-- The empty array owns no word.
example {a : Addr} {P : MProp 64} {m : Mem 64} (h : P.get m) : (ExArr a 0 ∗ P).get m :=
  ExArr.intro (vs := []) rfl (by simpa [Arr, MProp.emp_sep] using h)

end Bbu.Sep.ContractTest
