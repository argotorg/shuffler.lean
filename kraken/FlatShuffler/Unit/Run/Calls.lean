module

public import FlatShuffler.Unit.Run.Return
import all FlatShuffler.Unit.Run.Return
public import FlatShuffler.Unit.Run.Load
import all FlatShuffler.Unit.Run.Load
public import FlatShuffler.Unit.RemoveSurplus
import all FlatShuffler.Unit.RemoveSurplus

@[expose] public section

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

set_option experimental.vcgen true

namespace FlatShuffler.Unit.RunU
open FlatShuffler.Sep

theorem surplus_pre {planned : Vector Word maxStackSize} {g : G} {t : MachineData}
    (hok : g.Ok) (hs : Safe planned (flat g) g.xo) : surplusA g t := by
  refine ⟨?_, hs.surplus.2⟩
  have hb := hs.surplus.1
  rw [Surplus.trace_len hok] at hb
  exact hb

theorem lowest_pre {planned : Vector Word maxStackSize} {g a : G} {t : MachineData}
    (hok : a.Ok) (hk : Keep g a) (hs : Safe planned (flat g) g.xo)
    (hm : Flat.removeSurplus (flat g) = (.done, flat a)) : lowestA planned a t := by
  have hd : (Flat.removeSurplus (flat g)).1 = .done := congrArg Prod.fst hm
  have ha := hs.lowest hd
  rw [hm] at ha
  refine ⟨?_, ha.2⟩
  have hb := ha.1
  rw [Surplus.trace_len hok] at hb
  change a.h.nops.toNat + 2 * a.h.len.toNat ≤ 6 * a.h.n.toNat + g.xo at hb
  simpa only [hk.xo] using hb

theorem take_frame (lo : List Word) (w x y z : Word) :
    (lo ++ [w, x, y, z]).take ((lo ++ [w, x, y, z]).length - 3) = lo ++ [w] := by
  simp only [List.length_append, List.length_cons, List.length_nil, Nat.reduceAdd]
  rw [show lo.length + 4 - 3 = lo.length + 1 by omega, List.take_append]
  simp
  exact List.take_of_length_le (by omega)

section
variable [Host] [FunDecls] (S PM : Addr) (planned : Vector Word maxStackSize)
    (g : G) (F : MProp 64) (s : MachineData) (ra : Int64)

theorem b_fn (hp : VPre (RunView PM planned) G.Ok S g F (runA planned) runD s)
    (lo : List Word) (w x y z : Word) (hl : lo.length = lowestD)
    (hk0 : Kg (RunView PM planned S g ∗ F) s ra (lo ++ [w, x, y, z]) (s.pushRa ra))
    (hout : ∀ l ∈ Program.labels runAsm, label l ≠ label "exit")
    (hsur : VSpecWithExit (RunView PM planned) G.Ok Names.removeSurplus surplusA 4
      surplusQ surplusX) :
    runAsm.ForallBlocks fun blk =>
      blk.label = .label Names.run → Obl S PM planned g F s ra blk := by
  simp only [Names.removeSurplus] at hsur
  cfg_block [Obl, Names.run]
  intro t ht
  simp only [Inv, Names.run, ↓reduceIte] at ht
  subst ht
  have hrdi : (s.pushRa ra).regs.rdi.toBitVec = S := hp.rdi
  have ⟨hpush, hm⟩ := hk0.pushes (xs := [(s.pushRa ra).regs.r12.toBitVec,
    (s.pushRa ra).regs.rbp.toBitVec, (s.pushRa ra).regs.rbx.toBitVec]) (by simp [hl])
  simp only [PushOk] at hpush
  obtain ⟨p0, p1, p2, -⟩ := hpush
  try symexec_norm at p0 p1 p2
  simp only [List.length_cons, List.length_nil] at hm
  rw [take_frame] at hm
  simp only [pushes, List.reverse_cons, List.reverse_nil, List.nil_append] at hm
  have hsp : (s.pushRa ra).regs.rsp.toBitVec - 8#64 - 8#64 - 8#64 =
      rsp s - 8#64 - 24#64 := by
    rw [← Reg64s.get64_rsp, hk0.sp64]
    bv_omega
  kvcgen64 [hsur]
  all_goals try symexec_norm at ⊢
  vc_by_shape
  | load => run_loads [p0, p1, p2]
  | other =>
    refine Bd.callWithExit (k := 4) (A := surplusA) (Q := surplusQ) (X := surplusX)
      (S := S) (PM := PM) (planned := planned) (g := g) (F := F)
      (s := s) (ra := ra) (lo := lo) (w := w) ?_ (by decide)
      hrdi hp.ok (surplus_pre hp.ok hp.args) ?_ (by
        intro tx hp harg
        apply ProofKit.intercept_exit (E := E S PM planned g F s ra) hout
        refine Or.inr ⟨rfl, harg, post_imp hp ?_⟩
        intro a hx
        change ExitRes Flat.removeSurplus g a at hx
        obtain ⟨hkeep, hf, hfail⟩ := hx
        have he := emission_surplus_fail (planned := planned) (l := zeroLocals)
          (by rw [hfail]; decide)
        refine ⟨zeroLocals, hkeep, ?_, ?_⟩
        · rw [he]; exact hf
        · rw [he]; exact hfail)
    · refine ⟨⟨?_, hsp⟩, hl, rfl, rfl, rfl⟩
      simpa only [fr, saved, List.append_assoc, List.singleton_append, MachineData.pushRa,
        Reg64s.set64_rsp, List.cons_append, List.nil_append] using hm
    · intro u a lo' w' hbd hq hok hag
      obtain ⟨⟨hkeep, hf, hal⟩, normalByte⟩ := hq
      have hbx : u.regs.rbp.toBitVec = S := by
        rw [mod_keep hag (by simp [Sep.mod]) Reg64s.get64_rbp]
        exact hrdi
      kvcgen64
      all_goals try symexec_norm
      vc_by_shape
      | goto ".LB.Emission.run.1" =>
        have hd := code_eq_zero (hal.symm.trans (al_zero (by
          rw [Bool.not_eq_false']; with_reducible assumption)))
        have hres : Flat.removeSurplus (flat g) = (.done, flat a) := Prod.ext hd hf.symm
        cfg_goto
        · exact (hbd.kb.next rfl rfl).stack (by decide)
        · simp only [Inv, Names.run, String.reduceEq, ↓reduceIte]
          refine ⟨a, lo', w', ?_, hbx, hok, hkeep, hres⟩
          apply hbd.next <;> rfl
        · simp [V, Names.run]
      | other =>
        have hd := code_ne_zero (fun he => al_ne (by
          rw [Bool.not_eq_true']; with_reducible assumption) (hal.trans he))
        have he := emission_surplus_fail (planned := planned) (l := zeroLocals) hd
        first
        | (left; simp [V, Names.run])
        | (simp only [Inv, Names.run, String.reduceEq, ↓reduceIte]
           refine ⟨a, lo', w', ?_, hok, ⟨zeroLocals, hkeep, ?_, ?_⟩, normalByte⟩
           · apply hbd.next <;> rfl
           · rw [he]; exact hf
           · rw [he]; exact hal)

end
end FlatShuffler.Unit.RunU
