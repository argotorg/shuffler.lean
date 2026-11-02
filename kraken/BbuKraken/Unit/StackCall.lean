module

public import BbuKraken.Unit.ExitDefs
import all BbuKraken.Unit.ExitDefs

@[expose] public section

open Std.WP Lean.Order
open scoped Program.WP

namespace Bbu.Sep

theorem Stk.frame (P : MProp 64) (sp : Addr) (fr : List Word) (v : Word) (F : MProp 64) :
    P ∗ Stk sp fr v ∗ F =
      P ∗ Stk sp [] v ∗ (Arr (sp - 8#64 - BitVec.ofNat 64 (8 * fr.length)) fr ∗ F) := by
  unfold Stk
  simp only [Arr, MProp.emp_sep]
  ecancel

theorem Post.imp {S : Addr} {F : MProp 64} {d : Nat} {s t : MachineData}
    {Q R : G → MachineData → Prop} (hp : Post S F d Q s t)
    (h : ∀ g', Q g' t → R g' t) : Post S F d R s t := by
  obtain ⟨g', fr, v, hQ, hok, hlen, hm⟩ := hp
  exact ⟨g', fr, v, h g' hQ, hok, hlen, hm⟩

/-- A callee that needs no free stack words keeps the caller's free words in its frame. -/
theorem Spec.with_free [Host] [FunDecls] {f : Label} {A : G → MachineData → Prop}
    {Q : G → G → MachineData → MachineData → Prop} (h : Spec f A 0 Q) (d : Nat) :
    Spec f A d Q := by
  intro asz osz K E
  refine ⟨fun s ⟨S, g, F, hp, hk⟩ => ?_⟩
  obtain ⟨fr, v, hlen, hm⟩ := hp.mem
  apply (h asz osz K E).1 s
  refine ⟨S, g, Arr (rsp s - 8#64 - BitVec.ofNat 64 (8 * fr.length)) fr ∗ F,
    ⟨hp.rdi, hp.ok, ⟨[], v, rfl, ?_⟩, hp.args⟩, ?_⟩
  · rw [Stk.frame] at hm
    exact hm
  intro t ⟨g', fr', v', hQ, hok, hlen', hm'⟩ hag
  obtain rfl := List.eq_nil_of_length_eq_zero hlen'
  apply hk t ⟨g', fr, v', hQ, hok, hlen, ?_⟩ hag
  rw [Stk.frame]
  exact hm'

/-- Lower stack words stay in the frame of a callee. -/
theorem Stk.frame_below (sp : Addr) (lo hi : List Word) (v : Word) (P F : MProp 64) :
    P ∗ Stk sp (lo ++ hi) v ∗ F =
      P ∗ Stk sp hi v ∗
        (Arr (sp - 8#64 - BitVec.ofNat 64 (8 * (lo.length + hi.length))) lo ∗ F) := by
  unfold Stk
  rw [List.length_append, Arr.append]
  have ha : sp - 8#64 - BitVec.ofNat 64 (8 * (lo.length + hi.length)) +
      BitVec.ofNat 64 (8 * lo.length) = sp - 8#64 - BitVec.ofNat 64 (8 * hi.length) := by
    rw [Nat.mul_add, BitVec.ofNat_add]
    bv_omega
  rw [ha]
  ac_rfl

/-- A callee keeps the additional lower words on both return and exit. -/
theorem SpecWithExit.with_free [Host] [FunDecls] {f : Label} {A : G → MachineData → Prop}
    {d : Nat} {Q X : G → G → MachineData → MachineData → Prop}
    (h : SpecWithExit f A d Q X) (k : Nat) : SpecWithExit f A (k + d) Q X := by
  intro asz osz K E
  refine ⟨fun s ⟨S, g, F, hp, hn, hx⟩ => ?_⟩
  obtain ⟨fr, v, hlen, hm⟩ := hp.mem
  let lo := fr.take k
  let hi := fr.drop k
  have hlo : lo.length = k := by dsimp [lo]; simp only [List.length_take]; omega
  have hhi : hi.length = d := by dsimp [hi]; simp only [List.length_drop]; omega
  have heq : fr = lo ++ hi := (List.take_append_drop k fr).symm
  rw [heq, Stk.frame_below] at hm
  apply (h asz osz K E).1 s
  refine ⟨S, g, Arr (rsp s - 8#64 - BitVec.ofNat 64 (8 * (lo.length + hi.length))) lo ∗ F,
    ⟨hp.rdi, hp.ok, ⟨hi, v, hhi, hm⟩, hp.args⟩, ?_, ?_⟩
  · intro t ⟨g', fr', v', hQ, hok, hlen', hm'⟩ hag
    apply hn t ⟨g', lo ++ fr', v', hQ, hok, by simp [hlo, hlen'], ?_⟩ hag
    rw [Stk.frame_below]
    simpa only [hhi, hlen'] using hm'
  · intro t ⟨g', fr', v', hX, hok, hlen', hm'⟩ harg
    apply hx t ⟨g', lo ++ fr', v', hX, hok, by simp [hlo, hlen'], ?_⟩ harg
    rw [Stk.frame_below]
    simpa only [hhi, hlen'] using hm'

end Bbu.Sep

namespace ProofKit

theorem intercept_exit [Host] {ls : List Label} {s₀ t : MachineData}
    {I : CfgLabel → Nat → Unit → MachineData → Prop}
    {E : Int64 → MachineData → Prop}
    (hout : ∀ l ∈ ls, label l ≠ label "exit") (he : E (label "exit") t) :
    Program.Intercept ls s₀ I E (label "exit") t :=
  Or.inr ⟨he, fun l hl ha => False.elim (hout l hl ha)⟩

end ProofKit
