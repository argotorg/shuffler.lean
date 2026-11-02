module

public import FlatShuffler.Sep.View
import all FlatShuffler.Sep.View

@[expose] public section

/-!
# Contracts with separation atoms

The contract shape for the state weakest precondition (`Program.WP.cfg`, `CallSpec`). The memory
part of each assertion is one `(View S g ∗ Stk sp fr v ∗ F).get m`, and the frame `F` is a
parameter. `Kp` is a state inside a body: it holds the memory assertion and the registers that the
body must give back.
-/

open Std.WP Lean.Order
open scoped Program.WP

namespace FlatShuffler.Sep

/-! ## The stack -/

-- The stack below `sp`: the return address slot `v` at `sp - 8`, and the free words `fr` under it.
-- A function with `d` free words can call a function with `d - 1` free words (`Stk.call`).
def Stk (sp : Addr) (fr : List Word) (v : Word) : MProp 64 :=
  Arr (sp - 8#64 - BitVec.ofNat 64 (8 * fr.length)) fr ∗ Wd (sp - 8#64) v

-- A call takes the top free word for the return address of the callee.
theorem Stk.call (sp : Addr) (fr : List Word) (w v : Word) (F : MProp 64) :
    Stk sp (fr ++ [w]) v ∗ F = Stk (sp - 8#64) fr w ∗ (Wd (sp - 8#64) v ∗ F) := by
  have e1 : sp - 8#64 - BitVec.ofNat 64 (8 * (fr ++ [w]).length)
      = sp - 8#64 - 8#64 - BitVec.ofNat 64 (8 * fr.length) := by
    simp only [List.length_append, List.length_cons, List.length_nil]
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub]; omega
  have e2 : sp - 8#64 - 8#64 - BitVec.ofNat 64 (8 * fr.length) + BitVec.ofNat 64 (8 * fr.length)
      = sp - 8#64 - 8#64 := BitVec.sub_add_cancel _ _
  unfold Stk
  rw [e1, Arr.append, e2]
  simp only [Arr, MProp.sep_emp, MProp.sep_assoc]

-- One free word as an atom: a `pushq` stores to it.
theorem Stk.top_eq (sp : Addr) (x v : Word) (P F : MProp 64) :
    P ∗ Stk sp [x] v ∗ F = Wd (sp - 8#64 - 8#64) x ∗ (P ∗ Wd (sp - 8#64) v ∗ F) := by
  unfold Stk
  simp only [Arr, MProp.sep_emp, List.length_cons, List.length_nil, Nat.zero_add, Nat.mul_one]
  ecancel

/-! ## Contracts -/

-- The registers that a callee can change. The memory part is all of memory:
-- the `∗` assertion of the postcondition gives what the callee keeps.
def mod : Modifies := ⟨[.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11], [(0#64, 2 ^ 64)]⟩

theorem mod_mem (s t : MachineData) : Mem.UnchangedOutside mod.mem s.dmem t.dmem :=
  fun b hb => absurd (Or.inl (by have := b.isLt; simp; omega)) hb

-- The precondition: `rdi` is the struct, the struct and the stack hold `g`, the
-- stack below `rsp` (`d` free words and the return slot) is owned, `F` is the rest.
structure Pre (S : Addr) (g : G) (F : MProp 64) (A : G → MachineData → Prop) (d : Nat) (s : MachineData) : Prop where
  rdi : rdi s = S
  ok : g.Ok
  mem : ∃ fr v, fr.length = d ∧ (View S g ∗ Stk (rsp s) fr v ∗ F).get s.dmem
  args : A g s

-- The postcondition: a new ghost `g'` with the result `Q`, the same stack size, the same `F`.
def Post (S : Addr) (F : MProp 64) (d : Nat) (Q : G → MachineData → Prop) (s t : MachineData) : Prop :=
  ∃ g' fr v, Q g' t ∧ g'.Ok ∧ fr.length = d
    ∧ (View S g' ∗ Stk (rsp s) fr v ∗ F).get t.dmem

-- The body triple.
abbrev Body [Host] [FunDecls] (prog : Program) (pre : MachineData → Prop)
    (post : MachineData → MachineData → Prop) : Prop :=
  ∀ s ra, ⦃ fun t => t = s.pushRa ra ∧ pre s ⦄ prog
    ⦃ (fun _ _ => False); fun a t => a = ra ∧ post s t ∧ mod.Agree s t ⦄

-- The call rule: the caller gives the ghost and the frame at the call.
abbrev Spec [Host] [FunDecls] (f : Label) (A : G → MachineData → Prop) (d : Nat)
    (Q : G → G → MachineData → MachineData → Prop) : Prop :=
  ∀ asz osz (K : Unit → MachineData → Prop) (E : Int64 → MachineData → Prop),
    ⦃ fun s => ∃ S g F, Pre S g F A d s
        ∧ ∀ s', Post S F d (fun g' t => Q g g' s t) s s' → mod.Agree s s' → K () s' ⦄
      (Directive.instr (.regular asz osz (.call (.rel (.sub (.label f) .after_current_instruction)))))
    ⦃ K; E ⦄

theorem Pre.isSome {S : Addr} {g : G} {F : MProp 64} {A : G → MachineData → Prop} {d : Nat} {s : MachineData}
    (h : Pre S g F A d s) : (s.dmem.loadInt (s.regs.get64 .rsp - 8#64) 8).isSome = true := by
  obtain ⟨fr, v, -, hm⟩ := h.mem
  obtain ⟨R, e⟩ : ∃ R, View S g ∗ Stk (rsp s) fr v ∗ F = Wd (rsp s - 8#64) v ∗ R :=
    ⟨_, by unfold Stk; ecancel⟩
  exact Wd.isSome (e ▸ hm)

-- A body for each ghost and frame gives the call rule.
theorem spec_of_body [Host] [FunDecls] {f : Label} {g₀ : Fragment} (hg : FunDecls.at (label f) = some g₀)
    {A : G → MachineData → Prop} {d : Nat} {Q : G → G → MachineData → MachineData → Prop}
    (hb : ∀ S g F, Body g₀.prog (Pre S g F A d) (fun s t => Post S F d (fun g' t => Q g g' s t) s t)) :
    Spec f A d Q := by
  intro asz osz K E
  refine ⟨fun s ⟨S, g, F, hp, hk⟩ => ?_⟩
  exact (Program.WP.callSpec_of_triple hg (hb S g F) asz osz K E).1 s ⟨hp.isSome, hp, hk⟩

/-! ## A callee that owns a part of the frame -/

-- `n` words from `a` with any values: an array argument that the callee can write.
def ExArr (a : Addr) (n : Nat) : MProp 64 :=
  MProp.mk fun m => ∃ vs : List Word, vs.length = n ∧ (Arr a vs).get m

theorem ExArr.intro {a : Addr} {vs : List Word} {n : Nat} {P : MProp 64} {m : Mem 64}
    (hn : vs.length = n) (h : (Arr a vs ∗ P).get m) : (ExArr a n ∗ P).get m := by
  rw [MProp.sep_comm] at h ⊢
  exact (MProp.le_def _ _).mp (MProp.sep_mono_right P (MProp.le_mk_of fun _ h' => ⟨vs, hn, h'⟩)) m h

theorem ExArr.elim {a : Addr} {n : Nat} {P : MProp 64} {m : Mem 64}
    (h : (ExArr a n ∗ P).get m) : ∃ vs : List Word, vs.length = n ∧ (Arr a vs ∗ P).get m := by
  obtain ⟨m₁, m₂, hu, hi, h₁, h₂⟩ := (MProp.get_sep_apply_iff _ _ _).mp h
  obtain ⟨vs, hn, h₁⟩ : ∃ vs : List Word, vs.length = n ∧ (Arr a vs).get m₁ := by
    unfold ExArr at h₁; simpa using h₁
  exact ⟨vs, hn, (MProp.get_sep_apply_iff _ _ _).mpr ⟨m₁, m₂, hu, hi, h₁, h₂⟩⟩

-- The call rule of a callee that owns `W s ∗ F` (`W s` is a part that the callee reads or
-- writes, for example an array at an argument register).
abbrev SpecW [Host] [FunDecls] (f : Label) (W : MachineData → MProp 64)
    (A : G → MachineData → Prop) (d : Nat) (Q : G → G → MachineData → MachineData → Prop) : Prop :=
  ∀ asz osz (K : Unit → MachineData → Prop) (E : Int64 → MachineData → Prop),
    ⦃ fun s => ∃ S g F, Pre S g (W s ∗ F) A d s
        ∧ ∀ s', Post S (W s ∗ F) d (fun g' t => Q g g' s t) s s' → mod.Agree s s' → K () s' ⦄
      (Directive.instr (.regular asz osz (.call (.rel (.sub (.label f) .after_current_instruction)))))
    ⦃ K; E ⦄

theorem spec_of_bodyW [Host] [FunDecls] {f : Label} {g₀ : Fragment}
    (hg : FunDecls.at (label f) = some g₀) {W : MachineData → MProp 64}
    {A : G → MachineData → Prop} {d : Nat} {Q : G → G → MachineData → MachineData → Prop}
    (hb : ∀ S g F, Body g₀.prog (fun s => Pre S g (W s ∗ F) A d s)
      (fun s t => Post S (W s ∗ F) d (fun g' t => Q g g' s t) s t)) :
    SpecW f W A d Q := by
  intro asz osz K E
  refine ⟨fun s ⟨S, g, F, hp, hk⟩ => ?_⟩
  exact (Program.WP.callSpec_of_triple hg (hb S g F) asz osz K E).1 s ⟨hp.isSome, hp, hk⟩

/-! ## A body state -/

-- A state inside a body: the memory holds `g`, the free words `fr`, the return
-- address and `F`; `rsp` and the callee-saved registers are those after the call.
structure Kp (S : Addr) (g : G) (F : MProp 64) (s : MachineData) (ra : Int64) (fr : List Word)
    (t : MachineData) : Prop where
  mem : (View S g ∗ Stk (rsp s) fr ra.toBitVec ∗ F).get t.dmem
  sp : t.regs.rsp = (s.pushRa ra).regs.rsp
  bx : t.regs.rbx = s.regs.rbx
  bp : t.regs.rbp = s.regs.rbp
  r12 : t.regs.r12 = s.regs.r12
  r13 : t.regs.r13 = s.regs.r13
  r14 : t.regs.r14 = s.regs.r14
  r15 : t.regs.r15 = s.regs.r15

section
variable {S : Addr} {g : G} {F : MProp 64} {s t : MachineData} {ra : Int64}
  {fr : List Word}

theorem Kp.init {v : Word} (h : (View S g ∗ Stk (rsp s) fr v ∗ F).get s.dmem) :
    Kp S g F s ra fr (s.pushRa ra) := by
  have e1 : View S g ∗ Stk (rsp s) fr v ∗ F
      = Wd (rsp s - 8#64) v ∗ (View S g ∗ Arr (rsp s - 8#64 - BitVec.ofNat 64 (8 * fr.length)) fr ∗ F) := by
    unfold Stk; ecancel
  have e2 : View S g ∗ Stk (rsp s) fr ra.toBitVec ∗ F
      = Wd (rsp s - 8#64) ra.toBitVec ∗ (View S g ∗ Arr (rsp s - 8#64 - BitVec.ofNat 64 (8 * fr.length)) fr ∗ F) := by
    unfold Stk; ecancel
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  rw [e2]
  exact Wd.store (e1 ▸ h) ra.toBitVec

theorem Kp.next {t' : MachineData} (h : Kp S g F s ra fr t) (hm : t'.dmem = t.dmem)
    (hsp : t'.regs.rsp = t.regs.rsp) (hbx : t'.regs.rbx = t.regs.rbx)
    (hbp : t'.regs.rbp = t.regs.rbp) (h12 : t'.regs.r12 = t.regs.r12)
    (h13 : t'.regs.r13 = t.regs.r13) (h14 : t'.regs.r14 = t.regs.r14)
    (h15 : t'.regs.r15 = t.regs.r15) : Kp S g F s ra fr t' :=
  ⟨hm ▸ h.mem, hsp.trans h.sp, hbx.trans h.bx, hbp.trans h.bp, h12.trans h.r12,
    h13.trans h.r13, h14.trans h.r14, h15.trans h.r15⟩

theorem Kp.sp64 (h : Kp S g F s ra fr t) : t.regs.get64 .rsp = rsp s - 8#64 := by
  rw [Reg64s.get64_rsp, h.sp]; rfl

theorem Kp.retAddr (h : Kp S g F s ra fr t) : t.retAddr = some ra := by
  obtain ⟨R, e⟩ : ∃ R, View S g ∗ Stk (rsp s) fr ra.toBitVec ∗ F
      = Wd (rsp s - 8#64) ra.toBitVec ∗ R := ⟨_, by unfold Stk; ecancel⟩
  rw [MachineData.retAddr, h.sp64, Wd.retAddr (e ▸ h.mem), Int64.ofBitVec_toBitVec]

theorem Kp.stack (h : Kp S g F s ra fr t) : t.StackAtOrBelow (s.pushRa ra) :=
  MachineData.stackAtOrBelow_of_toNat_lt (by simp [h.sp])

-- `ret` from a body in state `t` with result `Q g t` gives the postcondition.
theorem Kp.ret [Host] {Q : G → MachineData → Prop} {ls : List Label} {d : Nat}
    {I' : CfgLabel → Nat → Unit → MachineData → Prop} (h : Kp S g F s ra fr t) (hd : fr.length = d)
    (hok : g.Ok) (hQ : ∀ t', t'.dmem = t.dmem → rax t' = rax t → Q g t') :
    Program.Intercept ls (s.pushRa ra) I'
      (fun a t' => a = ra ∧ Post S F d Q s t' ∧ mod.Agree s t') t.retAddr.get!
      { regs := t.regs.set64 Reg64.rsp (t.regs.get64 Reg64.rsp + 8#64), zmms := t.zmms,
        status := t.status, dmem := t.dmem } := by
  have hsp : t.regs.get64 .rsp + 8#64 = rsp s := by rw [h.sp64]; exact BitVec.sub_add_cancel _ _
  refine Or.inr ⟨⟨by simp [h.retAddr], ⟨g, fr, ra.toBitVec, hQ _ rfl (by simp [rax]), hok, hd, h.mem⟩,
    fun q hq => ?_, mod_mem _ _⟩, fun _ _ _ => ?_⟩
  · simp only [Reg64s.get64_set64]
    split
    · next he => subst he; exact hsp
    · have hb := h.bx; have hp := h.bp; have h2 := h.r12; have h3 := h.r13; have h4 := h.r14
      have h5 := h.r15
      cases q <;> simp_all [mod, Reg64s.get64_rbx, Reg64s.get64_rbp, Reg64s.get64_r12,
        Reg64s.get64_r13, Reg64s.get64_r14, Reg64s.get64_r15]
  · apply MachineData.stackBelow_of_add_eight
    simp only [MachineData.pushRa, Reg64s.get64_set64, reduceIte]
    rw [hsp]; exact BitVec.sub_add_cancel _ _

-- A register that `mod` does not list has the same value after a call.
theorem mod_keep {c t : MachineData} (hag : mod.Agree c t) {q : Reg64} (hq : q ∉ mod.regs)
    {f : Reg64s → UInt64} (hf : ∀ r : Reg64s, r.get64 q = (f r).toBitVec) : f t.regs = f c.regs :=
  UInt64.toBitVec_inj.mp (by simpa [hf] using hag.1 q hq)

-- After a call: the callee kept the stack pointer and the callee-saved registers.
theorem Kp.agree {g' : G} {c : MachineData} {fr' : List Word} (h : Kp S g F s ra fr c)
    (hag : mod.Agree c t) (hm : (View S g' ∗ Stk (rsp s) fr' ra.toBitVec ∗ F).get t.dmem) :
    Kp S g' F s ra fr' t :=
  ⟨hm, (mod_keep hag (by simp [mod]) Reg64s.get64_rsp).trans h.sp,
    (mod_keep hag (by simp [mod]) Reg64s.get64_rbx).trans h.bx,
    (mod_keep hag (by simp [mod]) Reg64s.get64_rbp).trans h.bp,
    (mod_keep hag (by simp [mod]) Reg64s.get64_r12).trans h.r12,
    (mod_keep hag (by simp [mod]) Reg64s.get64_r13).trans h.r13,
    (mod_keep hag (by simp [mod]) Reg64s.get64_r14).trans h.r14,
    (mod_keep hag (by simp [mod]) Reg64s.get64_r15).trans h.r15⟩

-- Forget the values of an array in the frame.
theorem Kp.exArr {a : Addr} {vs : List Word} {n : Nat} (h : Kp S g (Arr a vs ∗ F) s ra fr t)
    (hn : vs.length = n) : Kp S g (ExArr a n ∗ F) s ra fr t := by
  have e : ∀ X : MProp 64, View S g ∗ Stk (rsp s) fr ra.toBitVec ∗ (X ∗ F)
      = X ∗ (View S g ∗ Stk (rsp s) fr ra.toBitVec ∗ F) := fun X => by ac_rfl
  have hm := h.mem
  rw [e] at hm
  exact ⟨by rw [e]; exact ExArr.intro hn hm, h.sp, h.bx, h.bp, h.r12, h.r13, h.r14, h.r15⟩

end

end FlatShuffler.Sep
