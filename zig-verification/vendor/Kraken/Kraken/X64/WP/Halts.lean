module

public import Kraken.X64.WP.Spec

/-!
# Halt labels

A halt label names a function that a proof does not enter, for example one that throws. It has no
fragment in `FunDecls`, so a call to it takes the `jump` path of `Executable.StepOut`, and
`Program.ContinueOnInternalExit` gives it to the exit continuation: the proof ends there.

A `funspec` postcondition tells a return from an exit by `a = ra`. For a halt exit to be an exit,
`ra` must not be a halt address, and for it to leave each fragment on the way out, no label of a
fragment can have a halt address. `Halts H` states these two facts about the layout.
`Halts.of_stubs` proves them when the program starts with a stub for each halt label.
-/

open Std.WP
open Lean.Order

@[expose] public section

/-- No return address, and no label outside `H`, has the address of a label in `H`. -/
class Halts [Host] (H : outParam (List Label)) : Prop where
  ret_not_mem : ∀ k asz osz t, Host.prog[k]? = some (.instr (.regular asz osz (.call t))) →
    Host.addrOf (k + 1) ∉ H.map label
  prog_label_not_mem : ∀ l ∈ Host.prog.labels, l ∉ H → label l ∉ H.map label

theorem Halts.label_not_mem [Host] {H : List Label} [Halts H] {p : Program} [hp : Embeds p]
    {l : Label} (hl : l ∈ p.labels := by decide) (hn : l ∉ H := by decide) :
    label l ∉ H.map label := by
  refine Halts.prog_label_not_mem l ?_ hn
  obtain ⟨_, hk⟩ := hp.embedding.isInfixAt
  simp only [Program.labels, List.mem_filterMap] at hl ⊢
  obtain ⟨d, hd, e⟩ := hl
  exact ⟨d, List.mem_of_mem_drop (hk ▸ List.mem_append_left _ hd), e⟩

/-- One stub for each halt label: the label, then `ud2`. -/
def haltStubs : List Label → Program
  | [] => []
  | l :: H => .label l :: .instr (.regular .W64 .W64 .ud2) :: haltStubs H

/-- A label followed by an instruction of positive size has an address other than that of each
directive two or more places after it. -/
theorem Host.addrOf_ne_label [Host] {j k : Nat} {l : Label} {ins : Instr}
    (hl : Host.prog[j]? = some (.label l)) (hi : Host.prog[j + 1]? = some (.instr ins))
    (hpad : ¬ ins.IsPadding) (hk : j + 2 ≤ k) : Host.addrOf k ≠ label l := by
  rw [Host.label_eq (p := Host.prog) (k := 0) (List.prefix_refl _) (by simpa using hl),
    Nat.zero_add]
  intro h
  have hc : Host.exe.program[j + 1]? =
      some {directive := .instr ins, size := Kraken.Layout.size Directive (j + 1)} := by
    rw [Host.exe_getElem?, hi]
    rfl
  have : Host.exe.sizeBefore (j + 2) = Host.exe.sizeBefore (j + 1) + Kraken.Layout.size Directive (j + 1) :=
    Host.exe.sizeBefore_succ hc
  have := Host.exe.sizeBefore_mono (show j ≤ j + 1 by omega)
  have := Host.exe.sizeBefore_mono (show j + 2 ≤ k by omega)
  have := Host.instr_size_pos (j + 1) _ hi hpad
  have := Host.sizeBefore_eq_of_addrOf_eq h
  omega

theorem haltStubs_length (H : List Label) : (haltStubs H).length = 2 * H.length := by
  induction H with
  | nil => rfl
  | cons _ _ ih => simp only [haltStubs, List.length_cons, ih]; omega

/-- The directives at index `j + 2 * H.length` or later have no halt address. -/
theorem haltStubs_addrOf_not_mem [Host] {H : List Label} {j : Nat}
    (hs : (haltStubs H).IsInfixAt Host.prog j) {k : Nat} (hk : j + 2 * H.length ≤ k) :
    Host.addrOf k ∉ H.map label := by
  induction H generalizing j with
  | nil => simp
  | cons l H ih =>
    obtain ⟨h0, hs⟩ := hs.cons
    obtain ⟨h1, hs⟩ := hs.cons
    simp only [List.length_cons] at hk
    simp only [List.map_cons, List.mem_cons, not_or]
    exact ⟨Host.addrOf_ne_label h0 h1 (by nofun) (by omega), ih hs (by omega)⟩

/-- The stubs hold only labels of `H` and `ud2`. -/
theorem haltStubs_getElem? {H : List Label} {i : Nat} {d : Directive}
    (h : (haltStubs H)[i]? = some d) :
    (∃ l ∈ H, d = .label l) ∨ d = .instr (.regular .W64 .W64 .ud2) := by
  induction H generalizing i with
  | nil => simp [haltStubs] at h
  | cons l H ih =>
    match i, h with
    | 0, h => exact Or.inl ⟨l, List.mem_cons_self, by simpa [haltStubs] using h.symm⟩
    | 1, h => exact Or.inr (by simpa [haltStubs] using h.symm)
    | i + 2, h =>
      rcases ih (by simpa [haltStubs] using h) with ⟨l', hl', e⟩ | e
      · exact Or.inl ⟨l', List.mem_cons_of_mem _ hl', e⟩
      · exact Or.inr e

/-- With the stubs at the start of the program, a directive that is not a stub, or that is a label
outside `H`, is at index `2 * H.length` or later. -/
theorem haltStubs_le_of_getElem? [Host] {H : List Label}
    (hs : (haltStubs H).IsInfixAt Host.prog 0) {k : Nat} {d : Directive}
    (hd : Host.prog[k]? = some d) (hn : ∀ l ∈ H, d ≠ .label l)
    (hu : d ≠ .instr (.regular .W64 .W64 .ud2)) : 2 * H.length ≤ k := by
  refine Nat.le_of_not_lt fun hlt => ?_
  have hk : (haltStubs H)[k]? = some d := by
    rw [← haltStubs_length] at hlt
    have := List.isInfixAt_iff_getElem?.mp hs k hlt
    rw [Nat.zero_add] at this
    rw [List.getElem?_eq_getElem hlt]
    exact this.symm.trans hd
  rcases haltStubs_getElem? hk with ⟨l, hl, e⟩ | e
  · exact hn l hl e
  · exact hu e

theorem Halts.of_stubs [Host] {H : List Label} (hs : (haltStubs H).IsInfixAt Host.prog 0) :
    Halts H where
  ret_not_mem k asz osz t hk := by
    have := haltStubs_le_of_getElem? hs hk (by simp) (by nofun)
    exact haltStubs_addrOf_not_mem hs (by omega)
  prog_label_not_mem l hl hn := by
    simp only [Program.labels, List.mem_filterMap] at hl
    obtain ⟨d, hd, hdl⟩ := hl
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hd
    have e : d = .label l := by cases d <;> simp_all [Directive.label?]
    subst e
    have := haltStubs_le_of_getElem? hs hk (fun l' hl' e => hn (by cases e; exact hl')) (by simp)
    rw [Host.label_eq (p := Host.prog) (k := 0) (List.prefix_refl _) hk, Nat.zero_add]
    exact haltStubs_addrOf_not_mem hs (by omega)

namespace Halts

open Program.WP

variable [Host] [FunDecls]

/-- Like `call_label`, for the calls of a program with halt labels `H`. A call to a label with no
fragment exits there, with the return address pushed. A call to a fragment may assume that the
return address is not a halt address. -/
theorem call_label {H : List Label} [Halts H] {f : Label} (asz osz : Width)
    {Q : Unit → MachineData → Prop} {E : Int64 → MachineData → Prop} :
    ⦃ fun s => Mem.Mapped [(s.regs.rsp.toBitVec - 8#64, 8)] s.dmem
        ∧ (FunDecls.at (label f) = none → ∀ ra, E (label f) (s.push64 ra))
        ∧ (FunDecls.at (label f) ≠ none → ∀ ra, ra ∉ H.map label →
          WP.wp (FunDecls.body f) (fun _ _ => False)
            (fun a s' => (a = ra → Q () s') ∧ (a ≠ ra → E a s')) (s.push64 ra)) ⦄
      (Directive.instr (.regular asz osz (.call (.rel (.sub (.label f) .after_current_instruction)))))
    ⦃ Q; E ⦄ := by
  cases hg : FunDecls.at (label f) with
  | none =>
    refine Triple.intro fun s ⟨hmapped, hexit, _⟩ => ?_
    refine Program.wp_single fun h _ _ _ _ hj => ?_
    obtain ⟨i, hload⟩ := Option.isSome_iff_exists.mp
      (Mem.Mapped.loadInt_isSome hmapped (Mem.Blocks.Inside.base (Nat.le_refl _)))
    have hload : Mem.loadInt s.dmem (s.regs.get64 .rsp - 8#64) 8 = some i := hload
    simp only [Directive.interp, Instr.interp, Operation.interp, RelRegOrMem.interp,
      ConstExpr.interp, MachineData.store, hload, Effects.All]
    rw [Int64.ofBitVec_toBitVec, Int64.add_sub_self_left]
    refine hj (label f) (s.push64 h.embedding.endAddr) ?_
    unfold Executable.StepOut
    simp only [hg, Option.map_none]
    exact hexit rfl _
  | some g =>
    refine Triple.intro fun s ⟨hmapped, _, hbody⟩ => (wp_call_iff hg).mpr fun [h : Embeds _] =>
      ⟨Mem.Mapped.loadInt_isSome hmapped (Mem.Blocks.Inside.base (Nat.le_refl _)), ?_⟩
    have hra : h.embedding.endAddr ∉ H.map label :=
      Halts.ret_not_mem _ asz osz _ h.embedding.isInfixAt.cons.1
    refine Program.wp_mono (fun _ h => h) (fun u hu => ?_) (hbody (by simp) _ hra)
    by_cases hpc : u.pc = h.embedding.endAddr
    · simp only [hpc, ite_true]
      exact hu.1 hpc
    · simp only [hpc, ite_false]
      exact hu.2 hpc

end Halts
