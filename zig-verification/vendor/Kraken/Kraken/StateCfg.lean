module

/-
The control-flow rule of the state wp. `Program.WP.cfg` proves the wp of a
program from one obligation per block of `Program.blocks`: an invariant `I`
gives the assertion at each label, and a variant `var` orders the edges
between labelled blocks.
-/
public import Kraken.X64.WP.Spec
public import Kraken.Blocks
public import Kraken.SeparationMem

@[expose] public section

open Std.WP
open Lean.Order


/-! ## The text of a block -/

def Program.fromNext (p : Program) : Option Label → Program
  | some l => Program.fromLabel p l
  | none => []

theorem Program.flatMap_drop_view {p : Program} (hnd : (Program.labels p).Nodup) (j : Nat) :
    ((Program.view p).2.drop j).flatMap Program.blockCells
      = Program.fromNext p (Program.firstLabel ((Program.view p).2.drop j)) := by
  rw [Program.firstLabel_drop]
  cases hj : (Program.view p).2[j]? with
  | none =>
    rw [List.drop_eq_nil_of_le (List.getElem?_eq_none_iff.mp hj)]
    rfl
  | some lb =>
    obtain ⟨l', b'⟩ := lb
    exact (Program.fromLabel_view hnd hj).symm

theorem Program.fromLabel_block {p : Program} (hnd : (Program.labels p).Nodup)
    {l : Label} {blk : Program.Block} (h : Program.blockAt p l = some blk) :
    Program.fromLabel p l = Directive.label l :: (blk.body ++ Program.fromNext p blk.next) := by
  obtain ⟨-, i, hi, hnext, -⟩ := Program.blockAtAux_spec h
  rw [Program.fromLabel_view hnd hi, Program.drop_flatMap_cons hi, hnext, Program.flatMap_drop_view hnd]

theorem Program.view_eq_entry {p : Program} (hnd : (Program.labels p).Nodup) :
    p = (Program.view p).1 ++ Program.fromNext p (Program.entryBlock p).next := by
  have h := Program.flatMap_drop_view hnd 0
  simp only [List.drop_zero] at h
  refine (Program.view_eq p).trans ?_
  rw [h]
  rfl

theorem Program.drop_fromLabel (p : Program) (l : Label) :
    p.drop (p.length - (Program.fromLabel p l).length) = Program.fromLabel p l := by
  obtain ⟨t, ht⟩ := Program.fromLabel_suffix p l
  have hlen := congrArg List.length ht
  rw [List.length_append] at hlen
  rw [show p.length - (Program.fromLabel p l).length = t.length by omega]
  calc p.drop t.length = (t ++ Program.fromLabel p l).drop t.length := by rw [ht]
    _ = Program.fromLabel p l := List.drop_left


/-! ## The control-flow rule -/

def Program.Intercept [Host] (ls : List Label) (s₀ : MachineData)
    (I' : Label → Nat → MachineData → Prop) (E : Int64 → MachineData → Prop)
    (a : Int64) (s : MachineData) : Prop :=
  (∃ i l, ls[i]? = some l ∧ label l = a ∧ s.StackAtOrBelow s₀ ∧ I' l (i + 1) s)
  ∨ (E a s ∧ ∀ l ∈ ls, label l = a → s₀.StackBelow s)

section
variable [Host] {ls : List Label} {s₀ s : MachineData} {I' : Label → Nat → MachineData → Prop}
  {E : Int64 → MachineData → Prop} {a : Int64}

theorem Program.Intercept.intro_label {i : Nat} {l : Label} (hl : ls[i]? = some l)
    (h : (s.StackAtOrBelow s₀ ∧ I' l (i + 1) s) ∨ (E (label l) s ∧ s₀.StackBelow s)) :
    Program.Intercept ls s₀ I' E (label l) s :=
  h.imp (fun h => ⟨i, l, hl, rfl, h⟩) (fun ⟨hE, hb⟩ => ⟨hE, fun _ _ _ => hb⟩)

theorem Program.Intercept.intro
    (h : (s.StackAtOrBelow s₀ ∧ ∃ l, label l = a ∧ l ∈ ls ∧ I' l (ls.idxOf l + 1) s)
      ∨ (E a s ∧ ∀ l ∈ ls, label l = a → s₀.StackBelow s)) :
    Program.Intercept ls s₀ I' E a s := by
  refine h.imp (fun ⟨hs, l, ha, hl, h⟩ => ?_) id
  have hi := List.idxOf_lt_length_of_mem hl
  exact ⟨_, l, by rw [List.getElem?_eq_getElem hi, List.getElem_idxOf hi], ha, hs, h⟩

theorem List.getElem?_cons_succ_of {α} {a b : α} {l : List α} {i : Nat} (h : l[i]? = some b) :
    (a :: l)[i + 1]? = some b :=
  h

macro_rules
  | `(grind| cfg_exit) =>
    `(grind| first
      ((apply Program.Intercept.intro_label);
        (repeat ((fail_if_success (apply List.getElem?_cons_zero)); (apply List.getElem?_cons_succ_of)));
        (apply List.getElem?_cons_zero))
      (apply Program.Intercept.intro)
      (skip))

theorem Program.Intercept.dispatch {p : Program} {C X : MachineState → Prop} {d : MachineData} {a : Int64}
    (h : Program.Intercept (Program.labels p) s₀ I' E a d)
    (hc : ∀ i l, (Program.labels p)[i]? = some l → label l = a → d.StackAtOrBelow s₀ →
      I' l (i + 1) d → C ⟨d, a⟩)
    (hx : E a d → X ⟨d, a⟩) :
    p.ContinueOnInternalExit s₀ C X ⟨d, a⟩ := by
  unfold Program.ContinueOnInternalExit
  rcases h with ⟨i, l, hl, hla, hown, hI⟩ | ⟨hE, hext⟩
  · rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨⟨l, List.mem_of_getElem? hl, hla⟩, hown⟩)]
    exact hc i l hl hla hown hI
  · rw [ite_eq_right_of_eq_false _ _ (eq_false fun ⟨⟨l, hl, hla⟩, hown⟩ => hown (hext l hl hla))]
    exact hx hE

theorem Program.labels_nodup_of_embeds {p : Program} [H : Embeds p] : (Program.labels p).Nodup :=
  Host.labels_nodup.sublist (H.embedding.isInfixAt.isInfix.sublist.filterMap _)

theorem Program.blockAt_noInternal {p : Program} {l : Label} {blk : Program.Block}
    (h : Program.blockAt p l = some blk) (a : Int64) : ¬ blk.body.InternalTarget a := by
  rintro ⟨l', hl', -⟩
  obtain ⟨-, i, hi, -, -⟩ := Program.blockAtAux_spec h
  have hfree := (Program.view_free p).2 _ (List.mem_of_getElem? hi) (.label l') (Program.mem_labels.mp hl')
  simp [Directive.isLabel] at hfree

theorem Program.entry_noInternal (p : Program) (a : Int64) : ¬ (Program.view p).1.InternalTarget a := by
  rintro ⟨l', hl', -⟩
  have hfree := (Program.view_free p).1 (.label l') (Program.mem_labels.mp hl')
  simp [Directive.isLabel] at hfree

end

@[spec_invariant_type] def Program.CfgInvariant := {s₀ : MachineData} → Label → MachineData → Prop

@[spec_invariant_type] def Program.CfgVariant := Label → MachineData → Nat

abbrev Program.CfgInvariant.lift (I : Program.CfgInvariant) (s₀ : MachineData) :
    Option Label → MachineData → Prop
  | none, s => s = s₀
  | some l, s => I (s₀ := s₀) l s

abbrev Program.Next (I : Program.CfgInvariant) (s₀ : MachineData) (Q : Unit → MachineData → Prop)
    (D : Label → Nat → MachineData → Prop) : Option Label → Nat → MachineData → Prop
  | some l, j, s => I (s₀ := s₀) l s ∧ D l j s
  | none, _, s => Q () s

namespace Program.WP

variable [Host] [FunDecls]

theorem cfg {p : Program} {s₀ : MachineData} {Q : Unit → MachineData → Prop}
    {E : Int64 → MachineData → Prop} (I : Program.CfgInvariant) (var : Program.CfgVariant)
    (h : ∀ blk ∈ Program.blocks p, ∀ t, I.lift s₀ blk.label t →
      WP.wp blk.body
        (fun _ => Program.Next @I s₀ Q (Program.Decreases var blk.label blk.idx t) blk.next (blk.idx + 1))
        (Program.Intercept (Program.labels p) s₀
          (fun l j s => I (s₀ := s₀) l s ∧ Program.Decreases var blk.label blk.idx t l j s) E) t) :
    WP.wp p Q E s₀ := by
  show Program.wp p (fun st => Q () st.data) (fun st => E st.pc st.data) s₀
  rw [Program.wp_eq]
  intro H
  have hlink := H.embedding.isInfixAt
  have hnd : (Program.labels p).Nodup := Program.labels_nodup_of_embeds
  have hK : ∀ l, Program.blockIdx p l ≤ (Program.view p).2.length := Program.blockIdx_le p
  have hcellOf : ∀ l, Program.fromLabel p l ≠ [] →
      p[p.length - (Program.fromLabel p l).length]? = some (Directive.label l) := by
    intro l hne
    have hdrop := Program.drop_fromLabel p l
    obtain ⟨t, rest, -, hfl, -, -⟩ := Program.fromLabel_split hnd hne
    conv at hdrop => rhs; rw [hfl]
    simpa [List.head?_drop] using congrArg List.head? hdrop
  have hne_of : ∀ l', (Program.blockAt p l').isSome → Program.fromLabel p l' ≠ [] := by
    intro l' hsome'
    obtain ⟨blk', hblk'⟩ := Option.isSome_iff_exists.mp hsome'
    rw [Program.fromLabel_block hnd hblk']
    exact List.cons_ne_nil _ _
  have edge : ∀ l s l' s', Program.Decreases var (some l) (Program.blockIdx p l + 1) s
      l' (Program.blockIdx p l' + 1) s' →
      Program.cfgMeasure p var (l', s') < Program.cfgMeasure p var (l, s) := by
    intro l s l' s' hedge
    have hedge : var l' s' < var l s
        ∨ (var l' s' = var l s ∧ Program.blockIdx p l + 1 < Program.blockIdx p l' + 1) :=
      hedge
    have hK' := hK l'
    unfold Program.cfgMeasure
    dsimp only
    rcases hedge with hlt | ⟨heq, hij⟩
    · have hmul : (var l' s' + 1) * ((Program.view p).2.length + 1)
          ≤ var l s * ((Program.view p).2.length + 1) :=
        Nat.mul_le_mul_right _ hlt
      have hsucc : (var l' s' + 1) * ((Program.view p).2.length + 1)
          = var l' s' * ((Program.view p).2.length + 1)
            + ((Program.view p).2.length + 1) := Nat.succ_mul _ _
      omega
    · rw [heq]
      omega
  have key : ∀ x : Label × MachineData, (Program.blockAt p x.1).isSome → I (s₀ := s₀) x.1 x.2 →
      While (·.pc ≠ H.embedding.endAddr)
        (fun «continue» => Host.exe.StepOver (fun a => (FunDecls.at a).map fun f => f.prog.wp (fun _ => False))
          «continue» (p.ContinueOnInternalExit s₀ «continue» fun st => E st.pc st.data))
        (fun st => Q () st.data)
        ⟨x.2, Host.addrOf (H.embedding.start + (p.length - (Program.fromLabel p x.1).length))⟩ := by
    intro x
    induction x using (measure (Program.cfgMeasure p var)).wf.induction with
    | _ x ih =>
      obtain ⟨l, s⟩ := x
      intro hsome hI
      dsimp only at hsome hI ⊢
      have jump : ∀ l' s', (Program.blockAt p l').isSome → I (s₀ := s₀) l' s' →
          Program.cfgMeasure p var (l', s') < Program.cfgMeasure p var (l, s) →
          While (·.pc ≠ H.embedding.endAddr)
            (fun «continue» => Host.exe.StepOver (fun a => (FunDecls.at a).map fun f => f.prog.wp (fun _ => False))
              «continue» (p.ContinueOnInternalExit s₀ «continue» fun st => E st.pc st.data))
            (fun st => Q () st.data) ⟨s', label l'⟩ := by
        intro l' s' hsome' hI' hlt
        rw [Host.label_eq hlink (hcellOf l' (hne_of l' hsome'))]
        exact ih (l', s') hlt hsome' hI'
      obtain ⟨blk, hblk⟩ := Option.isSome_iff_exists.mp hsome
      obtain ⟨hlab, i', hi', hnext', hidx⟩ := Program.blockAtAux_spec hblk
      have hbi : blk.idx = Program.blockIdx p l + 1 := by
        rw [hidx, Program.blockIdx_eq hnd hi', Nat.add_comm]
      have hb := h blk (Program.mem_blocks_of_blockAt hblk)
      rw [hlab, hbi] at hb
      have htext := Program.fromLabel_block hnd hblk
      have hlen := congrArg List.length htext
      simp only [List.length_cons, List.length_append] at hlen
      have hdrop := Program.drop_fromLabel p l
      have hsuf : (Program.fromLabel p l).length ≤ p.length := by
        have := congrArg List.length hdrop
        simp only [List.length_drop] at this
        omega
      generalize hi : p.length - (Program.fromLabel p l).length = i at hdrop ⊢
      rw [htext] at hdrop
      have hbody : blk.body.IsInfixAt p (i + 1) :=
        ⟨Program.fromNext p blk.next, by rw [← List.drop_drop, hdrop]; rfl⟩
      have hpi : p[i]? = some (.label l) := by
        have h0 := congrArg (·[0]?) hdrop
        simpa only [List.getElem?_drop, Nat.add_zero, List.getElem?_cons_zero] using h0
      have hlab' : Host.prog[H.embedding.start + i]? = some (.label l) := by
        obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp hpi
        rw [List.isInfixAt_iff_getElem?.mp hlink i hlt, heq]
      have haddr : Host.addrOf (H.embedding.start + (i + 1)) = Host.addrOf (H.embedding.start + i) := by
        rw [← Nat.add_assoc, Host.addrOf_succ hlab', Host.label_size _ _ hlab']; simp
      rw [← haddr]
      refine Program.run_infix (o := i + 1) hbody (by omega) (Program.blockAt_noInternal hblk)
        (hb s hI) ?_ ?_
      · intro st hpc hnext
        cases hn : blk.next with
        | none =>
          simp only [hn] at hnext hlen
          refine While.stop ?_ hnext
          show ¬ st.pc ≠ Host.addrOf (H.embedding.start + p.length)
          rw [hpc]
          simp only [Program.fromNext, List.length_nil] at hlen
          intro hne
          exact hne (by congr 1; omega)
        | some l' =>
          simp only [hn] at hnext hlen
          obtain ⟨hI', hdec⟩ := hnext
          obtain ⟨hsome', hidx'⟩ := Program.blockAt_next hnd hblk hn
          simp only [Program.fromNext] at hlen
          have hst : st = ⟨st.data, Host.addrOf (H.embedding.start + (p.length - (Program.fromLabel p l').length))⟩ := by
            cases st
            simp only [MachineState.mk.injEq, true_and] at hpc ⊢
            rw [hpc]
            congr 1
            omega
          rw [hst]
          exact ih (l', st.data) (edge l s l' st.data (by rw [hidx']; exact hdec)) hsome' hI'
      · rintro ⟨d, a⟩ hst
        refine Program.Intercept.dispatch hst (fun j l' hl' hla _ hI' => ?_) id
        subst hla
        exact jump l' d (Program.isSome_blockAt_of_mem (List.mem_of_getElem? hl')) hI'.1
          (edge l s l' d (by rw [Program.blockIdx_eq_of_getElem? hnd hl']; exact hI'.2))
  have hq : (Program.view p).1.IsInfixAt p 0 := ⟨_, (Program.view_eq_entry hnd).symm⟩
  have hlen0 := congrArg List.length (Program.view_eq_entry hnd)
  simp only [List.length_append] at hlen0
  refine Program.run_infix (o := 0) hq (by omega) (Program.entry_noInternal p)
    (h _ (Program.entryBlock_mem_blocks p) s₀ rfl) ?_ ?_
  · intro st hpc hnext
    simp only [Program.entryBlock] at hnext hlen0
    cases hv : (Program.view p).2 with
    | nil =>
      simp only [hv, Program.firstLabel, Program.fromNext, List.length_nil] at hnext hlen0
      refine While.stop ?_ hnext
      show ¬ st.pc ≠ Host.addrOf (H.embedding.start + p.length)
      rw [hpc]
      intro hne
      exact hne (by congr 1; omega)
    | cons lb rest =>
      obtain ⟨l', b'⟩ := lb
      simp only [hv, Program.firstLabel, Program.fromNext] at hnext hlen0
      have hsome' : (Program.blockAt p l').isSome := by
        have hndv : ((Program.view p).2.map (·.1)).Nodup := by rwa [← Program.labels_view]
        have h0 : (Program.view p).2[0]? = some (l', b') := by rw [hv]; rfl
        show (Program.blockAtAux 1 (Program.view p).2 l').isSome = true
        rw [Program.blockAtAux_of_getElem hndv h0]
        rfl
      have hst : st = ⟨st.data, Host.addrOf (H.embedding.start + (p.length - (Program.fromLabel p l').length))⟩ := by
        cases st
        simp only [MachineState.mk.injEq, true_and] at hpc ⊢
        rw [hpc]
        congr 1
        omega
      rw [hst]
      exact key (l', st.data) hsome' hnext.1
  · rintro ⟨d, a⟩ hst
    refine Program.Intercept.dispatch hst (fun j l' hl' hla _ hI' => ?_) id
    subst hla
    have hsome' := Program.isSome_blockAt_of_mem (List.mem_of_getElem? hl')
    rw [Host.label_eq hlink (hcellOf l' (hne_of l' hsome'))]
    exact key (l', d) hsome' hI'.1

@[spec] theorem Spec.cfg {p : Program} {s₀ : MachineData} {Q : Unit → MachineData → Prop}
    {E : Int64 → MachineData → Prop} (I : Program.CfgInvariant) (var : Program.CfgVariant)
    (h : ∀ blk ∈ Program.blocks p, ∀ t, I.lift s₀ blk.label t →
      WP.wp blk.body
        (fun _ => Program.Next @I s₀ Q (Program.Decreases var blk.label blk.idx t) blk.next (blk.idx + 1))
        (Program.Intercept (Program.labels p) s₀
          (fun l j s => I (s₀ := s₀) l s ∧ Program.Decreases var blk.label blk.idx t l j s) E) t) :
    ⦃ fun s => s = s₀ ⦄ Program.cfg p ⦃ Q; E ⦄ :=
  Triple.intro fun _ hs => hs ▸ (Program.cfg_eq p).symm ▸ Program.WP.cfg @I var h

end Program.WP
