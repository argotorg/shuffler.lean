import BbuKraken.Asm
import BbuKraken.Names

/-!
The function declarations of the linked program: `c/build_bottom_up.S` at the position `k`
of the host program. The labels are the symbol names of `BbuKraken.Names`. Each function
starts with its label and then an instruction that is not padding, so distinct function
labels have distinct addresses, and `FunDecls.at (label f)` is the fragment of `f`.
-/

open Std.WP Lean.Order
open scoped Program.WP

namespace Bbu

set_option maxRecDepth 100000 in
theorem bbuAsm_eq : bbuAsm = isSpilledAsm ++ shallowestCopyAsm ++ pushAsm ++ dupAsm
    ++ produceAsm ++ swapWithAsm ++ generateAsm ++ finishAsm ++ loopAsm
    ++ popAsm ++ buildBottomUpAsm ++ emissionPopAsm ++ spillSetAddAsm ++ spillSetAsm
    ++ removeSurplusAsm ++ removeSurplusEntryAsm ++ permuteEntryAsm ++ permuteAtLowestHeightAsm
    ++ permuteAtLowestHeightEntryAsm := by rfl

section
set_option maxRecDepth 100000

theorem isSpilled_at : isSpilledAsm.IsInfixAt bbuAsm 0 := by rw [bbuAsm_eq]; exact ⟨_, rfl⟩
theorem shallowestCopy_at : shallowestCopyAsm.IsInfixAt bbuAsm 16 := by
  rw [bbuAsm_eq]; exact ⟨_, rfl⟩
theorem swapWith_at : swapWithAsm.IsInfixAt bbuAsm 203 := by rw [bbuAsm_eq]; exact ⟨_, rfl⟩
theorem push_at : pushAsm.IsInfixAt bbuAsm 33 := by rw [bbuAsm_eq]; exact ⟨_, rfl⟩
theorem dup_at : dupAsm.IsInfixAt bbuAsm 74 := by rw [bbuAsm_eq]; exact ⟨_, rfl⟩
theorem produce_at : produceAsm.IsInfixAt bbuAsm 110 := by rw [bbuAsm_eq]; exact ⟨_, rfl⟩
theorem generate_at : generateAsm.IsInfixAt bbuAsm 266 := by rw [bbuAsm_eq]; exact ⟨_, rfl⟩
theorem finish_at : finishAsm.IsInfixAt bbuAsm 319 := by rw [bbuAsm_eq]; exact ⟨_, rfl⟩
theorem loop_at : loopAsm.IsInfixAt bbuAsm 528 := by rw [bbuAsm_eq]; exact ⟨_, rfl⟩
theorem buildBottomUp_at : buildBottomUpAsm.IsInfixAt bbuAsm 849 := by
  rw [bbuAsm_eq]; exact ⟨_, rfl⟩
end

section
variable [Host]

-- Two labels that are each followed by an instruction that is not padding have
-- the same address only if they are the same label.
theorem label_inj {a b : Nat} {l₁ l₂ : Label} {i₁ i₂ : Instr}
    (ha : Host.prog[a]? = some (.label l₁)) (ha' : Host.prog[a + 1]? = some (.instr i₁))
    (hpa : ¬ i₁.IsPadding)
    (hb : Host.prog[b]? = some (.label l₂)) (hb' : Host.prog[b + 1]? = some (.instr i₂))
    (hpb : ¬ i₂.IsPadding) (h : label l₁ = label l₂) : l₁ = l₂ := by
  rw [Host.label_eq (p := [.label l₁]) (k := a) (i := 0) (by simpa [List.isInfixAt_iff_getElem?])
      rfl, Host.label_eq (p := [.label l₂]) (k := b) (i := 0)
      (by simpa [List.isInfixAt_iff_getElem?]) rfl] at h
  rcases Nat.lt_trichotomy a b with hab | rfl | hab
  · have : a + 1 ≠ b := by rintro rfl; simp [ha'] at hb
    exact absurd h (Host.addrOf_ne ha' hpa (by omega) (by omega))
  · simpa [ha] using hb
  · have : b + 1 ≠ a := by rintro rfl; simp [hb'] at ha
    exact absurd h.symm (Host.addrOf_ne hb' hpb (by omega) (by omega))

end

end Bbu

namespace Bbu

-- The position of the program in the host program.
structure Linked [Host] where
  k : Nat
  hb : bbuAsm.IsInfixAt Host.prog k

section
variable [Host]

-- The fragment `g` starts with the label `l`, then an instruction that is not padding.
def Head (g : Fragment) (l : Label) : Prop :=
  g.startAddr = label l ∧ ∃ pos i, Host.prog[pos]? = some (.label l)
    ∧ Host.prog[pos + 1]? = some (.instr i) ∧ ¬ i.IsPadding

theorem Head.inj {f g : Fragment} {l l' : Label} (hf : Head f l) (hg : Head g l')
    (h : f.startAddr = g.startAddr) : l = l' := by
  obtain ⟨hf, a, i, ha, ha', hpa⟩ := hf
  obtain ⟨hg, b, i', hb, hb', hpb⟩ := hg
  exact label_inj ha ha' hpa hb hb' hpb (hf ▸ hg ▸ h)

theorem head_of_isInfixAt {p : Program} {k : Nat} {l : Label} {i : Instr} {rest : Program}
    (hk : p.IsInfixAt Host.prog k) (hp : p = .label l :: .instr i :: rest) (hpad : ¬ i.IsPadding) :
    Head (@Fragment.mk _ p ⟨⟨k, hk⟩⟩) l := by
  subst hp
  have h := List.isInfixAt_iff_getElem?.mp hk
  refine ⟨(Host.label_eq hk (i := 0) rfl).symm, k, i, h 0 (by simp), h 1 (by simp), hpad⟩

theorem FunDecls.at_of_unique {fs : List Fragment} {f : Fragment} {a : Int64} (hf : f ∈ fs)
    (ha : f.startAddr = a) (hu : ∀ g ∈ fs, g.startAddr = a → g = f) :
    (⟨fs⟩ : FunDecls).at a = some f := by
  show fs.find? _ = _
  induction fs with
  | nil => simp at hf
  | cons g fs ih =>
    by_cases hg : g.startAddr = a
    · simp [hu g (by simp) hg, ha]
    · have hf' : f ∈ fs := by
        rcases List.mem_cons.mp hf with rfl | h
        · exact absurd ha hg
        · exact h
      rw [List.find?_cons_of_neg (by simpa using hg)]
      exact ih hf' fun g' hg' => hu g' (by simp [hg'])

end

namespace Linked
variable [Host] (L : Linked)

def frag (p : Program) {o : Nat} (h : p.IsInfixAt bbuAsm o) : Fragment :=
  @Fragment.mk _ p ⟨⟨L.k + o, h.trans L.hb⟩⟩

-- The functions that are called.
def decls : FunDecls := ⟨[L.frag isSpilledAsm isSpilled_at,
  L.frag shallowestCopyAsm shallowestCopy_at, L.frag swapWithAsm swapWith_at,
  L.frag pushAsm push_at, L.frag dupAsm dup_at, L.frag produceAsm produce_at,
  L.frag generateAsm generate_at, L.frag finishAsm finish_at, L.frag loopAsm loop_at]⟩

macro "head_tac" : tactic =>
  `(tactic| exact head_of_isInfixAt _ rfl (by rintro ⟨⟩))

theorem heads : Head (L.frag isSpilledAsm isSpilled_at) Names.isSpilled
    ∧ Head (L.frag shallowestCopyAsm shallowestCopy_at) Names.shallowestCopyPosition
    ∧ Head (L.frag swapWithAsm swapWith_at) Names.swapWith
    ∧ Head (L.frag pushAsm push_at) Names.push
    ∧ Head (L.frag dupAsm dup_at) Names.dup
    ∧ Head (L.frag produceAsm produce_at) Names.produce
    ∧ Head (L.frag generateAsm generate_at) Names.generate
    ∧ Head (L.frag finishAsm finish_at) Names.permute
    ∧ Head (L.frag loopAsm loop_at) Names.buildBottomUp := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> head_tac

theorem at_label {fs : List Fragment} {f : Fragment} {l : Label} (hf : f ∈ fs) (hx : Head f l)
    (hall : ∀ g ∈ fs, ∃ l', Head g l' ∧ (l' = l → g = f)) :
    (⟨fs⟩ : FunDecls).at (label l) = some f :=
  FunDecls.at_of_unique hf hx.1 fun g hg ha => by
    obtain ⟨l', hg', he⟩ := hall g hg
    exact he (Head.inj hg' hx (ha.trans hx.1.symm))

theorem find_skip {f g : Fragment} {gs : List Fragment} {l l' : Label} (hg : Head g l')
    (hx : Head f l) (hne : l' ≠ l) :
    (g :: gs).find? (·.startAddr == label l) = gs.find? (·.startAddr == label l) :=
  List.find?_cons_of_neg (by
    intro h
    exact hne (Head.inj hg hx ((beq_iff_eq.mp h).trans hx.1.symm)))

theorem find_hit {f : Fragment} {gs : List Fragment} {l : Label} (hx : Head f l) :
    (f :: gs).find? (·.startAddr == label l) = some f :=
  by simp [hx.1]

set_option hygiene false in
macro "at_tac " h:ident : tactic => `(tactic| (
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := heads _
  show List.find? _ [_, _, _, _, _, _, _, _, _] = _
  all_goals first | rewrite [find_skip h1 $h (by decide)] | exact find_hit $h
  all_goals first | rewrite [find_skip h2 $h (by decide)] | exact find_hit $h
  all_goals first | rewrite [find_skip h3 $h (by decide)] | exact find_hit $h
  all_goals first | rewrite [find_skip h4 $h (by decide)] | exact find_hit $h
  all_goals first | rewrite [find_skip h5 $h (by decide)] | exact find_hit $h
  all_goals first | rewrite [find_skip h6 $h (by decide)] | exact find_hit $h
  all_goals first | rewrite [find_skip h7 $h (by decide)] | exact find_hit $h
  all_goals first | rewrite [find_skip h8 $h (by decide)] | exact find_hit $h
  all_goals exact find_hit $h))

theorem isSpilled_decl :
    L.decls.at (label Names.isSpilled) = some (L.frag isSpilledAsm isSpilled_at) := by at_tac h1
theorem shallowestCopy_decl : L.decls.at (label Names.shallowestCopyPosition)
    = some (L.frag shallowestCopyAsm shallowestCopy_at) := by at_tac h2
theorem swapWith_decl :
    L.decls.at (label Names.swapWith) = some (L.frag swapWithAsm swapWith_at) := by at_tac h3
theorem push_decl : L.decls.at (label Names.push) = some (L.frag pushAsm push_at) := by at_tac h4
theorem dup_decl : L.decls.at (label Names.dup) = some (L.frag dupAsm dup_at) := by at_tac h5
theorem produce_decl :
    L.decls.at (label Names.produce) = some (L.frag produceAsm produce_at) := by at_tac h6
theorem generate_decl :
    L.decls.at (label Names.generate) = some (L.frag generateAsm generate_at) := by at_tac h7
theorem finish_decl : L.decls.at (label Names.permute)
    = some (L.frag finishAsm finish_at) := by at_tac h8
theorem loop_decl :
    L.decls.at (label Names.buildBottomUp) = some (L.frag loopAsm loop_at) := by at_tac h9

end Linked

end Bbu
