import ProofKit.Cfg

/-!
`Program.WP.cfg` proofs with one lemma for each block. All untrusted: they only
build terms that the kernel checks.

The obligation `p.ForallBlocks P` of `Program.WP.cfg` has one conjunct for each
block. For a large program, a proof of all blocks in one declaration is slow to
elaborate and to check. With `forallBlocks_cases`, each block is a separate
lemma `p.ForallBlocks fun blk => blk.label = l → P blk`:

* `forallBlocks_cases L hc h`: `p.ForallBlocks P` from one obligation for each
  label in `L`, if each block has a label in `L` (`hc`).
* `cfg_labels`: the goal `p.ForallBlocks fun blk => blk.label ∈ L`.
* `cfg_block [lemmas]`: the goal `p.ForallBlocks fun blk => blk.label = l → P blk`
  for a literal label `l`; the goal of the block of `l` stays, with `P`
  unfolded by `lemmas` and `Program.labels p` as a literal list (for
  `cfg_goto`). The other blocks close.
-/

namespace ProofKit

theorem forallBlocksFrom_cases {P : Program.Block → Prop} {L : List CfgLabel} :
    ∀ {bs : List (Label × Program)} {b : CfgLabel} {j : Nat} {body : Program},
      Program.forallBlocksFrom (fun blk => blk.label ∈ L) b j body bs →
      (∀ l ∈ L, Program.forallBlocksFrom (fun blk => blk.label = l → P blk) b j body bs) →
      Program.forallBlocksFrom P b j body bs
  | [], _, _, _, hc, h => h _ hc rfl
  | (_, _) :: _, _, _, _, hc, h =>
    ⟨(h _ hc.1).1 rfl, forallBlocksFrom_cases hc.2 fun l hl => (h l hl).2⟩

/-- An obligation for all blocks from one obligation for each label in `L`, if
each block has a label in `L`. -/
theorem forallBlocks_cases {p : Program} {P : Program.Block → Prop} (L : List CfgLabel)
    (hc : p.ForallBlocks fun blk => blk.label ∈ L)
    (h : ∀ l ∈ L, p.ForallBlocks fun blk => blk.label = l → P blk) : p.ForallBlocks P :=
  forallBlocksFrom_cases hc h

/-- Each block of `p` has a label in the literal list `L`. -/
macro "cfg_labels" : tactic => `(tactic| (
  cfg_view as hview
  rw [Program.ForallBlocks, hview]
  clear hview
  simp only [Program.forallBlocksFrom, List.mem_cons, List.not_mem_nil, CfgLabel.label.injEq,
    reduceCtorEq, String.reduceEq, or_false, false_or, or_true, true_or, and_self]))

/-- The obligation of the block with the literal label `l`, from
`p.ForallBlocks fun blk => blk.label = l → P blk`. The simp lemmas unfold `P`. -/
syntax "cfg_block" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| cfg_block) => `(tactic| cfg_block [])
  | `(tactic| cfg_block [$ls,*]) => `(tactic| (
    cfg_view as hview
    have hlabels : Program.labels _ = _ :=
      (Program.labels_view _).trans (congrArg (fun v => List.map (·.1) v.2) hview)
    simp only [List.map_cons, List.map_nil] at hlabels
    rw [Program.ForallBlocks, hview]
    clear hview
    simp only [Program.forallBlocksFrom, hlabels, CfgLabel.label.injEq, reduceCtorEq,
      String.reduceEq, Nat.reduceAdd, false_implies, true_implies, and_true, true_and, $ls,*]
    all_goals clear hlabels))

end ProofKit
