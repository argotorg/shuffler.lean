module

public import ProofKit.Cfg
import all ProofKit.Cfg

@[expose] public section

/-!
# `permute`: one lemma for each block

A copy of `ProofKit.CfgBlock` of the branch `wf/u-loop` (commit 284bbce), in the namespace
`Bbu.Unit.Permute`, with the tactics `pm_labels` and `pm_block`. The copy keeps this branch
independent of the other unit branches.

* `forallBlocks_cases L hc h`: `p.ForallBlocks P` from one obligation for each label in `L`,
  if each block has a label in `L` (`hc`).
* `pm_labels`: the goal `p.ForallBlocks fun blk => blk.label ∈ L`.
* `pm_block [lemmas]`: the goal `p.ForallBlocks fun blk => blk.label = l → P blk` for a literal
  label `l`. The goal of the block of `l` stays, with `P` unfolded by `lemmas` and
  `Program.labels p` as a literal list. The other blocks close.
-/

namespace Bbu.Unit.Permute

theorem forallBlocksFrom_cases {P : Program.Block → Prop} {L : List CfgLabel} :
    ∀ {bs : List (Label × Program)} {b : CfgLabel} {j : Nat} {body : Program},
      Program.forallBlocksFrom (fun blk => blk.label ∈ L) b j body bs →
      (∀ l ∈ L, Program.forallBlocksFrom (fun blk => blk.label = l → P blk) b j body bs) →
      Program.forallBlocksFrom P b j body bs
  | [], _, _, _, hc, h => h _ hc rfl
  | (_, _) :: _, _, _, _, hc, h =>
    ⟨(h _ hc.1).1 rfl, forallBlocksFrom_cases hc.2 fun l hl => (h l hl).2⟩

theorem forallBlocks_cases {p : Program} {P : Program.Block → Prop} (L : List CfgLabel)
    (hc : p.ForallBlocks fun blk => blk.label ∈ L)
    (h : ∀ l ∈ L, p.ForallBlocks fun blk => blk.label = l → P blk) : p.ForallBlocks P :=
  forallBlocksFrom_cases hc h

macro "pm_labels" : tactic => `(tactic| (
  cfg_view as hview
  rw [Program.ForallBlocks, hview]
  clear hview
  simp only [Program.forallBlocksFrom, List.mem_cons, List.not_mem_nil, CfgLabel.label.injEq,
    reduceCtorEq, String.reduceEq, or_false, false_or, or_true, true_or, and_self]))

syntax "pm_block" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| pm_block) => `(tactic| pm_block [])
  | `(tactic| pm_block [$ls,*]) => `(tactic| (
    cfg_view as hview
    have hlabels : Program.labels _ = _ :=
      (Program.labels_view _).trans (congrArg (fun v => List.map (·.1) v.2) hview)
    simp only [List.map_cons, List.map_nil] at hlabels
    rw [Program.ForallBlocks, hview]
    clear hview
    simp only [Program.forallBlocksFrom, hlabels, CfgLabel.label.injEq, reduceCtorEq,
      String.reduceEq, Nat.reduceAdd, false_implies, true_implies, and_true, true_and, $ls,*]
    all_goals clear hlabels))

end Bbu.Unit.Permute
