module

public import BbuKraken.Link
import all BbuKraken.Link

public import BbuKraken.Unit.SpillAdd
import all BbuKraken.Unit.SpillAdd

@[expose] public section

/-! The declarations of all internal functions called by the planner. Each declaration
is a fragment of the same assembly file in the host program. Lookup uses the label
at the head of a fragment; distinct labels have distinct addresses. -/

namespace Bbu
namespace Linked

section
variable [Host]

-- A table of named fragments gives function declarations without address assumptions.
theorem decl_of_lookup {fs : List (Label × Fragment)}
    (hh : ∀ x ∈ fs, Head x.2 x.1) {l : Label} {f : Fragment}
    (hf : fs.lookup l = some f) :
    (⟨fs.map Prod.snd⟩ : FunDecls).at (label l) = some f := by
  have hx : Head f l := by
    obtain ⟨xs, ys, he, _⟩ := List.lookup_eq_some_iff.mp hf
    apply hh (l, f)
    rw [he]
    simp
  induction fs with
  | nil => simp at hf
  | cons x fs ih =>
    obtain ⟨l', g⟩ := x
    have hg := hh (l', g) (by simp)
    by_cases he : l = l'
    · subst l'
      have he : g = f := by simpa only [List.lookup_cons_self, Option.some.injEq] using hf
      subst g
      exact find_hit hx
    · have ht : fs.lookup l = some f := by
        simpa only [List.lookup_cons, beq_eq_false_iff_ne.mpr he] using hf
      change (g :: fs.map Prod.snd).find? _ = some f
      rw [find_skip hg hx (Ne.symm he)]
      exact ih (fun x hx => hh x (by simp [hx])) ht
end

variable [Host] (L : Linked)

def plannerFunctions : List (Label × Fragment) :=
  [(Names.isSpilled, L.frag isSpilledAsm isSpilled_at),
    (Names.shallowestCopyPosition, L.frag shallowestCopyAsm shallowestCopy_at),
    (Names.push, L.frag pushAsm push_at),
    (Names.dup, L.frag dupAsm dup_at),
    (Names.produce, L.frag produceAsm produce_at),
    (Names.swapWith, L.frag swapWithAsm swapWith_at),
    (Names.generate, L.frag generateAsm generate_at),
    (Names.permute, L.frag finishAsm finish_at),
    (Names.buildBottomUp, L.frag loopAsm loop_at),
    (Names.pop, L.frag popAsm pop_at),
    (Names.spillSetAdd, L.frag spillSetAddAsm spillSetAdd_at),
    (Names.removeSurplus, L.frag removeSurplusAsm removeSurplus_at),
    (Names.permuteAtLowestHeight, L.frag permuteAtLowestHeightAsm permuteAtLowestHeight_at),
    (Names.map, L.frag mapAsm map_at),
    (Names.closestCopy, L.frag closestCopyAsm closestCopy_at),
    (Names.mapInPlace, L.frag mapInPlaceAsm mapInPlace_at),
    (Names.mapClosestCopies, L.frag mapClosestCopiesAsm mapClosestCopies_at),
    (Names.mapWildcardSlotCopies, L.frag mapWildcardSlotCopiesAsm mapWildcardSlotCopies_at),
    (Names.keepWildcardSlots, L.frag keepWildcardSlotsAsm keepWildcardSlots_at),
    (Names.absorbSurplus, L.frag absorbSurplusAsm absorbSurplus_at),
    (Names.isRetained, L.frag isRetainedAsm isRetained_at),
    (Names.hasOtherRetainedCopy, L.frag hasOtherRetainedCopyAsm hasOtherRetainedCopy_at),
    (Names.isDemanded, L.frag isDemandedAsm isDemanded_at),
    (Names.classify, L.frag classifyAsm classify_at),
    (Names.resolve, L.frag resolveAsm resolve_at),
    (Names.isAvailable, L.frag isAvailableAsm isAvailable_at),
    (Names.run, L.frag runAsm run_at),
    (Names.plannerRun, L.frag plannerRunAsm plannerRun_at)]

@[instance_reducible] def plannerDecls : FunDecls := ⟨L.plannerFunctions.map Prod.snd⟩

theorem plannerHeads : ∀ x ∈ L.plannerFunctions, Head x.2 x.1 := by
  intro x hx
  simp only [plannerFunctions, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals exact head_of_isInfixAt _ rfl (by rintro ⟨⟩)

theorem planner_external (X : ExitBoundary) :
    ∀ x ∈ L.plannerFunctions, label x.1 ≠ label "exit" := by
  intro x hx
  simp only [plannerFunctions, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact X.head isSpilled_at rfl
  · exact X.head shallowestCopy_at rfl
  · exact X.head push_at rfl
  · exact X.head dup_at rfl
  · exact X.head produce_at rfl
  · exact X.head swapWith_at rfl
  · exact X.head generate_at rfl
  · exact X.head finish_at rfl
  · exact X.head loop_at rfl
  · exact X.head pop_at rfl
  · exact X.head spillSetAdd_at rfl
  · exact X.head removeSurplus_at rfl
  · exact X.head permuteAtLowestHeight_at rfl
  · exact X.head map_at rfl
  · exact X.head closestCopy_at rfl
  · exact X.head mapInPlace_at rfl
  · exact X.head mapClosestCopies_at rfl
  · exact X.head mapWildcardSlotCopies_at rfl
  · exact X.head keepWildcardSlots_at rfl
  · exact X.head absorbSurplus_at rfl
  · exact X.head isRetained_at rfl
  · exact X.head hasOtherRetainedCopy_at rfl
  · exact X.head isDemanded_at rfl
  · exact X.head classify_at rfl
  · exact X.head resolve_at rfl
  · exact X.head isAvailable_at rfl
  · exact X.head run_at rfl
  · exact X.head plannerRun_at rfl

theorem planner_exit_decl (X : ExitBoundary) : L.plannerDecls.at (label "exit") = none := by
  show (L.plannerFunctions.map Prod.snd).find? _ = none
  apply List.find?_eq_none.mpr
  intro f hf he
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hf
  exact L.planner_external X x hx ((L.plannerHeads x hx).1.symm.trans (beq_iff_eq.mp he))

theorem planner_lookup {l : Label} {f : Fragment} (hf : L.plannerFunctions.lookup l = some f) :
    L.plannerDecls.at (label l) = some f :=
  decl_of_lookup L.plannerHeads hf

theorem planner_isSpilled_decl : L.plannerDecls.at (label Names.isSpilled) =
    some (L.frag isSpilledAsm isSpilled_at) :=
  L.planner_lookup rfl

theorem planner_shallowestCopyPosition_decl : L.plannerDecls.at (label Names.shallowestCopyPosition) =
    some (L.frag shallowestCopyAsm shallowestCopy_at) :=
  L.planner_lookup rfl

theorem planner_push_decl : L.plannerDecls.at (label Names.push) =
    some (L.frag pushAsm push_at) :=
  L.planner_lookup rfl

theorem planner_dup_decl : L.plannerDecls.at (label Names.dup) =
    some (L.frag dupAsm dup_at) :=
  L.planner_lookup rfl

theorem planner_produce_decl : L.plannerDecls.at (label Names.produce) =
    some (L.frag produceAsm produce_at) :=
  L.planner_lookup rfl

theorem planner_swapWith_decl : L.plannerDecls.at (label Names.swapWith) =
    some (L.frag swapWithAsm swapWith_at) :=
  L.planner_lookup rfl

theorem planner_generate_decl : L.plannerDecls.at (label Names.generate) =
    some (L.frag generateAsm generate_at) :=
  L.planner_lookup rfl

theorem planner_permute_decl : L.plannerDecls.at (label Names.permute) =
    some (L.frag finishAsm finish_at) :=
  L.planner_lookup rfl

theorem planner_buildBottomUp_decl : L.plannerDecls.at (label Names.buildBottomUp) =
    some (L.frag loopAsm loop_at) :=
  L.planner_lookup rfl

theorem planner_pop_decl : L.plannerDecls.at (label Names.pop) =
    some (L.frag popAsm pop_at) :=
  L.planner_lookup rfl

theorem planner_spillSetAdd_decl : L.plannerDecls.at (label Names.spillSetAdd) =
    some (L.frag spillSetAddAsm spillSetAdd_at) :=
  L.planner_lookup rfl

theorem planner_removeSurplus_decl : L.plannerDecls.at (label Names.removeSurplus) =
    some (L.frag removeSurplusAsm removeSurplus_at) :=
  L.planner_lookup rfl

theorem planner_permuteAtLowestHeight_decl : L.plannerDecls.at (label Names.permuteAtLowestHeight) =
    some (L.frag permuteAtLowestHeightAsm permuteAtLowestHeight_at) :=
  L.planner_lookup rfl

theorem planner_map_decl : L.plannerDecls.at (label Names.map) =
    some (L.frag mapAsm map_at) :=
  L.planner_lookup rfl

theorem planner_closestCopy_decl : L.plannerDecls.at (label Names.closestCopy) =
    some (L.frag closestCopyAsm closestCopy_at) :=
  L.planner_lookup rfl

theorem planner_mapInPlace_decl : L.plannerDecls.at (label Names.mapInPlace) =
    some (L.frag mapInPlaceAsm mapInPlace_at) :=
  L.planner_lookup rfl

theorem planner_mapClosestCopies_decl : L.plannerDecls.at (label Names.mapClosestCopies) =
    some (L.frag mapClosestCopiesAsm mapClosestCopies_at) :=
  L.planner_lookup rfl

theorem planner_mapWildcardSlotCopies_decl : L.plannerDecls.at (label Names.mapWildcardSlotCopies) =
    some (L.frag mapWildcardSlotCopiesAsm mapWildcardSlotCopies_at) :=
  L.planner_lookup rfl

theorem planner_keepWildcardSlots_decl : L.plannerDecls.at (label Names.keepWildcardSlots) =
    some (L.frag keepWildcardSlotsAsm keepWildcardSlots_at) :=
  L.planner_lookup rfl

theorem planner_absorbSurplus_decl : L.plannerDecls.at (label Names.absorbSurplus) =
    some (L.frag absorbSurplusAsm absorbSurplus_at) :=
  L.planner_lookup rfl

theorem planner_isRetained_decl : L.plannerDecls.at (label Names.isRetained) =
    some (L.frag isRetainedAsm isRetained_at) :=
  L.planner_lookup rfl

theorem planner_hasOtherRetainedCopy_decl : L.plannerDecls.at (label Names.hasOtherRetainedCopy) =
    some (L.frag hasOtherRetainedCopyAsm hasOtherRetainedCopy_at) :=
  L.planner_lookup rfl

theorem planner_isDemanded_decl : L.plannerDecls.at (label Names.isDemanded) =
    some (L.frag isDemandedAsm isDemanded_at) :=
  L.planner_lookup rfl

theorem planner_classify_decl : L.plannerDecls.at (label Names.classify) =
    some (L.frag classifyAsm classify_at) :=
  L.planner_lookup rfl

theorem planner_resolve_decl : L.plannerDecls.at (label Names.resolve) =
    some (L.frag resolveAsm resolve_at) :=
  L.planner_lookup rfl

theorem planner_isAvailable_decl : L.plannerDecls.at (label Names.isAvailable) =
    some (L.frag isAvailableAsm isAvailable_at) :=
  L.planner_lookup rfl

theorem planner_run_decl : L.plannerDecls.at (label Names.run) =
    some (L.frag runAsm run_at) :=
  L.planner_lookup rfl

set_option maxRecDepth 2000 in
theorem planner_plannerRun_decl : L.plannerDecls.at (label Names.plannerRun) =
    some (L.frag plannerRunAsm plannerRun_at) :=
  L.planner_lookup rfl

end Linked
end Bbu
