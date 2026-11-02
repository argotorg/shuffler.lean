module

public import FlatShuffler.Unit.Defs
import all FlatShuffler.Unit.Defs

@[expose] public section

namespace FlatShuffler.Unit
open FlatShuffler.Sep

theorem nodup_eraseDups {α : Type} [BEq α] [LawfulBEq α] : (l : List α) → l.eraseDups.Nodup
  | [] => List.nodup_nil
  | a :: xs => by
    rw [List.eraseDups_cons, List.nodup_cons]
    refine ⟨fun hm => ?_, nodup_eraseDups _⟩
    rw [List.mem_eraseDups, List.mem_filter] at hm
    simp at hm
termination_by l => l.length
decreasing_by all_goals simp_wf; have := List.length_filter_le (fun b => !b == a) xs; omega

theorem vec_map {n : Nat} (v : Vector Word n) :
    vec (v.toList.map StackSlot.ofWord) =
      Vector.ofFn fun i : Fin maxStackSize => if h : i.val < n then StackSlot.ofWord v[i.val] else default := by
  ext i hi
  by_cases h : i < n <;> simp [vec, h]

end FlatShuffler.Unit
