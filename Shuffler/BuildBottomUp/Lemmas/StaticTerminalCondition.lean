import Shuffler.BuildBottomUp.Lemmas.StaticSuffix
import Shuffler.BuildBottomUp.Lemmas.StaticCopyBridge
import Shuffler.BuildBottomUp.Lemmas.StaticCycleBridge
import Shuffler.BuildBottomUp.Lemmas.StaticNoGeneration

namespace Shuffler.BuildBottomUp.Success

-- At the fixed cutoff, either all original holes are complete or the current
-- assigned destination has exactly seventeen stack slots left to process.
theorem terminal_success_iff (initial : State source target spills) (hvalid : initial.Valid)
    (hn : 16 < initial.stack.length) (state : State source target spills)
    (hp : PrefixState initial hvalid (cutoff initial) state) :
    Succeeds (buildBottomUp.loop (cutoff initial) state) (fun _ => True) ↔
      Ready initial (cutoff initial) ∧ Terminal initial := by
  by_cases hfirst : generationEnd initial ≤ boundary initial
  · have hcut : cutoff initial = generationEnd initial := by
      exact Nat.min_eq_right hfirst
    have hp' : PrefixState initial hvalid (generationEnd initial) state := hcut ▸ hp
    have hnone (j : Fin target.length) : state.mapping.symm j ≠ none := by
      intro hj
      obtain ⟨hb, hge⟩ := (hp'.unbound j).mp hj
      have hlt := hole_before_generationEnd initial j ((mem_holes initial j).mpr hb)
      omega
    have hpending : state.pending_generations = 0 := by
      have hz : state.mapping.unmapped_target_slots = 0 :=
        (Mapping.unmapped_target_slots_eq_zero state.mapping).mpr
          (fun j => Option.isSome_iff_ne_none.mpr (hnone j))
      exact hp'.invariant.pending.symm.trans hz
    have hr : Ready initial (generationEnd initial) := hp'.ready_iff.mpr
      (fun j hj => False.elim (hnone j hj))
    have hterminal : Succeeds (buildBottomUp.loop (generationEnd initial) state) (fun _ => True) ↔
        CyclesReady initial (generationEnd initial) := by
      rw [loop_success_iff_completedFixed _ state hp'.invariant hp'.invariant.valid hpending,
        hp'.cycles.fixed_below_iff, cyclesReady_iff initial hvalid]
    simpa only [hcut, Terminal, ite_eq_left hfirst, hr, true_and] using hterminal
  · have hlt : boundary initial < generationEnd initial := by omega
    have hcut : cutoff initial = boundary initial := Nat.min_eq_left hlt.le
    have hp' : PrefixState initial hvalid (boundary initial) state := hcut ▸ hp
    have hc : boundary initial < target.length := boundary_lt initial hvalid hn
    have hwidth : state.stack.length - boundary initial = MAX_SWAP_DEPTH + 1 := by
      rw [hp'.length, prefixWidth_boundary initial hvalid hn]
      rfl
    have hcurrent : boundary initial < state.stack.length := by
      unfold MAX_SWAP_DEPTH at hwidth
      omega
    let current : Fin state.stack.length := ⟨boundary initial, hcurrent⟩
    have hbound : (state.mapping.symm ⟨boundary initial, hc⟩).isSome := by
      apply Option.isSome_iff_ne_none.mpr
      intro hnone
      have hb := ((hp'.unbound ⟨boundary initial, hc⟩).mp hnone).1
      have hi := boundary_bound initial hvalid hn
      simp [hb] at hi
    obtain ⟨carrier, hb⟩ := Option.isSome_iff_exists.mp hbound
    have hpending : state.pending_generations ≠ 0 := by
      intro hz
      have htotal := (Mapping.unmapped_target_slots_eq_zero state.mapping).mp
        (hp'.invariant.pending.trans hz)
      obtain ⟨j, hj, hge⟩ := remaining_hole_of_lt_generationEnd initial (boundary initial) hlt
      have hnone := (hp'.unbound j).mpr ⟨(mem_holes initial j).mp hj, hge⟩
      simpa [hnone] using htotal j
    have hterminal := loop_bound_boundary_success_iff (boundary initial) state hp'.invariant
      hwidth hpending hc current rfl carrier hb
    rw [← hp'.ready_iff, ← hp'.boundarySafe_iff hc current carrier rfl hb] at hterminal
    simpa only [hcut, Terminal, ite_eq_right hfirst] using hterminal

end Shuffler.BuildBottomUp.Success
