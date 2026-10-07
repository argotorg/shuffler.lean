import Shuffler.Optimality.ValueGraph.Circuit

namespace Shuffler.Optimality.ValueGraph

variable {ι : Type} [DecidableEq ι]

-- Every source value used by a completed circuit is absent from the unused
-- edges. A closed circuit has the same source and destination vertex set.
theorem tour_separated (start finish : ι → Value) (first : ι) (edges : List ι)
    (hb : Balanced start finish edges) (hn : edges.Nodup) :
    ∀ edge ∈ (tour start finish first edges).1,
      ∀ next ∈ (tour start finish first edges).2, start edge ≠ start next := by
  have ht := tour_trail start finish first edges hb
  have hp := tour_partition start finish first edges
  have hnodup := (List.nodup_append.mp (hp.nodup_iff.mpr hn)).1
  have hex := tour_exhausted start finish first edges hb
  intro edge he next hn heq
  let circuit := (tour start finish first edges).1
  let previous := circuit.formPerm.symm edge
  have hprev : previous ∈ circuit := by
    rw [← List.formPerm_mem_iff_mem]
    simpa only [previous, Equiv.apply_symm_apply] using he
  have hvalue := Circuit.formPerm start finish circuit ⟨start first, ht.1⟩ hnodup previous hprev
  simp only [previous, Equiv.apply_symm_apply] at hvalue
  exact hex previous hprev next hn (heq.symm.trans hvalue.symm)

def ValueDisjoint (start : ι → Value) (first second : List ι) : Prop :=
  ∀ edge ∈ first, ∀ next ∈ second, start edge ≠ start next

-- The emitted circuits use disjoint value groups. This property is stronger
-- than disjoint occurrence positions and is needed for value-optimality.
theorem decompose_valueDisjoint (start finish : ι → Value) (fuel : Nat) (edges : List ι)
    (hb : Balanced start finish edges) (hn : edges.Nodup) :
    (decompose start finish fuel edges).Pairwise (ValueDisjoint start) := by
  induction fuel generalizing edges with
  | zero => simp [decompose]
  | succ fuel ih =>
      cases edges with
      | nil => simp [decompose]
      | cons first rest =>
          have ht := tour_trail start finish first (first :: rest) hb
          have hp := tour_partition start finish first (first :: rest)
          have hn' := (List.nodup_append.mp (hp.nodup_iff.mpr hn)).2.1
          have hs := tour_separated start finish first (first :: rest) hb hn
          apply List.pairwise_cons.mpr
          constructor
          · intro circuit hc edge he next hnext
            have hgood := decompose_preserves start finish
              (fun next => ∀ edge ∈ (tour start finish first (first :: rest)).1,
                start edge ≠ start next) fuel (tour start finish first (first :: rest)).2
              (fun next hm edge he => hs edge he next hm) circuit hc next hnext
            exact hgood edge he
          · exact ih _ ht.2 hn'

end Shuffler.Optimality.ValueGraph
