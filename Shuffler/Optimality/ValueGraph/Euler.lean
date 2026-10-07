import Shuffler.Optimality.ValueGraph.Theorems
import Mathlib.Data.Multiset.Count

namespace Shuffler.Optimality.ValueGraph

section Euler

variable {ι : Type} [DecidableEq ι]

def Trail (start finish : ι → Value) : Value → Value → List ι → Prop
  | first, last, [] => first = last
  | first, last, edge :: rest => first = start edge ∧ Trail start finish (finish edge) last rest

def vertexCounts (endpoint : ι → Value) (edges : List ι) : Multiset Value :=
  edges.map endpoint

def Balanced (start finish : ι → Value) (edges : List ι) : Prop :=
  vertexCounts start edges = vertexCounts finish edges

-- Each pending entry records a vertex and the edge that entered it. The
-- final entry is the root, which has no incoming edge.
def PendingPath (start finish : ι → Value) (root : Value) :
    List (Value × Option ι) → Prop
  | [] => True
  | [(vertex, incoming)] => vertex = root ∧ incoming = none
  | (vertex, incoming) :: (parent, previous) :: rest =>
      ∃ edge, incoming = some edge ∧ start edge = parent ∧ finish edge = vertex ∧
        PendingPath start finish root ((parent, previous) :: rest)

def WalkInvariant (start finish : ι → Value) (root : Value)
    (pending : List (Value × Option ι)) (remaining circuit : List ι) : Prop :=
  ∃ anchor, Trail start finish anchor root circuit ∧
    match pending with
    | [] => anchor = root ∧ Balanced start finish remaining
    | (current, _) :: _ =>
        PendingPath start finish root pending ∧
        vertexCounts start remaining + {anchor} = vertexCounts finish remaining + {current}

theorem vertexCounts_erase (endpoint : ι → Value) (edges : List ι) (edge : ι)
    (he : edge ∈ edges) :
    vertexCounts endpoint edges = {endpoint edge} + vertexCounts endpoint (edges.erase edge) := by
  have h := Multiset.coe_eq_coe.mpr ((List.perm_cons_erase he).map endpoint)
  simpa only [vertexCounts, List.map_cons, Multiset.cons_coe, Multiset.singleton_add] using h

theorem balance_erase (start finish : ι → Value) (remaining : List ι)
    (anchor current : Value) (edge : ι) (he : edge ∈ remaining)
    (hs : start edge = current)
    (hb : vertexCounts start remaining + {anchor} = vertexCounts finish remaining + {current}) :
    vertexCounts start (remaining.erase edge) + {anchor} =
      vertexCounts finish (remaining.erase edge) + {finish edge} := by
  apply add_left_cancel (a := ({current} : Multiset Value))
  calc
    {current} + (vertexCounts start (remaining.erase edge) + {anchor}) =
        vertexCounts start remaining + {anchor} := by
      rw [vertexCounts_erase start remaining edge he, hs]
      ac_rfl
    _ = vertexCounts finish remaining + {current} := hb
    _ = {current} + (vertexCounts finish (remaining.erase edge) + {finish edge}) := by
      rw [vertexCounts_erase finish remaining edge he]
      ac_rfl

omit [DecidableEq ι] in
theorem dead_end_anchor (start finish : ι → Value) (remaining : List ι)
    (anchor current : Value)
    (hb : vertexCounts start remaining + {anchor} = vertexCounts finish remaining + {current})
    (hn : remaining.find? (fun edge => start edge = current) = none) :
    anchor = current := by
  have hnot : current ∉ vertexCounts start remaining := by
    intro hm
    obtain ⟨edge, he, hs⟩ := List.mem_map.mp hm
    have hfind : (remaining.find? (fun edge => start edge = current)).isSome := by
      exact List.find?_isSome.mpr ⟨edge, he, by simp [hs]⟩
    simp [hn] at hfind
  by_contra hne
  have hc := congrArg (Multiset.count current) hb
  simp [Multiset.count_eq_zero_of_notMem hnot, Ne.symm hne] at hc

theorem walk_push_invariant (start finish : ι → Value) (root vertex : Value)
    (incoming : Option ι) (pending : List (Value × Option ι)) (remaining circuit : List ι)
    (hinv : WalkInvariant start finish root ((vertex, incoming) :: pending) remaining circuit)
    (edge : ι) (he : edge ∈ remaining) (hs : start edge = vertex) :
    WalkInvariant start finish root
      ((finish edge, some edge) :: (vertex, incoming) :: pending) (remaining.erase edge) circuit := by
  obtain ⟨anchor, htrail, hpath, hbalance⟩ := hinv
  exact ⟨anchor, htrail, ⟨edge, rfl, hs, rfl, hpath⟩,
    balance_erase start finish remaining anchor vertex edge he hs hbalance⟩

omit [DecidableEq ι] in
theorem walk_pop_invariant (start finish : ι → Value) (root vertex : Value)
    (incoming : Option ι) (pending : List (Value × Option ι)) (remaining circuit : List ι)
    (hinv : WalkInvariant start finish root ((vertex, incoming) :: pending) remaining circuit)
    (hn : remaining.find? (fun edge => start edge = vertex) = none) :
    WalkInvariant start finish root pending remaining (incoming.toList ++ circuit) := by
  obtain ⟨anchor, htrail, hpath, hbalance⟩ := hinv
  have ha := dead_end_anchor start finish remaining anchor vertex hbalance hn
  subst anchor
  have hb : Balanced start finish remaining := add_right_cancel hbalance
  cases pending with
  | nil =>
      obtain ⟨rfl, rfl⟩ := hpath
      exact ⟨_, htrail, rfl, hb⟩
  | cons entry rest =>
      rcases entry with ⟨parent, previous⟩
      obtain ⟨edge, rfl, hs, hf, hpath⟩ := hpath
      exact ⟨parent, ⟨hs.symm, hf ▸ htrail⟩, hpath, congrArg (· + {parent}) hb⟩

-- Two units per unused edge and one per pending entry bound the remaining
-- traversal steps. Thus the caller's fuel is a proved bound, not a timeout.
theorem walk_trail (start finish : ι → Value) (root : Value)
    (fuel : Nat) (pending : List (Value × Option ι)) (remaining circuit : List ι)
    (hinv : WalkInvariant start finish root pending remaining circuit)
    (hfuel : 2 * remaining.length + pending.length ≤ fuel) :
    Trail start finish root root (walk start finish fuel pending remaining circuit).1 ∧
    Balanced start finish (walk start finish fuel pending remaining circuit).2 := by
  induction fuel generalizing pending remaining circuit with
  | zero =>
      have hp : pending = [] := List.length_eq_zero_iff.mp (by omega)
      subst pending
      obtain ⟨anchor, ht, rfl, hb⟩ := hinv
      exact ⟨ht, hb⟩
  | succ fuel ih =>
      cases pending with
      | nil =>
          obtain ⟨anchor, ht, rfl, hb⟩ := hinv
          exact ⟨ht, hb⟩
      | cons entry pending =>
          rcases entry with ⟨vertex, incoming⟩
          simp only [walk]
          split
          · rename_i edge he
            have hm := List.mem_of_find?_eq_some he
            have hs : start edge = vertex := of_decide_eq_true
              (List.find?_some (p := fun edge => decide (start edge = vertex)) he)
            apply ih _ _ _ (walk_push_invariant start finish root vertex incoming pending
              remaining circuit hinv edge hm hs)
            have hl := List.length_erase_of_mem hm
            have hpos := List.length_pos_of_mem hm
            simp only [List.length_cons] at hfuel ⊢
            omega
          · rename_i hn
            apply ih _ _ _ (walk_pop_invariant start finish root vertex incoming pending
              remaining circuit hinv hn)
            simp only [List.length_cons] at hfuel
            omega

theorem tour_trail (start finish : ι → Value) (first : ι) (edges : List ι)
    (hb : Balanced start finish edges) :
    Trail start finish (start first) (start first) (tour start finish first edges).1 ∧
    Balanced start finish (tour start finish first edges).2 := by
  apply walk_trail
  · exact ⟨start first, rfl, ⟨rfl, rfl⟩, congrArg (· + {start first}) hb⟩
  · simp

def pendingEdges (pending : List (Value × Option ι)) : Multiset ι :=
  pending.filterMap Prod.snd

theorem walk_partition (start finish : ι → Value)
    (fuel : Nat) (pending : List (Value × Option ι)) (remaining circuit : List ι)
    (hfuel : 2 * remaining.length + pending.length ≤ fuel) :
    ((walk start finish fuel pending remaining circuit).1 : Multiset ι) +
      ((walk start finish fuel pending remaining circuit).2 : Multiset ι) =
      (circuit : Multiset ι) + pendingEdges pending + (remaining : Multiset ι) := by
  induction fuel generalizing pending remaining circuit with
  | zero =>
      have hp : pending = [] := List.length_eq_zero_iff.mp (by omega)
      subst pending
      simp [walk, pendingEdges]
  | succ fuel ih =>
      cases pending with
      | nil => simp [walk, pendingEdges]
      | cons entry pending =>
          rcases entry with ⟨vertex, incoming⟩
          simp only [walk]
          split
          · rename_i edge he
            have hm := List.mem_of_find?_eq_some he
            have hl := List.length_erase_of_mem hm
            have hpos := List.length_pos_of_mem hm
            have hf : 2 * (remaining.erase edge).length +
                (((finish edge, some edge) :: (vertex, incoming) :: pending).length) ≤ fuel := by
              simp only [List.length_cons] at hfuel ⊢
              omega
            rw [ih _ _ _ hf]
            have herase : (remaining : Multiset ι) = {edge} + (remaining.erase edge : Multiset ι) :=
              Multiset.coe_eq_coe.mpr (List.perm_cons_erase hm)
            rw [herase]
            change (circuit : Multiset ι) + ({edge} + pendingEdges ((vertex, incoming) :: pending)) +
              (remaining.erase edge : Multiset ι) =
              (circuit : Multiset ι) + pendingEdges ((vertex, incoming) :: pending) +
                ({edge} + (remaining.erase edge : Multiset ι))
            ac_rfl
          · have hf : 2 * remaining.length + pending.length ≤ fuel := by
              simp only [List.length_cons] at hfuel
              omega
            rw [ih _ _ _ hf]
            cases incoming with
            | none => rfl
            | some edge =>
                change ({edge} + (circuit : Multiset ι)) + pendingEdges pending + (remaining : Multiset ι) =
                  (circuit : Multiset ι) + ({edge} + pendingEdges pending) + (remaining : Multiset ι)
                ac_rfl

theorem tour_partition (start finish : ι → Value) (first : ι) (edges : List ι) :
    ((tour start finish first edges).1 ++ (tour start finish first edges).2).Perm edges := by
  apply Multiset.coe_eq_coe.mp
  simpa only [tour, Multiset.coe_add, pendingEdges, List.filterMap_cons, List.filterMap_nil,
    Multiset.coe_nil, zero_add, add_zero] using
    walk_partition start finish (2 * edges.length + 1) [(start first, none)] edges [] (by simp)

theorem walk_remaining_subset (start finish : ι → Value)
    (fuel : Nat) (pending : List (Value × Option ι)) (remaining circuit : List ι) :
    (walk start finish fuel pending remaining circuit).2 ⊆ remaining := by
  induction fuel generalizing pending remaining circuit with
  | zero => exact List.Subset.refl _
  | succ fuel ih =>
      cases pending with
      | nil => exact List.Subset.refl _
      | cons entry pending =>
          rcases entry with ⟨vertex, incoming⟩
          simp only [walk]
          split
          · intro edge he
            exact List.mem_of_mem_erase (ih _ _ _ he)
          · exact ih _ _ _

theorem tour_remaining_first_notMem (start finish : ι → Value) (first : ι) (rest : List ι)
    (hn : (first :: rest).Nodup) :
    first ∉ (tour start finish first (first :: rest)).2 := by
  unfold tour
  simp only [List.length_cons, Nat.mul_add, Nat.mul_one, walk, List.find?_cons,
    decide_true, List.erase_cons_head]
  intro hm
  have hs := walk_remaining_subset start finish (2 * (rest.length + 1))
    [(finish first, some first), (start first, none)] rest [] hm
  exact hn.notMem hs

theorem tour_remaining_length_lt (start finish : ι → Value) (first : ι) (rest : List ι)
    (hn : (first :: rest).Nodup) :
    (tour start finish first (first :: rest)).2.length < (first :: rest).length := by
  have hp := tour_partition start finish first (first :: rest)
  have hf : first ∈ (tour start finish first (first :: rest)).1 := by
    have hm := hp.mem_iff.mpr (List.mem_cons_self)
    exact (List.mem_append.mp hm).resolve_right (tour_remaining_first_notMem start finish first rest hn)
  have hlen := hp.length_eq
  have hpos : 0 < (tour start finish first (first :: rest)).1.length := List.length_pos_of_mem hf
  simp only [List.length_append] at hlen
  omega

def Circuit (start finish : ι → Value) (edges : List ι) : Prop :=
  ∃ root, Trail start finish root root edges

-- The output circuits partition the supplied edges. The bound on the outer
-- loop follows from strict decrease of the remaining edge count.
theorem decompose_spec (start finish : ι → Value) (fuel : Nat) (edges : List ι)
    (hb : Balanced start finish edges) (hn : edges.Nodup) (hf : edges.length ≤ fuel) :
    (∀ circuit ∈ decompose start finish fuel edges, Circuit start finish circuit) ∧
    (decompose start finish fuel edges).flatten.Perm edges := by
  induction fuel generalizing edges with
  | zero =>
      have he : edges = [] := List.length_eq_zero_iff.mp (by omega)
      subst edges
      simp [decompose]
  | succ fuel ih =>
      cases edges with
      | nil => simp [decompose]
      | cons first rest =>
          have ht := tour_trail start finish first (first :: rest) hb
          have hp := tour_partition start finish first (first :: rest)
          have hn' := (List.nodup_append.mp (hp.nodup_iff.mpr hn)).2.1
          have hl := tour_remaining_length_lt start finish first rest hn
          have hf' : (tour start finish first (first :: rest)).2.length ≤ fuel := by omega
          have hi := ih _ ht.2 hn' hf'
          constructor
          · intro circuit hc
            rcases List.mem_cons.mp hc with rfl | hc
            · exact ⟨start first, ht.1⟩
            · exact hi.1 circuit hc
          · change ((tour start finish first (first :: rest)).1 ++
              (decompose start finish fuel (tour start finish first (first :: rest)).2).flatten).Perm _
            exact (hi.2.append_left _).trans hp

def Exhausted (start finish : ι → Value) (remaining circuit : List ι) : Prop :=
  ∀ edge ∈ circuit, ∀ next ∈ remaining, start next ≠ finish edge

omit [DecidableEq ι] in
theorem pending_incoming_finish (start finish : ι → Value) (root vertex : Value)
    (incoming : Option ι) (pending : List (Value × Option ι))
    (hp : PendingPath start finish root ((vertex, incoming) :: pending))
    (edge : ι) (he : incoming = some edge) : finish edge = vertex := by
  cases pending with
  | nil => simp [PendingPath, he] at hp
  | cons entry rest =>
      rcases entry with ⟨parent, previous⟩
      obtain ⟨actual, ha, _, hf, _⟩ := hp
      have h : actual = edge := Option.some.inj (ha.symm.trans he)
      simpa [h] using hf

omit [DecidableEq ι] in
theorem not_start_of_dead_end (start : ι → Value) (remaining : List ι) (vertex : Value)
    (hn : remaining.find? (fun edge => start edge = vertex) = none) :
    ∀ edge ∈ remaining, start edge ≠ vertex := by
  intro edge he hs
  have hfind : (remaining.find? (fun edge => start edge = vertex)).isSome :=
    List.find?_isSome.mpr ⟨edge, he, by simp [hs]⟩
  simp [hn] at hfind

-- When an edge leaves the pending path, every unused edge at its destination
-- has been consumed. Later steps only remove unused edges, so this fact lasts.
theorem walk_exhausted (start finish : ι → Value) (root : Value)
    (fuel : Nat) (pending : List (Value × Option ι)) (remaining circuit : List ι)
    (hinv : WalkInvariant start finish root pending remaining circuit)
    (hex : Exhausted start finish remaining circuit) :
    Exhausted start finish (walk start finish fuel pending remaining circuit).2
      (walk start finish fuel pending remaining circuit).1 := by
  induction fuel generalizing pending remaining circuit with
  | zero => exact hex
  | succ fuel ih =>
      cases pending with
      | nil => exact hex
      | cons entry pending =>
          rcases entry with ⟨vertex, incoming⟩
          simp only [walk]
          split
          · rename_i edge he
            have hm := List.mem_of_find?_eq_some he
            have hs : start edge = vertex := of_decide_eq_true
              (List.find?_some (p := fun edge => decide (start edge = vertex)) he)
            apply ih _ _ _ (walk_push_invariant start finish root vertex incoming pending
              remaining circuit hinv edge hm hs)
            intro old hold next hnext
            exact hex old hold next (List.mem_of_mem_erase hnext)
          · rename_i hn
            apply ih _ _ _ (walk_pop_invariant start finish root vertex incoming pending
              remaining circuit hinv hn)
            intro old hold next hnext
            rcases List.mem_append.mp hold with hold | hold
            · have hsome : incoming = some old := by
                cases incoming with
                | none => simp at hold
                | some edge =>
                    have h : old = edge := by simpa using hold
                    subst old
                    rfl
              have hfinish := pending_incoming_finish start finish root vertex incoming pending
                hinv.choose_spec.2.1 old hsome
              rw [hfinish]
              exact not_start_of_dead_end start remaining vertex hn next hnext
            · exact hex old hold next hnext

theorem tour_exhausted (start finish : ι → Value) (first : ι) (edges : List ι)
    (hb : Balanced start finish edges) :
    Exhausted start finish (tour start finish first edges).2 (tour start finish first edges).1 := by
  apply walk_exhausted start finish (start first)
  · exact ⟨start first, rfl, ⟨rfl, rfl⟩, congrArg (· + {start first}) hb⟩
  · simp [Exhausted]

end Euler

end Shuffler.Optimality.ValueGraph
