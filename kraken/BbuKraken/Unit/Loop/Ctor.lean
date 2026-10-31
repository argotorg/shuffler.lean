import BbuKraken.Unit.Loop.Model

/-!
# `buildBottomUp`: the state of the constructor

`FInv.ctor`: for `m ≤ n ≤ MAX_N` and distinct destinations below `n` (`Dests`), the state of the
constructor satisfies `FInv`, and its trace is empty.

The constructor has three folds: it clears `pos` below `n`, binds each slot below `m` to its
destination, and counts the target offsets without a slot.
-/

namespace Bbu.Flat

-- A property that each step of a fold keeps.
theorem foldl_inv {α β : Type} (P : β → Prop) (f : β → α → β) (hf : ∀ b a, P b → P (f b a)) :
    ∀ (l : List α) (b : β), P b → P (l.foldl f b)
  | [], _, h => h
  | a :: l, b, h => foldl_inv P f hf l (f b a) (hf b a h)

theorem mem_offsets {d k : Word} (h : d < k) : d ∈ offsets k := by
  simp only [offsets, List.mem_map, List.mem_range]
  exact ⟨d.toNat, BitVec.lt_def.mp h, BitVec.eq_of_toNat_eq (by simp)⟩

/-! ## The destinations -/

-- The destinations of the slots below `m` are below `n` and distinct.
structure DOk (dests : Vector Word MAX_N) (m n : Word) : Prop where
  lt : ∀ p, p < m → get dests p < n
  inj : ∀ p q, p < m → q < m → get dests p = get dests q → p = q

theorem listDests_length {m : Nat} (d : Vector Word MAX_N) (hm : m ≤ MAX_N) :
    (listDests m d).length = m := by
  simp [listDests, hm]

theorem listDests_getElem {m : Nat} {d : Vector Word MAX_N} {p : Word} (hm : m ≤ MAX_N)
    (hp : p.toNat < m) (h : p.toNat < (listDests m d).length) :
    (listDests m d)[p.toNat] = (get d p).toNat := by
  simp [listDests, get, show p.toNat < MAX_N by omega]

theorem DOk.of_dests {d : Vector Word MAX_N} {m n : Word} (hm : m.toNat ≤ MAX_N)
    (hd : Dests n.toNat (listDests m.toNat d)) : DOk d m n := by
  have hl : ∀ p : Word, p < m → p.toNat < (listDests m.toNat d).length := by
    intro p hp; rw [listDests_length d hm]; exact BitVec.lt_def.mp hp
  refine ⟨fun p hp => ?_, fun p q hp hq e => ?_⟩
  · have := hd.1 _ (hl p hp)
    rw [listDests_getElem hm (BitVec.lt_def.mp hp)] at this
    exact BitVec.lt_def.mpr this
  · have := hd.2 _ (hl p hp) _ (hl q hq)
      (by rw [listDests_getElem hm (BitVec.lt_def.mp hp),
        listDests_getElem hm (BitVec.lt_def.mp hq), e])
    exact BitVec.eq_of_toNat_eq this

/-! ## The first fold: `pos` is `NONE` below `n` -/

theorem fold_none_not_mem (l : List Word) (st : St) {j : Word} (hj : j ∉ l) :
    get (l.foldl (fun st d => { st with pos := put st.pos d NONE }) st).pos j = get st.pos j := by
  induction l generalizing st with
  | nil => rfl
  | cons a l ih =>
    simp only [List.mem_cons, not_or] at hj
    rw [List.foldl_cons, ih _ hj.2]
    exact get_put_ne _ _ hj.1

theorem fold_none_mem (l : List Word) (st : St) {j : Word} (hj : j ∈ l) (hm : j.toNat < MAX_N) :
    get (l.foldl (fun st d => { st with pos := put st.pos d NONE }) st).pos j = NONE := by
  induction l generalizing st with
  | nil => cases hj
  | cons a l ih =>
    rw [List.foldl_cons]
    by_cases h : j ∈ l
    · exact ih _ h
    · rw [fold_none_not_mem _ _ h]
      have : j = a := by simpa [h] using hj
      subst this
      exact get_put_self _ _ hm

/-! ## The second fold: the bindings -/

section
variable (dests : Vector Word MAX_N) (n : Word)

-- The fold of the bindings of the slots below `k`.
def binds (st : St) (k : Nat) : St :=
  (List.range k).foldl (fun st i => bind st (BitVec.ofNat 64 i) (get dests (BitVec.ofNat 64 i))) st

-- The mapping after the bindings of the slots below `k`.
structure BInv (D P : Vector Word MAX_N) (k : Nat) : Prop where
  dest : ∀ i : Word, i.toNat < k → get D i = get dests i
  inv : ∀ i : Word, i.toNat < k → get P (get dests i) = i
  pos : ∀ d, d < n → get P d = NONE ∨ ((get P d).toNat < k ∧ get dests (get P d) = d)

theorem binds_eq (st : St) (k : Nat) :
    binds dests st k = { st with dest := (binds dests st k).dest, pos := (binds dests st k).pos } := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [binds, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    simp only [binds] at ih
    rw [ih]
    rfl

theorem binds_inv {m : Word} (st : St) (hmn : m ≤ n) (hn : n.toNat ≤ MAX_N) (hd : DOk dests m n)
    (hp : ∀ d, d < n → get st.pos d = NONE) :
    ∀ k, k ≤ m.toNat → BInv dests n (binds dests st k).dest (binds dests st k).pos k := by
  intro k
  induction k with
  | zero => intro _; exact ⟨fun _ h => absurd h (Nat.not_lt_zero _),
      fun _ h => absurd h (Nat.not_lt_zero _), fun d hd => .inl (hp d hd)⟩
  | succ k ih =>
    intro hk
    obtain ⟨ha, hb, hc⟩ := ih (by omega)
    have hm : m.toNat ≤ MAX_N := by rw [BitVec.le_def] at hmn; omega
    have pk : (BitVec.ofNat 64 k).toNat = k := toNat_ofNat_lt (by omega)
    have plt : BitVec.ofNat 64 k < m := by rw [BitVec.lt_def, pk]; omega
    have dlt := hd.lt _ plt
    have mp : (BitVec.ofNat 64 k).toNat < MAX_N := by rw [pk]; omega
    have mdp : (get dests (BitVec.ofNat 64 k)).toNat < MAX_N := by
      rw [BitVec.lt_def] at dlt; omega
    have e : binds dests st (k + 1) = bind (binds dests st k) (BitVec.ofNat 64 k)
        (get dests (BitVec.ofNat 64 k)) := by
      simp only [binds, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [e]
    simp only [Flat.bind]
    have ne_k : ∀ i : Word, i.toNat < k + 1 → i ≠ BitVec.ofNat 64 k → i.toNat < k := by
      intro i hi hne
      have : i.toNat ≠ k := fun h' => hne (BitVec.eq_of_toNat_eq (by rw [pk]; exact h'))
      omega
    refine ⟨fun i hi => ?_, fun i hi => ?_, fun d hd' => ?_⟩
    · rw [get_put _ _ _ mp]
      split
      · rename_i h'; rw [h']
      · rename_i hne; exact ha i (ne_k i hi hne)
    · by_cases hik : i = BitVec.ofNat 64 k
      · subst hik; exact get_put_self _ _ mdp
      · have hi' := ne_k i hi hik
        have ilt : i < m := by rw [BitVec.lt_def]; omega
        have : get dests i ≠ get dests (BitVec.ofNat 64 k) :=
          fun e' => hik (hd.inj _ _ ilt plt e')
        rw [get_put_ne _ _ this]; exact hb i hi'
    · rw [get_put _ _ _ mdp]
      split
      · rename_i h'; exact .inr ⟨by rw [pk]; omega, h'.symm⟩
      · rcases hc d hd' with h' | ⟨h1, h2⟩
        · exact .inl h'
        · exact .inr ⟨by omega, h2⟩

end

/-! ## The third fold: the count -/

theorem fold_pend (l : List Word) (st : St) :
    l.foldl (fun st d => if get st.pos d = NONE then { st with pend := st.pend + 1 } else st) st
      = { st with pend := st.pend + BitVec.ofNat 64 (l.countP (fun d => get st.pos d = NONE)) } := by
  induction l generalizing st with
  | nil => cases st; simp
  | cons a l ih =>
    rw [List.foldl_cons]
    by_cases h : get st.pos a = NONE
    · rw [ite_eq_left h, ih]
      simp only [List.countP_cons, h, decide_true, ↓reduceIte]
      congr 1
      rw [BitVec.ofNat_add]; ac_rfl
    · rw [ite_eq_right h, ih]
      simp [h]

/-! ## The constructor -/

-- The state of the constructor satisfies `FInv`, and its trace is empty.
theorem FInv.ctor {data target : Vector StackSlot MAX_N} {m n : Word} {dests : Vector Word MAX_N}
    {spills : BitVec 32 → BitVec 8} {u : Uninit} (hmn : m ≤ n) (hn : n.toNat ≤ MAX_N)
    (hd : Dests n.toNat (listDests m.toNat dests)) :
    FInv (ctor data m target n dests spills u) ∧ (ctor data m target n dests spills u).trace = [] := by
  have hm : m.toNat ≤ MAX_N := by rw [BitVec.le_def] at hmn; omega
  have hk := DOk.of_dests hm hd
  unfold Flat.ctor
  dsimp only
  generalize hs1 : (offsets n).foldl (fun st d => { st with pos := put st.pos d NONE })
    ({ target, targetSize := n, spills, data, size := m, trace := [], dest := u.dest, pos := u.pos,
       pend := 0, blockedOffset := u.blockedOffset, blockedExcess := u.blockedExcess } : St) = s1
  -- The first fold.
  have f1 : s1.targetSize = n ∧ s1.size = m ∧ s1.trace = [] ∧ s1.pend = 0 := by
    rw [← hs1]
    refine foldl_inv (fun s : St => s.targetSize = n ∧ s.size = m ∧ s.trace = [] ∧ s.pend = 0)
      (fun st d => { st with pos := put st.pos d NONE }) (fun _ _ h => h) _ _ ?_
    exact ⟨rfl, rfl, rfl, rfl⟩
  have p1 : ∀ d, d < n → get s1.pos d = NONE := by
    intro d hd'
    rw [← hs1]
    exact fold_none_mem _ _ (mem_offsets hd') (by rw [BitVec.lt_def] at hd'; omega)
  -- The second fold.
  have e2 : (offsets m).foldl (fun st p => bind st p (get dests p)) s1 = binds dests s1 m.toNat := by
    simp only [offsets, List.foldl_map, binds]
  rw [e2]
  have b2 := binds_inv dests n s1 hmn hn hk p1 m.toNat (Nat.le_refl _)
  generalize hD : (binds dests s1 m.toNat).dest = D at b2
  generalize hP : (binds dests s1 m.toNat).pos = P at b2
  rw [binds_eq, hD, hP, fold_pend]
  obtain ⟨b2a, b2b, b2c⟩ := b2
  obtain ⟨t1, t2, t3, t4⟩ := f1
  -- The count.
  have hiff : ∀ d ∈ List.range n.toNat,
      (get P (BitVec.ofNat 64 d) = NONE) ↔ d ∉ listDests m.toNat dests := by
    intro d hdr
    rw [List.mem_range] at hdr
    have dn : BitVec.ofNat 64 d < n := by
      rw [BitVec.lt_def, toNat_ofNat_lt (by omega)]; exact hdr
    rw [List.mem_iff_getElem]
    constructor
    · rintro hN ⟨i, hi0, he⟩
      have hi : i < m.toNat := by rwa [listDests_length dests hm] at hi0
      have hi' : (BitVec.ofNat 64 i).toNat < m.toNat := by rw [toNat_ofNat_lt (by omega)]; exact hi
      have e := listDests_getElem (d := dests) hm hi' (by rw [listDests_length dests hm]; exact hi')
      simp only [toNat_ofNat_lt (show i < MAX_N by omega)] at e
      rw [e] at he
      have : get dests (BitVec.ofNat 64 i) = BitVec.ofNat 64 d :=
        BitVec.eq_of_toNat_eq (by rw [he, toNat_ofNat_lt (by omega)])
      have := b2b _ hi'
      rw [‹get dests (BitVec.ofNat 64 i) = _›, hN] at this
      exact ne_none (by rw [toNat_ofNat_lt (by omega)]; omega) this.symm
    · intro hnm
      rcases b2c _ dn with h' | ⟨h1, h2⟩
      · exact h'
      · exfalso
        apply hnm
        refine ⟨(get P (BitVec.ofNat 64 d)).toNat, by rw [listDests_length dests hm]; omega, ?_⟩
        rw [listDests_getElem hm h1, h2, toNat_ofNat_lt (by omega)]
  have hc : (offsets n).countP (fun d => get P d = NONE) = n.toNat - m.toNat := by
    rw [offsets, List.countP_map]
    rw [List.countP_congr (q := fun d => decide (d ∉ listDests m.toNat dests))
      (fun d hd' => by simpa using hiff d hd')]
    rw [countP_not_mem hd, listDests_length dests hm]
  refine ⟨⟨?_, ?_, fun i hi => ?_, fun i hi => ?_, fun d hd' => ?_⟩, t3⟩
  · show s1.targetSize.toNat ≤ MAX_N; rw [t1]; exact hn
  · show s1.size.toNat + (s1.pend + BitVec.ofNat 64 _).toNat = s1.targetSize.toNat
    rw [t1, t2, t4, hc]
    rw [BitVec.le_def] at hmn; rw [max_n] at hn; bv_omega
  · replace hi : i < s1.size := hi
    rw [t2] at hi
    show get D i < s1.targetSize
    rw [t1, b2a i (BitVec.lt_def.mp hi)]; exact hk.lt i hi
  · replace hi : i < s1.size := hi
    rw [t2] at hi
    show get P (get D i) = i
    rw [b2a i (BitVec.lt_def.mp hi)]; exact b2b i (BitVec.lt_def.mp hi)
  · replace hd' : d < s1.targetSize := hd'
    rw [t1] at hd'
    show get P d = NONE ∨ (get P d < s1.size ∧ get D (get P d) = d)
    rw [t2]
    rcases b2c d hd' with h' | ⟨h1, h2⟩
    · exact .inl h'
    · exact .inr ⟨BitVec.lt_def.mpr h1, by rw [b2a _ h1]; exact h2⟩


-- The state of the constructor: `HInv` at `T = 0`.
theorem HInv.ctor {data target : Vector StackSlot MAX_N} {m n : Word}
    {dests : Vector Word MAX_N} {spills : BitVec 32 → BitVec 8} {u : Uninit} {x : Nat} (hmn : m ≤ n)
    (hn : n.toNat ≤ MAX_N) (hd : Dests n.toNat (listDests m.toNat dests)) :
    HInv (ctor data m target n dests spills u) 0 x := by
  obtain ⟨hf, ht⟩ := FInv.ctor (data := data) (target := target) (spills := spills) (u := u)
    hmn hn hd
  have := hf.cnt
  refine ⟨hf, by simp, ?_⟩
  rw [ht]; simp only [List.length_nil]; omega

end Bbu.Flat
