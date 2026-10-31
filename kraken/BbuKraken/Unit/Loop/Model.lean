import BbuKraken.Unit.Defs
import BbuKraken.FlatList.Basic

/-!
# `buildBottomUp`: the flat model

- `FInv` (in `Unit/LoopInv.lean`): the invariant of the mapping that the loop keeps. The
  destination of each slot is a target offset, `pos` is the inverse of `dest`, and each target
  offset without a slot is pending (`size + pend = n`). `FInv` gives the preconditions `DestOk`
  and `PermOk`, and `size < n` when a generation is pending.
- The preservation of `FInv` by the units that the loop calls, and the growth of the trace.
- The initial `FInv`: the state of the constructor (`ctor`).

The lemmas are in `Bbu.Flat`, so that the names of the flat model have priority over the names
of the list model in `Bbu`.
-/

namespace Bbu.Flat

theorem max_n : MAX_N = 1024 := rfl

-- A word below `MAX_N` is not `NONE`.
theorem ne_none {x : Word} (h : x.toNat < MAX_N) : x ≠ NONE := by
  intro e; subst e; simp [NONE, max_n] at h

theorem toNat_ofNat_lt {i : Nat} (h : i < MAX_N) : (BitVec.ofNat 64 i).toNat = i := by
  rw [BitVec.toNat_ofNat]; rw [max_n] at h; exact Nat.mod_eq_of_lt (by omega)

section
variable {st : St}

-- `FInv` reads only `targetSize`, `size`, `pend`, `dest` and `pos`.
theorem FInv.of_eq {st' : St} (h : FInv st) (e1 : st'.targetSize = st.targetSize)
    (e2 : st'.size = st.size) (e3 : st'.pend = st.pend) (e4 : st'.dest = st.dest)
    (e5 : st'.pos = st.pos) : FInv st' := by
  obtain ⟨a, b, c, d, e⟩ := h
  exact ⟨by rw [e1]; exact a, by rw [e1, e2, e3]; exact b, by rw [e1, e2, e4]; exact c,
    by rw [e2, e4, e5]; exact d, by rw [e1, e2, e4, e5]; exact e⟩

theorem FInv.size_le (h : FInv st) : st.size.toNat ≤ st.targetSize.toNat := by
  have := h.cnt; omega

theorem FInv.lt_max (h : FInv st) {i : Word} (hi : i < st.targetSize) : i.toNat < MAX_N := by
  have := h.n; rw [BitVec.lt_def] at hi; omega

theorem FInv.lt_max_of_size (h : FInv st) {i : Word} (hi : i < st.size) : i.toNat < MAX_N := by
  have := h.n; have := h.size_le; rw [BitVec.lt_def] at hi; omega

-- A pending generation leaves a free slot.
theorem FInv.size_lt (h : FInv st) (hp : st.pend ≠ 0) : st.size < st.targetSize := by
  have := h.cnt
  have : st.pend.toNat ≠ 0 := fun e => hp (BitVec.eq_of_toNat_eq (by simpa using e))
  rw [BitVec.lt_def]; omega

-- No pending generation: all target offsets have a slot.
theorem FInv.size_eq (h : FInv st) (hp : st.pend = 0) : st.size = st.targetSize := by
  have := h.cnt; rw [hp] at this; exact BitVec.eq_of_toNat_eq (by simpa using this)

-- `dest` is injective on the slots.
theorem FInv.dest_inj (h : FInv st) {i j : Word} (hi : i < st.size) (hj : j < st.size)
    (e : get st.dest i = get st.dest j) : i = j := by
  rw [← h.inv i hi, ← h.inv j hj, e]

theorem FInv.ofNat_lt (h : FInv st) {i : Nat} (hi : i < st.size.toNat) :
    BitVec.ofNat 64 i < st.size := by
  have := h.n; have := h.size_le
  rw [BitVec.lt_def, toNat_ofNat_lt (by omega)]; exact hi

theorem FInv.destOk (h : FInv st) : Unit.DestOk st :=
  fun _ hi => .inr (BitVec.lt_def.mp (h.dest _ (h.ofNat_lt hi)))

-- All target offsets have a slot: the destinations are a permutation.
theorem FInv.permOk (h : FInv st) (hn : st.size = st.targetSize) : Unit.PermOk st := by
  refine ⟨fun i hi => ?_, fun i hi j hj e => ?_⟩
  · have := h.dest _ (h.ofNat_lt hi); rw [hn]; exact BitVec.lt_def.mp this
  · have e' := congrArg BitVec.toNat (h.dest_inj (h.ofNat_lt hi) (h.ofNat_lt hj) e)
    have := h.n; have := h.size_le
    rwa [toNat_ofNat_lt (by omega), toNat_ofNat_lt (by omega)] at e'

end

/-! ## `swapDestinations` -/

theorem swapDestinations_trace (st : St) (a b : Word) :
    (swapDestinations st a b).trace = st.trace := rfl

theorem swapDestinations_size (st : St) (a b : Word) :
    (swapDestinations st a b).size = st.size := rfl

theorem FInv.swapDestinations {st : St} (h : FInv st) {a b : Word} (ha : a < st.size)
    (hb : b < st.size) : FInv (swapDestinations st a b) := by
  have hda := h.dest a ha
  have hdb := h.dest b hb
  have ma := h.lt_max_of_size ha
  have mb := h.lt_max_of_size hb
  have mda := h.lt_max hda
  have mdb := h.lt_max hdb
  have nda := ne_none mda
  have ndb := ne_none mdb
  have ia := h.inv a ha
  have dA : get (put (put st.dest a (get st.dest b)) b (get st.dest a)) a
      = if a = b then get st.dest a else get st.dest b := by
    rw [get_put _ _ _ mb, get_put _ _ _ ma]; by_cases e : a = b <;> simp [e]
  have dB : get (put (put st.dest a (get st.dest b)) b (get st.dest a)) b = get st.dest a := by
    rw [get_put_self _ _ mb]
  have dX : ∀ x, x ≠ a → x ≠ b →
      get (put (put st.dest a (get st.dest b)) b (get st.dest a)) x = get st.dest x := by
    intro x xa xb; rw [get_put_ne _ _ xb, get_put_ne _ _ xa]
  unfold Flat.swapDestinations
  dsimp only
  rw [dA, dB]
  by_cases eab : a = b
  · -- One slot: nothing changes.
    subst eab
    rw [ite_eq_left rfl, ite_eq_left nda, ite_eq_left nda]
    have dE : ∀ x, get (put (put st.dest a (get st.dest a)) a (get st.dest a)) x
        = get st.dest x := by
      intro x; rw [get_put _ _ _ ma, get_put _ _ _ ma]; by_cases e : x = a <;> simp [e]
    have pE : ∀ x, get (put (put st.pos (get st.dest a) a) (get st.dest a) a) x
        = get st.pos x := by
      intro x; rw [get_put _ _ _ mda, get_put _ _ _ mda]; by_cases e : x = get st.dest a <;> simp [e, ia]
    refine ⟨h.n, h.cnt, fun i hi => ?_, fun i hi => ?_, fun d hd => ?_⟩
    · show get (put (put st.dest a (get st.dest a)) a (get st.dest a)) i < _
      rw [dE]; exact h.dest i hi
    · show get (put (put st.pos (get st.dest a) a) (get st.dest a) a)
        (get (put (put st.dest a (get st.dest a)) a (get st.dest a)) i) = i
      rw [dE, pE]; exact h.inv i hi
    · show get (put (put st.pos (get st.dest a) a) (get st.dest a) a) d = NONE ∨
        (get (put (put st.pos (get st.dest a) a) (get st.dest a) a) d < st.size ∧
          get (put (put st.dest a (get st.dest a)) a (get st.dest a))
            (get (put (put st.pos (get st.dest a) a) (get st.dest a) a) d) = d)
      rw [pE, dE]; exact h.pos d hd
  · rw [ite_eq_right eab, ite_eq_left ndb, ite_eq_left nda]
    have hne : get st.dest a ≠ get st.dest b := fun e => eab (h.dest_inj ha hb e)
    have pX : ∀ x, get (put (put st.pos (get st.dest b) a) (get st.dest a) b) x
        = if x = get st.dest a then b else if x = get st.dest b then a else get st.pos x := by
      intro x; rw [get_put _ _ _ mda, get_put _ _ _ mdb]
    rw [ite_eq_right eab] at dA
    refine ⟨h.n, h.cnt, fun i hi => ?_, fun i hi => ?_, fun d hd => ?_⟩
    · show get (put (put st.dest a (get st.dest b)) b (get st.dest a)) i < _
      by_cases xa : i = a
      · subst xa; rw [dA]; exact hdb
      by_cases xb : i = b
      · subst xb; rw [dB]; exact hda
      rw [dX i xa xb]; exact h.dest i hi
    · show get (put (put st.pos (get st.dest b) a) (get st.dest a) b)
        (get (put (put st.dest a (get st.dest b)) b (get st.dest a)) i) = i
      by_cases xa : i = a
      · subst xa; rw [dA, pX, ite_eq_right (Ne.symm hne), ite_eq_left rfl]
      by_cases xb : i = b
      · subst xb; rw [dB, pX, ite_eq_left rfl]
      rw [dX i xa xb, pX]
      have n1 : get st.dest i ≠ get st.dest a := fun e => xa (h.dest_inj hi ha e)
      have n2 : get st.dest i ≠ get st.dest b := fun e => xb (h.dest_inj hi hb e)
      rw [ite_eq_right n1, ite_eq_right n2]; exact h.inv i hi
    · show get (put (put st.pos (get st.dest b) a) (get st.dest a) b) d = NONE ∨
        (get (put (put st.pos (get st.dest b) a) (get st.dest a) b) d < st.size ∧
          get (put (put st.dest a (get st.dest b)) b (get st.dest a))
            (get (put (put st.pos (get st.dest b) a) (get st.dest a) b) d) = d)
      rw [pX]
      by_cases e1 : d = get st.dest a
      · rw [ite_eq_left e1, dB]; exact .inr ⟨hb, e1.symm⟩
      rw [ite_eq_right e1]
      by_cases e2 : d = get st.dest b
      · rw [ite_eq_left e2, dA]; exact .inr ⟨ha, e2.symm⟩
      rw [ite_eq_right e2]
      rcases h.pos d hd with hn | ⟨hp, hd'⟩
      · exact .inl hn
      · refine .inr ⟨hp, ?_⟩
        have pa : get st.pos d ≠ a := fun e => e1 (by rw [← hd', e])
        have pb : get st.pos d ≠ b := fun e => e2 (by rw [← hd', e])
        rw [dX _ pa pb]; exact hd'

/-! ## `swapWith` -/

-- `swapWith` is done: the mapping keeps `FInv`, the trace has one more operation, and the size
-- does not change.
theorem FInv.swapWith {st : St} (h : FInv st) {p : Word} (hd : (swapWith st p).1 = .done) :
    FInv (swapWith st p).2 ∧ (swapWith st p).2.trace.length = st.trace.length + 1
      ∧ (swapWith st p).2.size = st.size := by
  unfold Flat.swapWith at hd ⊢
  split at hd
  · cases hd
  rename_i hp
  split at hd
  · cases hd
  rename_i hf
  dsimp only at hd ⊢
  split at hd
  · cases hd
  rename_i hdep
  rw [ite_eq_right hp, ite_eq_right hf, ite_eq_right hdep]
  have hp' : p < st.size := Decidable.not_not.mp hp
  have h1 : FInv (stackSwap st p) := h.of_eq rfl rfl rfl rfl rfl
  refine ⟨h1.swapDestinations hp' ?_, by simp [Flat.swapDestinations, stackSwap], rfl⟩
  show st.size - 1 < st.size
  bv_omega

/-! ## `produce` and `generate` -/

-- The state after an action that is done: one more slot, bound for `t`.
structure Grow (st st' : St) (t : Word) : Prop where
  none : get st.pos t = NONE
  size : st'.size = st.size + 1
  trace : ∃ op, st'.trace = st.trace ++ [op]
  dest : st'.dest = put st.dest st.size t
  pos : st'.pos = put st.pos t st.size
  pend : st'.pend = st.pend
  tsize : st'.targetSize = st.targetSize

section
variable {st : St} {t : Word}

theorem push_grow {x : StackSlot} (h : (push st x t).1 = .done) : Grow st (push st x t).2 t := by
  unfold Flat.push at *
  dsimp only at h ⊢
  split at h
  · simp at h
  · rename_i hp
    simp only [hp, ↓reduceIte]
    exact ⟨by simpa [stackPush] using hp, rfl, ⟨_, rfl⟩,
      by simp [Flat.bind, stackPush, BitVec.add_sub_cancel],
      by simp [Flat.bind, stackPush, BitVec.add_sub_cancel], rfl, rfl⟩

theorem dup_grow {c : Word} (h : (dup st c t).1 = .done) : Grow st (dup st c t).2 t := by
  unfold Flat.dup at *
  dsimp only at h ⊢
  split at h
  · simp at h
  · rename_i hk
    split at h
    · simp at h
    · rename_i hp
      simp only [hk, hp, ↓reduceIte]
      exact ⟨by simpa [stackDup] using hp, rfl, ⟨_, rfl⟩,
        by simp [Flat.bind, stackDup, BitVec.add_sub_cancel],
        by simp [Flat.bind, stackDup, BitVec.add_sub_cancel], rfl, rfl⟩

-- `produce` is done: `Grow`, and one less pending generation.
theorem produce_grow (h : (produce st t).1 = .done) :
    ∃ st', Grow st st' t ∧ (produce st t).2 = { st' with pend := st.pend - 1 } := by
  unfold Flat.produce at *
  dsimp only at h ⊢
  generalize hr : (if isJunk (get st.target t) then push st (get st.target t) t
      else if shallowestCopyPosition st (get st.target t) ≠ NONE ∧
          isDupReachable st (shallowestCopyPosition st (get st.target t)) = true then
        dup st (shallowestCopyPosition st (get st.target t)) t
      else if (canBeFreelyGenerated (get st.target t) ||
          isSpilled st (get st.target t)) = true then
        push st (get st.target t) t
      else if shallowestCopyPosition st (get st.target t) ≠ NONE then
        blockDupUnreachable st (shallowestCopyPosition st (get st.target t))
      else (Status.assertionFailed, st)) = r at h ⊢
  have key : r.1 = .done → Grow st r.2 t := by
    subst hr
    split
    · exact push_grow
    split
    · exact dup_grow
    split
    · exact push_grow
    split
    · intro h'
      unfold blockDupUnreachable block at h'
      split at h' <;> simp at h'
    · simp
  by_cases h1 : r.1 = .done
  · have g := key h1
    simp only [h1, ne_eq, not_true_eq_false, ↓reduceIte] at h ⊢
    split at h
    · simp at h
    · rename_i h2
      simp only [h2, ↓reduceIte]
      exact ⟨r.2, g, by rw [g.pend]⟩
  · simp [h1] at h

theorem Grow.trace_length {st' : St} (g : Grow st st' t) :
    st'.trace.length = st.trace.length + 1 := by
  obtain ⟨op, e⟩ := g.trace; rw [e]; simp

-- A generation keeps `FInv`.
theorem FInv.grow (h : FInv st) (hp : st.pend ≠ 0) {st' : St} (g : Grow st st' t)
    (ht : t < st.targetSize) : FInv { st' with pend := st.pend - 1 } := by
  have hsl := h.size_lt hp
  have ms := h.lt_max hsl
  have mt := h.lt_max ht
  have hpn : st.pend.toNat ≠ 0 := fun e => hp (BitVec.eq_of_toNat_eq (by simpa using e))
  have hsz : (st.size + 1).toNat = st.size.toNat + 1 := by
    rw [max_n] at ms; bv_omega
  have hlt1 : ∀ i, i < st.size + 1 → i ≠ st.size → i < st.size := by
    intro i hi hne; rw [BitVec.lt_def] at *; rw [hsz] at hi
    have : i.toNat ≠ st.size.toNat := fun e => hne (BitVec.eq_of_toNat_eq e)
    omega
  refine ⟨?_, ?_, fun i hi => ?_, fun i hi => ?_, fun d hd => ?_⟩
  · show st'.targetSize.toNat ≤ _; rw [g.tsize]; exact h.n
  · show st'.size.toNat + (st.pend - 1).toNat = st'.targetSize.toNat
    have := h.cnt
    rw [g.size, g.tsize, hsz]
    have : (st.pend - 1).toNat = st.pend.toNat - 1 := by bv_omega
    omega
  · show get st'.dest i < st'.targetSize
    rw [g.dest, g.tsize, get_put _ _ _ ms]
    split
    · exact ht
    · rename_i hne; replace hi : i < st'.size := hi; rw [g.size] at hi
      exact h.dest i (hlt1 i hi hne)
  · show get st'.pos (get st'.dest i) = i
    replace hi : i < st'.size := hi
    rw [g.dest, g.pos, get_put _ _ _ ms]
    split
    · rename_i e; subst e; rw [get_put_self _ _ mt]
    · rename_i hne
      rw [g.size] at hi
      have hi' := hlt1 i hi hne
      have hn : get st.dest i ≠ t := by
        intro e
        have := h.inv i hi'
        rw [e, g.none] at this
        exact ne_none (h.lt_max_of_size hi') this.symm
      rw [get_put_ne _ _ hn]; exact h.inv i hi'
  · show get st'.pos d = NONE ∨ (get st'.pos d < st'.size ∧ get st'.dest (get st'.pos d) = d)
    replace hd : d < st'.targetSize := hd
    rw [g.tsize] at hd
    rw [g.pos, g.size, g.dest, get_put _ _ _ mt]
    split
    · rename_i e; subst e
      refine .inr ⟨?_, get_put_self _ _ ms⟩
      rw [BitVec.lt_def, hsz]; omega
    · rename_i hne
      rcases h.pos d hd with hn | ⟨hl, he⟩
      · exact .inl hn
      · refine .inr ⟨?_, ?_⟩
        · rw [BitVec.lt_def, hsz]; rw [BitVec.lt_def] at hl; omega
        · have : get st.pos d ≠ st.size := fun e => by
            rw [e] at hl; exact (BitVec.lt_irrefl _ hl)
          rw [get_put_ne _ _ this]; exact he

theorem gen_fail (h : ¬t < st.targetSize) : generate st t = (.assertionFailed, st) := by
  simp [Flat.generate, h]

theorem gen_prod (h : t < st.targetSize) (hp : (produce st t).1 ≠ .done) :
    generate st t = produce st t := by
  simp [Flat.generate, h, hp]

-- `produce` is done: `generate` is the branch after `produce`.
theorem gen_after (h : t < st.targetSize) (hp : (produce st t).1 = .done) :
    generate st t =
      if t + 1 < (produce st t).2.size ∧ ¬isFinal (produce st t).2 t then
        if get (produce st t).2.data t = get (produce st t).2.data ((produce st t).2.size - 1) then
          (.done, swapDestinations (produce st t).2 t ((produce st t).2.size - 1))
        else if isSwapReachable (produce st t).2 t then swapWith (produce st t).2 t
        else (.done, (produce st t).2)
      else (.done, (produce st t).2) := by
  unfold Flat.generate
  dsimp only
  rw [ite_eq_right (Decidable.not_not.mpr h), ite_eq_right (Decidable.not_not.mpr hp)]

-- `generate` is done: `FInv`, and at most two more operations.
theorem FInv.generate (h : FInv st) (hp : st.pend ≠ 0) (hd : (generate st t).1 = .done) :
    FInv (generate st t).2 ∧ (generate st t).2.trace.length ≤ st.trace.length + 2 := by
  by_cases ht : t < st.targetSize
  case neg => rw [gen_fail ht] at hd; cases hd
  by_cases h1 : (produce st t).1 = .done
  case neg => rw [gen_prod ht h1] at hd; exact absurd hd h1
  obtain ⟨st', g, e⟩ := produce_grow h1
  have hX : FInv (produce st t).2 := by rw [e]; exact h.grow hp g ht
  have tl : (produce st t).2.trace.length = st.trace.length + 1 := by
    rw [e]; exact g.trace_length
  rw [gen_after ht h1] at hd ⊢
  split
  · rename_i hc
    have mt := h.lt_max ht
    have htl : t < (produce st t).2.size := by
      have := hc.1; rw [max_n] at mt; bv_omega
    have htop : (produce st t).2.size - 1 < (produce st t).2.size := by
      have := hc.1; bv_omega
    rw [ite_eq_left hc] at hd
    split
    · exact ⟨hX.swapDestinations htl htop, by rw [swapDestinations_trace]; omega⟩
    · rename_i he
      rw [ite_eq_right he] at hd
      split
      · rename_i hr
        rw [ite_eq_left hr] at hd
        have := hX.swapWith hd
        exact ⟨this.1, by omega⟩
      · exact ⟨hX, by dsimp only; omega⟩
  · exact ⟨hX, by dsimp only; omega⟩

end

end Bbu.Flat
