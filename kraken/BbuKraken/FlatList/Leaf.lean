module

public import BbuKraken.FlatList.Basic
import all BbuKraken.FlatList.Basic

@[expose] public section

/-!
The leaf units of the flat model keep `Sim`: `push`, `dup`, `swapDestinations`, `swapWith`
and `shallowestCopyPosition`.
-/

namespace Bbu.Flat

/-! ## `optW` -/

theorem optW_ne_NONE {x : Option Nat} (hx : ∀ p, x = some p → p < 2 ^ 64 - 1) :
    optW x ≠ NONE ↔ x.isSome := by
  cases x with
  | none => simp [optW]
  | some p =>
    simp only [optW, Option.isSome_some, iff_true]
    have := hx p rfl
    exact ne_NONE (by rw [toNat_ofNat_of_lt (by omega)]; exact this)

/-! ## The list accessors -/

theorem slot_append {l : List Slot} {x : Slot} {i : Nat} :
    (l ++ [x])[i]? = if i < l.length then l[i]? else if i = l.length then some x else none := by
  by_cases h1 : i < l.length
  · rw [ite_eq_left h1, List.getElem?_append_left h1]
  · rw [ite_eq_right h1, List.getElem?_append_right (by omega)]
    by_cases h2 : i = l.length
    · subst h2; simp
    · rw [ite_eq_right h2, List.getElem?_eq_none (by simp; omega)]

theorem val_append {st st' : Bbu.St} {x : Slot} (h : st'.slots = st.slots ++ [x]) (i : Nat) :
    st'.val i = if i < st.len then st.val i else if i = st.len then x.val else default := by
  simp only [Bbu.St.val, Bbu.St.len, h, slot_append]
  by_cases h1 : i < st.slots.length
  · simp [h1]
  · by_cases h2 : i = st.slots.length <;> simp [h1, h2]

theorem dest_append {st st' : Bbu.St} {x : Slot} (h : st'.slots = st.slots ++ [x]) (i : Nat) :
    st'.dest i = if i < st.len then st.dest i else if i = st.len then x.dest else 0 := by
  simp only [Bbu.St.dest, Bbu.St.len, h, slot_append]
  by_cases h1 : i < st.slots.length
  · simp [h1]
  · by_cases h2 : i = st.slots.length <;> simp [h1, h2]

theorem join_set {l : List (Option Nat)} {d : Nat} {x : Option Nat} (hd : d < l.length)
    (d' : Nat) : ((l.set d x)[d']?).join = if d' = d then x else (l[d']?).join := by
  simp only [List.getElem?_set]
  by_cases h : d = d'
  · subst h; simp [hd]
  · simp [h, Ne.symm h]

theorem len_append {st st' : Bbu.St} {x : Slot} (h : st'.slots = st.slots ++ [x]) :
    st'.len = st.len + 1 := by
  simp [Bbu.St.len, h]

section
variable {e : Env} {fs : St} {st : Bbu.St}

theorem Sim.pos_ne_NONE (hs : Sim e fs st) {d : Word} (hd : d.toNat < e.n) :
    get fs.pos d ≠ NONE ↔ (positionOf st d.toNat).isSome := by
  rw [hs.pos d (hs.n ▸ hd)]
  apply optW_ne_NONE
  intro p hp
  have := positionOf_some hs.hpos hp
  have := hs.len_lt
  unfold MAX_N at this
  omega

theorem Sim.size_lt (hs : Sim e fs st) : fs.size.toNat ≤ MAX_N := hs.size ▸ hs.len_lt

/-! ## `add` -/

-- A new top slot `slot` that is bound for `d`.
theorem Sim.add (hs : Sim e fs st) {slot : StackSlot} {d : Word} {op : Op} {st' : Bbu.St}
    (hd : d.toNat < e.n) (hlt : st.len < e.n) (hn : positionOf st d.toNat = none)
    (h1 : st'.slots = st.slots ++ [⟨slot, d.toNat⟩])
    (h2 : st'.positionOf = st.positionOf.set d.toNat (some st.len))
    (h3 : st'.trace = st.trace ++ [op]) (h4 : st'.pendingGenerations = st.pendingGenerations) :
    Sim e { fs with data := put fs.data fs.size slot, size := fs.size + 1,
                    trace := fs.trace ++ [op], dest := put fs.dest fs.size d,
                    pos := put fs.pos d fs.size } st' := by
  have hn' := hs.n
  have hsz := hs.size
  have hle := hs.n_le
  unfold MAX_N at hle
  have hS : fs.size.toNat < MAX_N := by unfold MAX_N; omega
  have hD : d.toNat < MAX_N := by unfold MAX_N; omega
  have hl := hs.hpos.length
  refine ⟨hs.env, hs.n_le, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [len_append h1]
    dsimp only
    rw [BitVec.toNat_add_of_lt (by simp; omega)]
    simp [hsz]
  · rw [len_append h1]; dsimp only; omega
  · intro i hi
    rw [len_append h1] at hi
    rw [val_append h1, get_put _ _ _ hS]
    by_cases h : i = fs.size
    · subst h; simp [hsz]
    · have hi' : i.toNat < st.len := by have := toNat_ne_of_ne h; omega
      rw [ite_eq_right h, ite_eq_left hi', hs.data i hi']
  · intro i hi
    rw [len_append h1] at hi
    rw [dest_append h1, get_put _ _ _ hS]
    by_cases h : i = fs.size
    · subst h; simp [hsz]
    · have hi' : i.toNat < st.len := by have := toNat_ne_of_ne h; omega
      rw [ite_eq_right h, ite_eq_left hi', hs.dest i hi']
  · intro d' hd'
    dsimp only at hd' ⊢
    rw [positionOf, h2, join_set (by omega), get_put _ _ _ hD]
    by_cases h : d' = d
    · subst h; simp [optW, ← hsz]
    · rw [ite_eq_right h, ite_eq_right (toNat_ne_of_ne h), hs.pos d' hd', positionOf]
  · rw [h4]; exact hs.pend
  · rw [h3]; simp [hs.trace]
  · have := hs.hpos.addState (v := slot) (op := op) (hn' ▸ hd) hn
    exact this.congr h2 (by simp [Bbu.St.dests, h1])

/-! ## `push` and `dup` -/

theorem sim_push (hs : Sim e fs st) {slot : StackSlot} {d : Word} (hd : d.toNat < e.n)
    (hlt : st.len < e.n) : SimR e (push fs slot d) (Bbu.add st slot d.toNat (.push slot)) := by
  rw [add_eq]
  have hp : get (stackPush fs slot).pos d ≠ NONE ↔ (positionOf st d.toNat).isSome :=
    hs.pos_ne_NONE hd
  unfold push
  dsimp only
  by_cases h : (positionOf st d.toNat).isSome
  · rw [ite_eq_left h, ite_eq_left (hp.mpr h)]
    exact rfl
  · rw [ite_eq_right h, ite_eq_right (fun h' => h (hp.mp h'))]
    refine ⟨rfl, ?_⟩
    have hn : positionOf st d.toNat = none := Option.not_isSome_iff_eq_none.mp h
    have hf : bind (stackPush fs slot) ((stackPush fs slot).size - 1) d =
        { fs with data := put fs.data fs.size slot, size := fs.size + 1,
                  trace := fs.trace ++ [.push slot], dest := put fs.dest fs.size d,
                  pos := put fs.pos d fs.size } := by
      simp [bind, stackPush, BitVec.add_sub_cancel]
    rw [hf]
    exact hs.add hd hlt hn rfl rfl rfl rfl

/-! ## The operations -/

theorem setWidth_eq (w : Word) : w.setWidth 8 = BitVec.ofNat 8 w.toNat := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_setWidth]

theorem swapW_eq (w : Word) : Op.swapW w = Op.swap w.toNat := by
  unfold Op.swapW Op.swap; rw [setWidth_eq]

theorem dupW_eq (w : Word) : Op.dupW w = Op.dup w.toNat := by
  unfold Op.dupW Op.dup; rw [setWidth_eq]

theorem dup_depth {s c : Word} (h : c.toNat < s.toNat) :
    (s - 1 - c + 1).toNat = s.toNat - c.toNat := by
  bv_omega

theorem swap_depth {s c : Word} (h : c.toNat < s.toNat) :
    (s - 1 - c).toNat = s.toNat - 1 - c.toNat := by
  bv_omega

theorem dup_eq (hs : Sim e fs st) {copy : Word} (hc : copy.toNat < st.len) :
    stackDup fs copy =
      { fs with data := put fs.data fs.size (st.val copy.toNat), size := fs.size + 1,
                trace := fs.trace ++ [.dup (st.len - copy.toNat)] } := by
  rw [stackDup, hs.data copy hc, dupW_eq, dup_depth (hs.size ▸ hc), hs.size]

theorem beq_false {a b : BitVec 8} (h : ¬a = b) : (a == b) = false := by simp [h]

theorem sim_dup (hs : Sim e fs st) {copy d : Word} (hd : d.toNat < e.n) (hlt : st.len < e.n)
    (hc : copy.toNat < st.len) :
    SimR e (dup fs copy d)
      (if (st.val copy.toNat).kind == FunctionReturnLabel then .error .assertion
       else Bbu.add st (st.val copy.toNat) d.toNat (.dup (st.len - copy.toNat))) := by
  unfold dup
  rw [hs.data copy hc]
  by_cases hk : (st.val copy.toNat).kind = FunctionReturnLabel
  · rw [ite_eq_left hk, ite_eq_left (by simp [hk] : ((st.val copy.toNat).kind == FunctionReturnLabel) = true)]
    exact rfl
  rw [ite_eq_right hk, beq_false hk, ite_eq_right (by decide : ¬(false = true)), add_eq]
  dsimp only
  have hp : get (stackDup fs copy).pos d ≠ NONE ↔ (positionOf st d.toNat).isSome :=
    hs.pos_ne_NONE hd
  by_cases h : (positionOf st d.toNat).isSome
  · rw [ite_eq_left h, ite_eq_left (hp.mpr h)]
    exact rfl
  · rw [ite_eq_right h, ite_eq_right (fun h' => h (hp.mp h'))]
    refine ⟨rfl, ?_⟩
    have hn : positionOf st d.toNat = none := Option.not_isSome_iff_eq_none.mp h
    rw [dup_eq hs hc]
    have hf : bind
        { fs with
          data := put fs.data fs.size (st.val copy.toNat), size := fs.size + 1,
          trace := fs.trace ++ [.dup (st.len - copy.toNat)] } (fs.size + 1 - 1) d =
        { fs with
          data := put fs.data fs.size (st.val copy.toNat), size := fs.size + 1,
          trace := fs.trace ++ [.dup (st.len - copy.toNat)], dest := put fs.dest fs.size d,
          pos := put fs.pos d fs.size } := by
      simp [bind, BitVec.add_sub_cancel]
    rw [hf]
    exact hs.add hd hlt hn rfl rfl rfl rfl

/-! ## `swapDestinations` -/

theorem swapDest_val {st : Bbu.St} {a b : Nat} (ha : a < st.len) (hb : b < st.len) (i : Nat) :
    (Bbu.swapDestinations st a b).val i = st.val i := by
  simp only [Bbu.swapDestinations, Bbu.St.val, List.getElem?_set]
  simp only [Bbu.St.len] at ha hb
  by_cases h1 : b = i
  · subst h1; by_cases h2 : a = b
    · subst h2; simp [ha]
    · simp [hb]
  · by_cases h2 : a = i
    · subst h2; simp [h1, ha]
    · simp [h1, h2]

theorem swapDest_dest {st : Bbu.St} {a b : Nat} (ha : a < st.len) (hb : b < st.len) (i : Nat) :
    (Bbu.swapDestinations st a b).dest i =
      if i = b then st.dest a else if i = a then st.dest b else st.dest i := by
  simp only [Bbu.swapDestinations, Bbu.St.dest, List.getElem?_set]
  simp only [Bbu.St.len] at ha hb
  by_cases h1 : b = i
  · subst h1; simp [hb]
  · by_cases h2 : a = i
    · subst h2; simp [h1, ha, Ne.symm h1]
    · simp [h1, h2, Ne.symm h1, Ne.symm h2]

theorem _root_.Bbu.Pos.dest_lt' {n : Nat} {st : Bbu.St} (hp : Pos n st) {i : Nat} (hi : i < st.len) :
    st.dest i < n := by
  rw [St.dest_eq, getElem!_pos st.dests i (by rw [St.length_dests]; exact hi)]
  exact hp.dests.1 i _

theorem lt_NONE {a : Word} (h : a.toNat < MAX_N) : a ≠ NONE := by
  apply ne_NONE; unfold MAX_N at h; omega

theorem Sim.swapDest (hs : Sim e fs st) {a b : Word} (ha : a.toNat < st.len)
    (hb : b.toNat < st.len) :
    Sim e (swapDestinations fs a b) (Bbu.swapDestinations st a.toNat b.toNat) := by
  have hle := hs.n_le
  have hsz := hs.size
  have hlen := hs.len_le
  have hA : a.toNat < MAX_N := by omega
  have hB : b.toNat < MAX_N := by omega
  have hl : (Bbu.swapDestinations st a.toNat b.toNat).len = st.len := swapDest_len _ _ _
  have hp' := hs.hpos.swapDest ha hb
  -- The new destination of each slot.
  have hd : ∀ i : Word, get (put (put fs.dest a (get fs.dest b)) b (get fs.dest a)) i =
      if i = b then get fs.dest a else if i = a then get fs.dest b else get fs.dest i := by
    intro i
    rw [get_put _ _ _ hB, get_put _ _ _ hA]
  have hD : ∀ i : Word, i.toNat < st.len →
      (get (put (put fs.dest a (get fs.dest b)) b (get fs.dest a)) i).toNat =
        (Bbu.swapDestinations st a.toNat b.toNat).dest i.toNat := by
    intro i hi
    rw [hd, swapDest_dest ha hb]
    by_cases h1 : i = b
    · subst h1; simp [hs.dest _ ha]
    · rw [ite_eq_right h1, ite_eq_right (toNat_ne_of_ne h1)]
      by_cases h2 : i = a
      · subst h2; simp [hs.dest _ hb]
      · rw [ite_eq_right h2, ite_eq_right (toNat_ne_of_ne h2), hs.dest _ hi]
  have hDl : ∀ i : Word, i.toNat < st.len →
      (get (put (put fs.dest a (get fs.dest b)) b (get fs.dest a)) i).toNat < fs.targetSize.toNat := by
    intro i hi
    rw [hD i hi]
    exact hp'.dest_lt' (by rw [hl]; exact hi)
  refine ⟨hs.env, hs.n_le, ?_, ?_, ?_, ?_, ?_, hs.pend, hs.trace, hp'⟩
  · rw [hl]; exact hs.size
  · rw [hl]; exact hs.len_le
  · intro i hi
    rw [hl] at hi
    rw [swapDest_val ha hb]
    exact hs.data i hi
  · intro i hi
    rw [hl] at hi
    exact hD i hi
  · intro d hdn
    have hdn' : d.toNat < fs.targetSize.toNat := hdn
    have hDa := hD a ha
    have hDb := hD b hb
    have hla := hDl a ha
    have hlb := hDl b hb
    have hPl := hs.hpos.length
    unfold swapDestinations
    dsimp only
    generalize put (put fs.dest a (get fs.dest b)) b (get fs.dest a) = D at hDa hDb hla hlb ⊢
    rw [ite_eq_left (lt_NONE (by omega)), ite_eq_left (lt_NONE (by omega)),
      get_put _ _ _ (by omega), get_put _ _ _ (by omega), positionOf,
      swapDest_positionOf (by rw [Bbu.St.len] at ha; exact ha) (by exact hb),
      join_set (by rw [List.length_set]; omega), join_set (by omega), ← positionOf]
    rw [← hDb, ← hDa]
    by_cases h1 : d = get D b
    · subst h1; simp [optW]
    · by_cases h2 : d = get D a
      · subst h2; simp [h1, optW, BitVec.toNat_inj]
      · simp [h1, h2, hs.pos d hdn', BitVec.toNat_inj]

theorem Sim.swapDest' (hs : Sim e fs st) {a b : Word} {k : Nat} (ha : a.toNat < st.len)
    (hb : b.toNat = k) (hk : k < st.len) :
    Sim e (swapDestinations fs a b) (Bbu.swapDestinations st a.toNat k) :=
  hb ▸ hs.swapDest ha (hb ▸ hk)

/-! ## `swapWith` -/

theorem swapVals_val {st st' : Bbu.St} {a b : Nat}
    (h : st'.slots = (st.slots.set a ⟨st.val b, st.dest a⟩).set b ⟨st.val a, st.dest b⟩)
    (ha : a < st.len) (hb : b < st.len) (i : Nat) :
    st'.val i = if i = b then st.val a else if i = a then st.val b else st.val i := by
  simp only [Bbu.St.val, h, List.getElem?_set]
  simp only [Bbu.St.len] at ha hb
  by_cases h1 : b = i
  · subst h1; simp [hb]
  · by_cases h2 : a = i
    · subst h2; simp [h1, ha, Ne.symm h1]
    · simp [h1, h2, Ne.symm h1, Ne.symm h2]

theorem swapVals_dest {st st' : Bbu.St} {a b : Nat}
    (h : st'.slots = (st.slots.set a ⟨st.val b, st.dest a⟩).set b ⟨st.val a, st.dest b⟩)
    (i : Nat) : st'.dest i = st.dest i := by
  have : st'.dests = st.dests := by rw [St.dests, h]; exact swapVals_dests st a b
  rw [St.dest_eq, St.dest_eq, this]

-- The value exchange of `stackSwap`: the slots at `pos` and the top exchange, the
-- destinations stay.
theorem Sim.swapVals (hs : Sim e fs st) {pos : Word} {st' : Bbu.St} (hp : pos.toNat < st.len)
    (h1 : st'.slots = (st.slots.set pos.toNat ⟨st.val (st.len - 1), st.dest pos.toNat⟩).set
      (st.len - 1) ⟨st.val pos.toNat, st.dest (st.len - 1)⟩)
    (h2 : st'.positionOf = st.positionOf)
    (h3 : st'.trace = st.trace ++ [.swap (st.len - 1 - pos.toNat)])
    (h4 : st'.pendingGenerations = st.pendingGenerations) :
    Sim e (stackSwap fs pos) st' := by
  have hsz := hs.size
  have hlen := hs.len_le
  have hle := hs.n_le
  have hl : st'.len = st.len := by simp [Bbu.St.len, h1]
  have hT : (fs.size - 1).toNat = st.len - 1 := by bv_omega
  have hds : st'.dests = st.dests := by rw [St.dests, h1]; exact swapVals_dests st _ _
  refine ⟨hs.env, hs.n_le, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hl]; exact hs.size
  · rw [hl]; exact hs.len_le
  · intro i hi
    rw [hl] at hi
    unfold stackSwap
    dsimp only
    rw [get_put _ _ _ (by omega), get_put _ _ _ (by omega), swapVals_val h1 hp (by omega)]
    have hT' : ∀ j : Word, j = fs.size - 1 ↔ j.toNat = st.len - 1 :=
      fun j => ⟨fun h => h ▸ hT, fun h => eq_of_toNat (h.trans hT.symm)⟩
    have hP : ∀ j : Word, j = pos ↔ j.toNat = pos.toNat := fun j => ⟨fun h => h ▸ rfl, eq_of_toNat⟩
    by_cases e1 : i.toNat = st.len - 1
    · rw [ite_eq_left ((hT' i).mpr e1), ite_eq_left e1, hs.data pos hp]
    · rw [ite_eq_right (fun h => e1 ((hT' i).mp h)), ite_eq_right e1]
      by_cases e2 : i.toNat = pos.toNat
      · rw [ite_eq_left ((hP i).mpr e2), ite_eq_left e2, hs.data _ (by omega), hT]
      · rw [ite_eq_right (fun h => e2 ((hP i).mp h)), ite_eq_right e2, hs.data i hi]
  · intro i hi
    rw [hl] at hi
    rw [swapVals_dest h1]
    exact hs.dest i hi
  · intro d hd
    rw [positionOf, h2, ← positionOf]
    exact hs.pos d hd
  · rw [h4]; exact hs.pend
  · rw [h3]
    unfold stackSwap
    dsimp only
    rw [hs.trace, swapW_eq, swap_depth (by omega), hsz]
  · exact hs.hpos.congr h2 hds

theorem isFinal_iff (hs : Sim e fs st) {pos : Word} (hp : pos.toNat < st.len) :
    isFinal fs pos = true ↔ st.dest pos.toNat = pos.toNat := by
  rw [isFinal, beq_iff_eq, ← hs.dest pos hp]
  exact ⟨congrArg BitVec.toNat, eq_of_toNat⟩

theorem sim_swapWith (hs : Sim e fs st) (pos : Word) :
    SimR e (swapWith fs pos) (Bbu.swapWith st pos.toNat) := by
  have hsz := hs.size
  have hlen := hs.len_le
  have hle := hs.n_le
  unfold swapWith Bbu.swapWith
  by_cases h1 : ¬pos < fs.size
  · rw [ite_eq_left h1, ite_eq_left (Or.inl (by bv_omega))]
    exact rfl
  have hp : pos.toNat < st.len := by bv_omega
  rw [ite_eq_right h1]
  by_cases h2 : isFinal fs pos = true
  · rw [ite_eq_left h2, ite_eq_left (Or.inr ((isFinal_iff hs hp).mp h2))]
    exact rfl
  rw [ite_eq_right h2,
    ite_eq_right (c := st.len ≤ pos.toNat ∨ st.dest pos.toNat = pos.toNat) (by
      intro h; rcases h with h | h
      · omega
      · exact h2 ((isFinal_iff hs hp).mpr h))]
  dsimp only
  have hd : (depthOf fs pos).toNat = st.len - 1 - pos.toNat := by unfold depthOf; bv_omega
  by_cases h3 : 1 ≤ depthOf fs pos ∧ depthOf fs pos ≤ maxSwapDepth
  · rw [ite_eq_right (c := ¬(1 ≤ depthOf fs pos ∧ depthOf fs pos ≤ maxSwapDepth)) (fun h => h h3),
      ite_eq_right (c := st.len - 1 - pos.toNat < 1 ∨ MAX_SWAP_DEPTH < st.len - 1 - pos.toNat) (by
        unfold maxSwapDepth at h3; unfold MAX_SWAP_DEPTH; bv_omega)]
    refine ⟨rfl, ?_⟩
    refine Sim.swapDest' ?_ ?_ ?_ ?_
    · exact Sim.swapVals hs hp rfl rfl rfl rfl
    · simp [Bbu.St.len]; simp only [Bbu.St.len] at hp; omega
    · show (fs.size - 1).toNat = _; simp only [Bbu.St.len] at hsz ⊢; bv_omega
    · simp [Bbu.St.len]; simp only [Bbu.St.len] at hp; omega
  · rw [ite_eq_left (c := ¬(1 ≤ depthOf fs pos ∧ depthOf fs pos ≤ maxSwapDepth)) h3,
      ite_eq_left (c := st.len - 1 - pos.toNat < 1 ∨ MAX_SWAP_DEPTH < st.len - 1 - pos.toNat) (by
        unfold maxSwapDepth at h3; unfold MAX_SWAP_DEPTH; bv_omega)]
    exact rfl

/-! ## `shallowestCopyPosition` -/

theorem copyBelow_eq (hs : Sim e fs st) (slot : StackSlot) :
    ∀ k, k ≤ st.len →
      copyBelow fs slot (BitVec.ofNat 64 k) =
        optW ((List.range k).reverse.find? (st.val · == slot)) := by
  have hl := hs.len_lt
  unfold MAX_N at hl
  intro k
  induction k with
  | zero => intro _; rw [copyBelow]; simp [optW]
  | succ k ih =>
    intro hk
    rw [copyBelow, dite_eq_right (by intro h; have := congrArg BitVec.toNat h; simp at this; omega)]
    have hk1 : BitVec.ofNat 64 (k + 1) - 1 = BitVec.ofNat 64 k := by
      apply eq_of_toNat; simp; omega
    rw [hk1, hs.data _ (by rw [toNat_ofNat_of_lt (by omega)]; omega), toNat_ofNat_of_lt (by omega),
      List.range_succ, List.reverse_append]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
      List.find?_cons]
    by_cases hv : st.val k = slot
    · simp [hv, optW]
    · rw [ite_eq_right hv, ih (by omega)]
      have hb : (st.val k == slot) = false := by simpa using hv
      rw [hb]

theorem sim_copy (hs : Sim e fs st) (slot : StackSlot) :
    shallowestCopyPosition fs slot = optW (Bbu.shallowestCopyPosition st slot) := by
  have h := copyBelow_eq hs slot st.len (Nat.le_refl _)
  have hsz : BitVec.ofNat 64 st.len = fs.size := by
    apply eq_of_toNat; rw [toNat_ofNat_of_lt (by have := hs.len_lt; unfold MAX_N at this; omega), hs.size]
  rw [hsz] at h
  exact h

end

end Bbu.Flat
