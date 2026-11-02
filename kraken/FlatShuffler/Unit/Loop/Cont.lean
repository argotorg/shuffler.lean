module

public import FlatShuffler.Unit.Loop.Model
import all FlatShuffler.Unit.Loop.Model

@[expose] public section

/-!
# `buildBottomUp`: the model between the labels

The asm of the loop has a label at each branch of `body`, `bound` and `placeTop`. For each label
there is one definition here: the part of `body` that the asm does from that label on. Each
definition has the text of that part, so the equations to `body`, `bound` and `placeTop` are `rfl`.
The loops of `urgentFrom` and `candidateFrom` have one lemma for each branch of one step.
-/

namespace FlatShuffler.Flat

/-! ## The loop -/

-- The result of the loop after an iteration that ends with `n`.
def kfin : Next → Status × St
  | .ret r => r
  | .cont st T => loop st (T + 1)

theorem loop_lt {st : St} {T : Word} (h : T < st.targetSize) : loop st T = kfin (body st T) := by
  rw [loop]
  simp only [h, ↓reduceIte]
  split <;> (rename_i e; rw [e]; rfl)

theorem loop_ge {st : St} {T : Word} (h : ¬T < st.targetSize) :
    loop st T = if st.size ≠ st.targetSize then (.assertionFailed, st) else (.done, st) := by
  rw [loop]
  simp only [h, ↓reduceIte]

/-! ## The parts of `body` -/

-- A slot is generated for `x`, then the loop does `targetOffset` again.
def kGenAt (st : St) (T x : Word) : Next :=
  let r := generate st x
  if r.1 ≠ .done then .ret r else .cont r.2 (T - 1)

-- The end of `placeTop`, for a `targetOffset` below the size that is not final.
def kTail (st : St) (T : Word) : Next :=
  if T ≠ st.size - 1 then
    if !isSwapReachable st T then .ret (blockSwapUnreachable st T)
    else
      let r := swapWith st T
      if r.1 ≠ .done then .ret r else .cont r.2 T
  else .cont st T

theorem placeTop_eq (st : St) (T : Word) :
    placeTop st T = if ¬T < st.size then .ret (.assertionFailed, st)
      else if isFinal st T then .ret (.assertionFailed, st) else kTail st T := rfl

-- The end of `bound`, after the swap of the destinations of `p` and of the source.
def kBoundSw (st : St) (T p : Word) : Next :=
  if p = T then .cont st T
  else if p ≠ st.size - 1 then
    if !isSwapReachable st p then .ret (blockSwapUnreachable st p)
    else
      let r := swapWith st p
      if r.1 ≠ .done then .ret r else placeTop r.2 T
  else placeTop st T

-- The end of `bound` for the source `b` and the position `p` of the slot to swap.
def kB (st : St) (T b p : Word) : Next :=
  if get st.data p ≠ get st.data b then .ret (.assertionFailed, st)
  else kBoundSw (swapDestinations st p b) T p

theorem bound_eq (st : St) (T : Word) :
    bound st T = if ¬(get st.pos T ≠ NONE ∧ get st.pos T ≥ T) then .ret (.assertionFailed, st)
      else kB st T (get st.pos T)
        (if get st.data T = get st.data (get st.pos T) then T
         else candidateFrom st (get st.data (get st.pos T)) (get st.pos T) (st.size - 1)) := rfl

-- A slot is generated for `targetOffset`, then it goes to `targetOffset`.
def kGenT (st : St) (T : Word) : Next :=
  let r := generate st T
  if r.1 ≠ .done then .ret r
  else
    let st := r.2
    if ¬T < st.size then .ret (.assertionFailed, st)
    else if isFinal st T then .cont st T
    else placeTop st T

-- After the two `generate` branches of `urgentToDup` and of the top.
def kU3 (st : St) (T : Word) : Next :=
  if get st.pos T ≠ NONE then bound st T else kGenT st T

-- After the `generate` branch of `urgentToDup`.
def kU2 (st : St) (T u : Word) : Next :=
  if u = NONE ∧ st.size > T ∧ st.size < st.targetSize ∧ get st.pos st.size = NONE ∧
      st.size - T < maxSwapDepth then kGenAt st T st.size
  else kU3 st T

-- After the loop of `urgentToDup`, with its value `u`.
def kU (st : St) (T u : Word) : Next :=
  if u ≠ NONE ∧ u ≠ T ∧ st.size - T < maxSwapDepth then kGenAt st T u else kU2 st T u

-- The result of the loop of `urgentToDup`.
def kUE (st : St) (T : Word) : Except (Status × St) Word → Next
  | .error r => .ret r
  | .ok u => kU st T u

-- After the check of `isFinal`.
def kPend (st : St) (T : Word) : Next :=
  if st.pend = 0 then
    if st.size ≠ st.targetSize then .ret (.assertionFailed, st) else .ret (permuteMapping st)
  else kUE st T (urgentFrom st T T NONE)

theorem body_eq (st : St) (T : Word) :
    body st T = if T < st.size ∧ isFinal st T then .cont st T else kPend st T := by
  unfold body kPend
  split
  · rfl
  · split
    · rfl
    · cases urgentFrom st T T NONE <;> rfl

/-! ## The steps of `urgentFrom` -/

section
variable {st : St} {T o u : Word}

theorem uf_ge (h : ¬o < st.targetSize) : urgentFrom st T o u = .ok u := by
  rw [urgentFrom]; simp only [h, ↓reduceDIte]

theorem uf_pos (h : o < st.targetSize) (hp : get st.pos o ≠ NONE) :
    urgentFrom st T o u = urgentFrom st T (o + 1) u := by
  rw [urgentFrom]; simp only [h, ↓reduceDIte, hp, ne_eq, not_false_eq_true, ↓reduceIte]

theorem uf_free (h : o < st.targetSize) (hp : get st.pos o = NONE)
    (hf : (isJunk (get st.target o) || canBeFreelyGenerated (get st.target o)
      || isSpilled st (get st.target o)) = true) :
    urgentFrom st T o u = urgentFrom st T (o + 1) u := by
  rw [urgentFrom]; simp only [h, ↓reduceDIte, hp, ne_eq, not_true_eq_false, ↓reduceIte, hf]

theorem uf_none (h : o < st.targetSize) (hp : get st.pos o = NONE)
    (hf : (isJunk (get st.target o) || canBeFreelyGenerated (get st.target o)
      || isSpilled st (get st.target o)) = false)
    (hc : shallowestCopyPosition st (get st.target o) = NONE) :
    urgentFrom st T o u = urgentFrom st T (o + 1) u := by
  rw [urgentFrom]
  simp only [h, ↓reduceDIte, hp, ne_eq, not_true_eq_false, ↓reduceIte, hf, Bool.false_eq_true, hc]

theorem uf_block (h : o < st.targetSize) (hp : get st.pos o = NONE)
    (hf : (isJunk (get st.target o) || canBeFreelyGenerated (get st.target o)
      || isSpilled st (get st.target o)) = false)
    (hc : shallowestCopyPosition st (get st.target o) ≠ NONE)
    (hr : isDupReachable st (shallowestCopyPosition st (get st.target o)) = false) :
    urgentFrom st T o u
      = .error (blockDupUnreachable st (shallowestCopyPosition st (get st.target o))) := by
  rw [urgentFrom]
  simp only [h, ↓reduceDIte, hp, ne_eq, not_true_eq_false, ↓reduceIte, hf, Bool.false_eq_true, hc,
    not_false_eq_true, hr, Bool.not_false]

theorem uf_next (h : o < st.targetSize) (hp : get st.pos o = NONE)
    (hf : (isJunk (get st.target o) || canBeFreelyGenerated (get st.target o)
      || isSpilled st (get st.target o)) = false)
    (hc : shallowestCopyPosition st (get st.target o) ≠ NONE)
    (hr : isDupReachable st (shallowestCopyPosition st (get st.target o)) = true) :
    urgentFrom st T o u = urgentFrom st T (o + 1)
      (if depthOf st (shallowestCopyPosition st (get st.target o)) = maxDupDepth
          ∧ shallowestCopyPosition st (get st.target o) ≠ T ∧ u = NONE then o else u) := by
  rw [urgentFrom]
  simp only [h, ↓reduceDIte, hp, ne_eq, not_true_eq_false, ↓reduceIte, hf, Bool.false_eq_true, hc,
    not_false_eq_true, hr, Bool.not_true]

end

/-! ## The steps of `candidateFrom` -/

section
variable {st : St} {slot : StackSlot} {b c : Word}

theorem cf_le (h : ¬c > b) : candidateFrom st slot b c = b := by
  rw [candidateFrom]; simp only [h, ↓reduceDIte]

theorem cf_hit (h : c > b) (hd : get st.data c = slot) (hf : isFinal st c = false) :
    candidateFrom st slot b c = c := by
  rw [candidateFrom]; simp [h, hd, hf]

theorem cf_next (h : c > b) (hn : ¬(get st.data c = slot ∧ !isFinal st c)) :
    candidateFrom st slot b c = candidateFrom st slot b (c - 1) := by
  rw [candidateFrom]; simp only [h, ↓reduceDIte, hn, ↓reduceIte]

end

end FlatShuffler.Flat
