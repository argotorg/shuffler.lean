module

public import FlatShuffler.FlatRel
import all FlatShuffler.FlatRel
public import FlatShuffler.ModelLemmas
import all FlatShuffler.ModelLemmas

@[expose] public section

/-!
The relation between a state of the flat model and a state of the list model (`Sim`), and
between their results (`SimR`). The bridge (`FlatBridge.lean`) shows that each unit of the
flat model keeps `Sim`.
-/

namespace FlatShuffler.Flat

/-! ## Words and arrays -/

theorem toNat_ofNat_of_lt {i : Nat} (h : i < 2 ^ 64) : (BitVec.ofNat 64 i).toNat = i :=
  Nat.mod_eq_of_lt h

theorem eq_of_toNat {a b : Word} (h : a.toNat = b.toNat) : a = b := BitVec.eq_of_toNat_eq h

theorem toNat_ne_of_ne {a b : Word} (h : a ≠ b) : a.toNat ≠ b.toNat :=
  fun h' => h (BitVec.eq_of_toNat_eq h')

theorem toNat_NONE : NONE.toNat = 2 ^ 64 - 1 := by decide

theorem ne_NONE {a : Word} (h : a.toNat < 2 ^ 64 - 1) : a ≠ NONE :=
  fun he => by subst he; rw [toNat_NONE] at h; omega

theorem get_put_self {α : Type} [Inhabited α] (v : Vector α MAX_N) {i : Word} (x : α)
    (hi : i.toNat < MAX_N) : get (put v i x) i = x := by
  simp [get, put, hi]

theorem get_put_ne {α : Type} [Inhabited α] (v : Vector α MAX_N) {i j : Word} (x : α)
    (h : j ≠ i) : get (put v i x) j = get v j := by
  have h' : i.toNat ≠ j.toNat := fun he => h (BitVec.eq_of_toNat_eq he.symm)
  unfold get put
  split
  · rename_i hj
    rw [Vector.getElem_setIfInBounds_ne hj h']
  · rfl

theorem get_put {α : Type} [Inhabited α] (v : Vector α MAX_N) {i : Word} (j : Word) (x : α)
    (hi : i.toNat < MAX_N) : get (put v i x) j = if j = i then x else get v j := by
  split
  · rename_i h; subst h; exact get_put_self v x hi
  · rename_i h; exact get_put_ne v x h

/-! ## The relation -/

-- The word of an `Optional<StackOffset>`.
def optW : Option Nat → Word
  | none => NONE
  | some p => BitVec.ofNat 64 p

-- The flat state `fs` holds the list state `st` in the environment `e`.
structure Sim (e : Env) (fs : St) (st : FlatShuffler.St) : Prop where
  env : e = listEnv fs.targetSize.toNat fs.target fs.spills
  n_le : fs.targetSize.toNat ≤ MAX_N
  size : fs.size.toNat = st.len
  len_le : st.len ≤ fs.targetSize.toNat
  data : ∀ i : Word, i.toNat < st.len → get fs.data i = st.val i.toNat
  dest : ∀ i : Word, i.toNat < st.len → (get fs.dest i).toNat = st.dest i.toNat
  pos : ∀ d : Word, d.toNat < fs.targetSize.toNat → get fs.pos d = optW (positionOf st d.toNat)
  pend : fs.pend.toNat = st.pendingGenerations
  trace : fs.trace = st.trace
  hpos : Pos fs.targetSize.toNat st

-- The flat state `fs` holds the list state `st` and the blocked slot `pos` with the excess
-- `excess`.
structure Blk (e : Env) (fs : St) (st : FlatShuffler.St) (pos excess : Nat) : Prop where
  sim : Sim e fs st
  blk0 : fs.blockedOffset.toNat = pos
  blk1 : fs.blockedExcess.toNat = excess

-- The flat result `r` holds the list result `m`.
def SimR (e : Env) (r : Status × St) : M FlatShuffler.St → Prop
  | .ok st => r.1 = .done ∧ Sim e r.2 st
  | .error (.blocked pos excess st) => r.1 = .blocked ∧ Blk e r.2 st pos excess
  | .error .assertion => r.1 = .assertionFailed

section
variable {e : Env} {fs : St} {st : FlatShuffler.St}

theorem Sim.n (hs : Sim e fs st) : e.n = fs.targetSize.toNat := by
  rw [hs.env]
  simp only [listEnv, Env.n, List.length_take, Vector.length_toList]
  have := hs.n_le
  omega

theorem Sim.len_lt (hs : Sim e fs st) : st.len ≤ MAX_N := Nat.le_trans hs.len_le hs.n_le

theorem Sim.dest_lt (hs : Sim e fs st) {i : Nat} (hi : i < st.len) : st.dest i < e.n := by
  rw [hs.n, St.dest_eq, getElem!_pos st.dests i (by rw [St.length_dests]; exact hi)]
  exact hs.hpos.dests.1 i _

theorem Sim.slots (hs : Sim e fs st) : slotsOf fs = st.slots.map Slot.val := by
  apply List.ext_getElem
  · simp [slotsOf, hs.size, St.len]
  · intro i h1 h2
    have hi : i < st.len := by simpa [slotsOf, hs.size] using h1
    have hl : i < 2 ^ 64 := by have := hs.len_lt; unfold MAX_N at this; omega
    simp only [slotsOf, List.getElem_map, List.getElem_range]
    rw [hs.data _ (by rw [toNat_ofNat_of_lt hl]; exact hi), toNat_ofNat_of_lt hl]
    simp [St.val, List.getElem?_eq_getElem (show i < st.slots.length from hi)]

theorem Sim.holds (hs : Sim e fs st) : Holds fs st fs.blockedOffset.toNat fs.blockedExcess.toNat :=
  ⟨hs.trace, hs.slots, by simp, by simp⟩

theorem Blk.holds {pos excess : Nat} (h : Blk e fs st pos excess) : Holds fs st pos excess :=
  ⟨h.sim.trace, h.sim.slots, by rw [← h.blk0]; simp, by rw [← h.blk1]; simp⟩

-- The target slot at an offset below `n`.
theorem Sim.target (hs : Sim e fs st) {t : Word} (ht : t.toNat < e.n) :
    e.target[t.toNat]! = get fs.target t := by
  have hn := hs.n
  have hle := hs.n_le
  rw [hs.env]
  rw [hs.env] at ht
  simp only [listEnv, Env.n, List.length_take, Vector.length_toList] at ht ⊢
  rw [getElem!_pos _ _ (by simp; omega)]
  simp [get, show t.toNat < MAX_N by omega]

theorem Sim.isSpilled (hs : Sim e fs st) (slot : StackSlot) :
    FlatShuffler.isSpilled e slot = isSpilled fs slot := by
  rw [hs.env]
  simp only [FlatShuffler.isSpilled, Flat.isSpilled, listEnv, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  congr 1

end

end FlatShuffler.Flat
