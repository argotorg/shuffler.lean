module

public import PlanBridge.Spill
import all PlanBridge.Spill
public import PlanBridge.Bounded
import all PlanBridge.Bounded
public import Shuffler.Resolve.Lemmas
import all Shuffler.Resolve.Lemmas

@[expose] public section

/-!
The flat `resolve` of `Planner::resolve` and PR31 `Planner.resolve`.
-/

namespace Bbu.Flat

-- A loop that returns true at the first offset from `o` on below `n` where `P` holds.
theorem anyFrom_iff {n : Word} (hn : n.toNat ≤ MAX_N) (P F : Word → Bool)
    (hF : ∀ o, F o = if o < n then (if P o then true else F (o + 1)) else false) :
    F 0 = true ↔ ∃ d < n.toNat, P (BitVec.ofNat 64 d) = true := by
  have h := allFrom_iff hn (fun o => !P o) (fun o => !F o) fun o => by
    rw [hF o]
    by_cases ho : o < n
    · rw [ite_eq_left ho, ite_eq_left ho]; cases P o <;> rfl
    · rw [ite_eq_right ho, ite_eq_right ho]; rfl
  constructor
  · intro h0
    by_contra hne
    have h1 := h.mpr fun d hd => by
      rw [Bool.not_eq_true']; exact Bool.eq_false_iff.mpr fun hp => hne ⟨d, hd, hp⟩
    rw [h0] at h1; cases h1
  · rintro ⟨d, hd, hp⟩
    by_contra h0
    have h1 := (h.mp (by rw [Bool.not_eq_true']; exact Bool.eq_false_iff.mpr h0)) d hd
    rw [hp] at h1; cases h1

end Bbu.Flat

namespace PlanBridge

open Shuffler Shuffler.Planner BbuBridge
open Bbu.Flat (get put optOf NONE isVariable spillIsSpilled spillAdd listEnv)

theorem hasOther_eq (source : Stack) {targetSize : ℕ}
    (mapping : Mapping source.length targetSize) (droppedNow : Vector Byte source.length)
    (offset : Fin source.length) :
    hasOtherRetainedCopy source mapping droppedNow offset =
      (List.finRange source.length).any fun o => decide (o ≠ offset ∧ source[o] = source[offset] ∧
        isRetained mapping o = true ∧ droppedNow[o] = 0) := by
  unfold hasOtherRetainedCopy
  generalize List.finRange source.length = l
  induction l with
  | nil => rfl
  | cons x xs ih =>
    rw [List.any_cons]
    by_cases h : x ≠ offset ∧ source[x] = source[offset] ∧ isRetained mapping x = true ∧
        droppedNow[x] = 0
    · rw [decide_eq_true h]; simp only [Fin.getElem_fin] at h; simp [h]
    · rw [decide_eq_false h, Bool.false_or, ← ih]; simp only [Fin.getElem_fin] at h; simp [h]

-- The PR31 dropped bytes `dn` are the flat bytes `fdn`.
def DnR {k : Nat} (dn : Vector Byte k) (fdn : Vector (BitVec 8) Bbu.MAX_N) : Prop :=
  ∀ i : Fin k, dn[i] = (get fdn (.ofNat 64 i.val)).toFin

theorem DnR.zero {k : Nat} {dn : Vector Byte k} {fdn : Vector (BitVec 8) Bbu.MAX_N}
    (h : DnR dn fdn) (i : Fin k) : dn[i] = 0 ↔ get fdn (.ofNat 64 i.val) = 0 := by
  rw [h i]
  constructor
  · intro h'; apply BitVec.eq_of_toFin_eq; exact h'
  · intro h'; rw [h']; rfl

theorem get_mem_take {α : Type} [Inhabited α] (v : Vector α Bbu.MAX_N) {m : Bbu.Word}
    (hm : m.toNat ≤ Bbu.MAX_N) {d : Nat} (hd : d < m.toNat) :
    get v (.ofNat 64 d) ∈ v.toList.take m.toNat := by
  rw [Bbu.Flat.get_ofNat v (by omega)]
  exact List.mem_iff_getElem.mpr ⟨d, by simp; omega, by simp⟩

theorem ofNat_inj {a b : Nat} (ha : a < Bbu.MAX_N) (hb : b < Bbu.MAX_N) :
    BitVec.ofNat 64 a = BitVec.ofNat 64 b ↔ a = b := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rwa [Bbu.Flat.toNat_ofNat_lt ha, Bbu.Flat.toNat_ofNat_lt hb] at this
  · rintro rfl; rfl

theorem isRetained_corr {M : Bbu.Flat.Mapping} {s t : Nat} {P : Mapping s t} (hR : MapR M P)
    (i : Fin s) : isRetained P i = Bbu.Flat.isRetained M (.ofNat 64 i.val) := by
  have h := hR.dest i
  unfold isRetained Bbu.Flat.isRetained Mapping.destinationOf
  cases hp : P i with
  | none =>
    rw [hp, Option.map_none, Bbu.Flat.optOf_eq_none] at h
    simp [h]
  | some d =>
    rw [hp, Option.map_some] at h
    have : get M.dest (.ofNat 64 i.val) ≠ NONE := fun h' => by
      rw [h', (Bbu.Flat.optOf_eq_none).mpr rfl] at h; cases h
    simp [this]


section
variable {pl : Bbu.Flat.Planner}

-- An offset of the source and its flat index.
theorem src_get (o : Fin (srcOf pl.source pl.m).length) :
    (srcOf pl.source pl.m)[o] = decode (get pl.source (.ofNat 64 o.val)) := by
  rw [Fin.getElem_fin, srcOf_get]

theorem src_lt (hm : pl.m.toNat ≤ Bbu.MAX_N) (o : Fin (srcOf pl.source pl.m).length) :
    o.val < pl.m.toNat := by
  have := o.isLt; have := srcOf_length (v := pl.source) hm; omega

theorem hasOther_corr (hm : pl.m.toNat ≤ Bbu.MAX_N)
    (canon : ∀ v ∈ pl.source.toList.take pl.m.toNat, Canon v) {t : Nat}
    {P : Mapping (srcOf pl.source pl.m).length t} {M : Bbu.Flat.Mapping} (hR : MapR M P)
    {dn : Vector Byte (srcOf pl.source pl.m).length} {fdn : Vector (BitVec 8) Bbu.MAX_N}
    (hdn : DnR dn fdn) (offset : Fin (srcOf pl.source pl.m).length) :
    hasOtherRetainedCopy (srcOf pl.source pl.m) P dn offset =
      Bbu.Flat.hasOtherRetainedCopy pl M fdn (.ofNat 64 offset.val) := by
  have hlen := srcOf_length (v := pl.source) hm
  have hoff := src_lt hm offset
  have key : ∀ o : Fin (srcOf pl.source pl.m).length,
      (o ≠ offset ∧ (srcOf pl.source pl.m)[o] = (srcOf pl.source pl.m)[offset] ∧
        isRetained P o = true ∧ dn[o] = 0) ↔
      ((BitVec.ofNat 64 o.val ≠ .ofNat 64 offset.val &&
        get pl.source (.ofNat 64 o.val) = get pl.source (.ofNat 64 offset.val) &&
        Bbu.Flat.isRetained M (.ofNat 64 o.val) && get fdn (.ofNat 64 o.val) = 0) = true) := by
    intro o
    have ho := src_lt hm o
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    rw [src_get, src_get, decode_eq_iff (canon _ (get_mem_take _ hm ho))
      (canon _ (get_mem_take _ hm hoff)), isRetained_corr hR, hdn.zero, ne_eq, ne_eq,
      ofNat_inj (by omega) (by omega), Fin.val_inj, and_assoc, and_assoc]
  apply Bool.eq_iff_iff.mpr
  rw [hasOther_eq, List.any_eq_true, Bbu.Flat.hasOtherRetainedCopy,
    Bbu.Flat.anyFrom_iff hm (fun o => o ≠ .ofNat 64 offset.val &&
      get pl.source o = get pl.source (.ofNat 64 offset.val) && Bbu.Flat.isRetained M o &&
      get fdn o = 0) _ fun o => by rw [Bbu.Flat.otherFrom]; simp only [dite_eq_ite]]
  constructor
  · rintro ⟨o, -, hc⟩
    exact ⟨o.val, src_lt hm o, (key o).mp (of_decide_eq_true hc)⟩
  · rintro ⟨d, hd, hc⟩
    let o : Fin (srcOf pl.source pl.m).length := ⟨d, by omega⟩
    exact ⟨o, List.mem_finRange _, decide_eq_true ((key o).mpr hc)⟩

theorem exists_take {α : Type} [Inhabited α] (v : Vector α Bbu.MAX_N) {m : Bbu.Word}
    (hm : m.toNat ≤ Bbu.MAX_N) (Q : α → Prop) :
    (∃ x ∈ v.toList.take m.toNat, Q x) ↔ ∃ d < m.toNat, Q (get v (.ofNat 64 d)) := by
  constructor
  · rintro ⟨x, hx, hq⟩
    obtain ⟨d, hd, rfl⟩ := List.mem_iff_getElem.mp hx
    simp only [List.length_take, Vector.length_toList] at hd
    refine ⟨d, by omega, ?_⟩
    rw [Bbu.Flat.get_ofNat v (by omega)]
    simpa using hq
  · rintro ⟨d, hd, hq⟩
    exact ⟨_, get_mem_take v hm hd, hq⟩

theorem isDemanded_corr (hn : pl.n.toNat ≤ Bbu.MAX_N)
    (canon : ∀ v ∈ pl.target.toList.take pl.n.toNat, Canon v) {x : Bbu.StackSlot}
    (hx : Canon x) :
    isDemanded (srcOf pl.target pl.n) (decode x) = Bbu.Flat.isDemanded pl x := by
  apply Bool.eq_iff_iff.mpr
  rw [isDemanded, List.any_eq_true, Bbu.Flat.isDemanded,
    Bbu.Flat.anyFrom_iff hn (fun j => !Bbu.isJunk (get pl.target j) && get pl.target j = x) _
      fun o => by rw [Bbu.Flat.demandedFrom]; simp only [dite_eq_ite]]
  have hmap : ∀ (l : List Bbu.StackSlot) (Q : Value → Prop),
      (∃ y ∈ l.map decode, Q y) ↔ ∃ v ∈ l, Q (decode v) := by intro l Q; simp
  simp only [srcOf, decide_eq_true_eq, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq]
  rw [hmap, exists_take _ hn (fun v => ¬(decode v).is_junk ∧ decode v = decode x)]
  constructor
  · rintro ⟨d, hd, hj, he⟩
    exact ⟨d, hd, by simpa [isJunk_iff] using hj,
      (decode_eq_iff (canon _ (get_mem_take _ hn hd)) hx).mp he⟩
  · rintro ⟨d, hd, hj, he⟩
    exact ⟨d, hd, by simpa [isJunk_iff] using hj,
      (decode_eq_iff (canon _ (get_mem_take _ hn hd)) hx).mpr he⟩

theorem isFRL_iff {x : Bbu.StackSlot} (hx : Canon x) :
    (decode x).isFunctionReturnLabel ↔ x.kind = Bbu.FunctionReturnLabel := by
  by_cases hk : x.kind = Bbu.FunctionReturnLabel
  · rw [hx.2 hk]; exact ⟨fun _ => rfl, fun _ => by decide⟩
  · refine ⟨fun h => ?_, fun h => absurd h hk⟩
    unfold decode at h
    split_ifs at h <;> exact h.elim

theorem isVariable_iff {x : Bbu.StackSlot} (hk : x.kind.toNat < 4) :
    (decode x).isVariable ↔ isVariable x = true := by
  constructor
  · intro h
    cases hd : decode x with
    | Var i => exact ((decode_var hk i).mp hd).1
    | _ => rw [hd] at h; exact h.elim
  · intro h
    rw [(decode_var hk _).mpr ⟨h, rfl⟩]
    trivial


-- The PR31 class of a flat class.
def clsOf (w : BitVec 8) : Option Nat := if w = Bbu.Flat.NOCLASS then none else some w.toNat

theorem classify_corr (hm : pl.m.toNat ≤ Bbu.MAX_N) (hn : pl.n.toNat ≤ Bbu.MAX_N)
    (ok : SlotsOk (pl.source.toList.take pl.m.toNat ++ pl.target.toList.take pl.n.toNat))
    {state : State (srcOf pl.source pl.m) (srcOf pl.target pl.n)} {sp : BitVec 32 → BitVec 8}
    (hsp : state.spills = pSpills (pl.source.toList.take pl.m.toNat) pl.n.toNat pl.target sp)
    (hal : state.spillingAllowed = pl.allowed)
    {P : Mapping (srcOf pl.source pl.m).length (srcOf pl.target pl.n).length}
    {M : Bbu.Flat.Mapping} (hR : MapR M P)
    {dn : Vector Byte (srcOf pl.source pl.m).length} {fdn : Vector (BitVec 8) Bbu.MAX_N}
    (hdn : DnR dn fdn) (offset : Fin (srcOf pl.source pl.m).length) (hsome : (P offset).isSome) :
    classify state P dn offset = .ok (clsOf (Bbu.Flat.classify pl sp M fdn (.ofNat 64 offset.val))) := by
  have ho := src_lt hm offset
  have hxS := get_mem_take pl.source hm ho
  have hxL := List.mem_append_left (pl.target.toList.take pl.n.toNat) hxS
  have hcx := ok.canon _ hxL
  have hkx := ok.kind _ hxL
  have hcS : ∀ v ∈ pl.source.toList.take pl.m.toNat, Canon v :=
    fun v hv => ok.canon v (List.mem_append_left _ hv)
  have hcT : ∀ v ∈ pl.target.toList.take pl.n.toNat, Canon v :=
    fun v hv => ok.canon v (List.mem_append_right _ hv)
  obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp hsome
  have hdest : get M.dest (.ofNat 64 offset.val) = .ofNat 64 d.val := by
    have := hR.dest offset
    rw [hd, Option.map_some] at this
    exact optOf_eq_some this
  have htd : (srcOf pl.target pl.n)[d] = decode (get pl.target (.ofNat 64 d.val)) := by
    rw [Fin.getElem_fin, srcOf_get]
  unfold classify
  dsimp only
  rw [requires_of_true _ (show (P.destinationOf offset).isSome = true from hsome), ok_bind]
  have htd' : ∀ h', (srcOf pl.target pl.n)[(P.destinationOf offset).get h'] =
      decode (get pl.target (.ofNat 64 d.val)) := fun h' => by
    have : (P.destinationOf offset).get h' = d := by simp [Mapping.destinationOf, hd]
    simp only [this, htd]
  simp only [htd', src_get, isFRL_iff hcx, isJunk_iff, ← isFree_iff, hsp, ← isSpilled_corr sp hxL,
    hasOther_corr hm hcS hR hdn, isDemanded_corr hn hcT hcx, hal, isVariable_iff hkx]
  unfold Bbu.Flat.classify
  dsimp only
  rw [hdest]
  generalize Bbu.isJunk (get pl.target (.ofNat 64 d.val)) = a
  generalize Bbu.Flat.hasOtherRetainedCopy pl M fdn (.ofNat 64 offset.val) = b
  generalize Bbu.Flat.isDemanded pl (get pl.source (.ofNat 64 offset.val)) = c
  generalize get pl.source (.ofNat 64 offset.val) = x
  generalize Bbu.isJunk x = e
  generalize Bbu.canBeFreelyGenerated x = f
  generalize spillIsSpilled sp x = g
  generalize isVariable x = i
  by_cases hk : x.kind = Bbu.FunctionReturnLabel
  · simp only [hk, ↓reduceIte]; rfl
  · simp only [hk, ↓reduceIte]
    cases a <;> cases b <;> cases c <;> cases e <;> cases f <;> cases g <;> cases i <;>
      cases pl.allowed <;> rfl

end

end PlanBridge
