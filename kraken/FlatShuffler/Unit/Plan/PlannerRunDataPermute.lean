module

public import FlatShuffler.Unit.Plan.PlannerRunDataPermuteInit
import all FlatShuffler.Unit.Plan.PlannerRunDataPermuteInit

@[expose] public section

namespace FlatShuffler.Flat

set_option maxRecDepth 4096

def restorePNext (cap : Nat) (old : Vector StackSlot maxStackSize) : PNext → PNext
  | .ret r => .ret (r.1, restoreData cap old r.2)
  | .cont st p => .cont (restoreData cap old st) p

theorem restoreData_exchange (cap : Nat) (old : Vector StackSlot maxStackSize) (st : St)
    (top : Word) (p : Vector Word maxStackSize) (pos : Word)
    (hp : pos.toNat < cap) (ht : (st.size - 1#64).toNat < cap) :
    exchange (restoreData cap old st) top p pos =
      restorePNext cap old (exchange st top p pos) := by
  simp only [exchange, BitVec.ofNat_eq_ofNat, restoreData_size, restoreData_get _ _ _ _ hp,
    restoreData_get _ _ _ _ ht]
  have hr : isSwapReachable (restoreData cap old st) pos = isSwapReachable st pos := by
    unfold isSwapReachable depthOf
    simp only [restoreData_size]
  rw [hr]
  by_cases he : get st.data pos = get st.data (st.size - 1#64)
  · simp only [he, ↓reduceIte]
    rw [restoreData_swapDestinations]
    rfl
  · simp only [he, ↓reduceIte]
    by_cases hu : (!isSwapReachable st pos) = true
    · simp only [hu, ↓reduceIte]
      rw [restoreData_blockSwapUnreachable]
      rfl
    · simp only [hu]
      rw [restoreData_stackSwap _ _ _ _ hp ht, restoreData_swapDestinations]
      rfl

theorem restoreData_permuteStep (cap : Nat) (old : Vector StackSlot maxStackSize) (st : St)
    (p : Vector Word maxStackSize) (h0 : 0 < st.size) (hs : st.size.toNat ≤ cap)
    (hb : Unit.Bij st.size p) :
    permuteStep (restoreData cap old st) (st.size - 1#64) p =
      restorePNext cap old (permuteStep st (st.size - 1#64) p) := by
  have ht : st.size - 1#64 < st.size := by bv_omega
  have htc : (st.size - 1#64).toNat < cap :=
    Nat.lt_of_lt_of_le (BitVec.lt_def.mp ht) hs
  simp only [permuteStep]
  split
  · split
    · rfl
    · rename_i hm
      have hp : (misplacedBelow p (st.size - 1#64) (st.size - 1#64)).toNat < cap := by
        rcases Unit.Permute.misplacedBelow_spec p (st.size - 1#64) (st.size - 1#64) with he | hh
        · exact absurd he hm
        · have := BitVec.lt_def.mp hh.1
          omega
      exact restoreData_exchange cap old st _ p _ hp htc
  · exact restoreData_exchange cap old st _ p _
      (Nat.lt_of_lt_of_le (BitVec.lt_def.mp (hb.1 _ ht)) hs) htc

private def nextState (r : PNext) : St :=
  match r with
  | .ret r => r.2
  | .cont st _ => st

private theorem exchange_fields (st : St) (top : Word) (p : Vector Word maxStackSize) (pos : Word) :
    (nextState (exchange st top p pos)).size = st.size ∧
      (nextState (exchange st top p pos)).targetSize = st.targetSize := by
  unfold exchange
  split
  · exact ⟨rfl, rfl⟩
  · split
    · simp only [blockSwapUnreachable, block]
      split <;> exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩

private theorem permuteStep_fields (st : St) (top : Word) (p : Vector Word maxStackSize) :
    (nextState (permuteStep st top p)).size = st.size ∧
      (nextState (permuteStep st top p)).targetSize = st.targetSize := by
  unfold permuteStep
  dsimp only
  split
  · split
    · exact ⟨rfl, rfl⟩
    · exact exchange_fields st top p _
  · exact exchange_fields st top p _

theorem permuteLoop_fields (fuel : Nat) (st : St) (top : Word) (p : Vector Word maxStackSize) :
    (permuteLoop fuel st top p).2.size = st.size ∧
      (permuteLoop fuel st top p).2.targetSize = st.targetSize := by
  induction fuel generalizing st p with
  | zero => exact ⟨rfl, rfl⟩
  | succ fuel ih =>
    rw [permuteLoop]
    have hf := permuteStep_fields st top p
    cases he : permuteStep st top p with
    | ret r => simpa only [he, nextState] using hf
    | cont st' p' =>
      rw [he] at hf
      dsimp only [nextState] at hf
      exact ⟨(ih st' p').1.trans hf.1, (ih st' p').2.trans hf.2⟩

theorem restoreData_permuteLoop (cap : Nat) (old : Vector StackSlot maxStackSize)
    (fuel : Nat) (st : St) (p : Vector Word maxStackSize)
    (hn : st.size.toNat ≤ maxStackSize) (h0 : 0 < st.size) (hs : st.size.toNat ≤ cap)
    (hb : Unit.Bij st.size p) :
    permuteLoop fuel (restoreData cap old st) (st.size - 1#64) p =
      let r := permuteLoop fuel st (st.size - 1#64) p
      (r.1, restoreData cap old r.2) := by
  induction fuel generalizing st p with
  | zero => rfl
  | succ fuel ih =>
    conv => rhs; rw [permuteLoop]
    rw [permuteLoop, restoreData_permuteStep cap old st p h0 hs hb]
    have hf := permuteStep_fields st (st.size - 1#64) p
    cases he : permuteStep st (st.size - 1#64) p with
    | ret r => rfl
    | cont st' p' =>
      rw [he] at hf
      dsimp only [nextState] at hf
      have heSize : st'.size = st.size := hf.1
      have hb' := (Unit.Permute.permuteStep_cont hn h0 hb he).1
      simpa only [restorePNext, heSize] using
        ih st' p' (by simpa only [heSize] using hn)
          (by simpa only [heSize] using h0) (by simpa only [heSize] using hs)
          (by simpa only [heSize] using hb')

theorem permute_fields (st : St) (p : Vector Word maxStackSize) :
    (permute st p).2.size = st.size ∧
      (permute st p).2.targetSize = st.targetSize := by
  unfold permute
  dsimp only
  split
  · exact ⟨rfl, rfl⟩
  · split
    · exact ⟨rfl, rfl⟩
    · exact permuteLoop_fields _ st _ _

theorem restoreData_permute (cap : Nat) (old : Vector StackSlot maxStackSize) (st : St)
    (p : Vector Word maxStackSize) (hn : st.size.toNat ≤ maxStackSize) (hs : st.size.toNat ≤ cap)
    (hb : Unit.Bij st.size p) :
    permute (restoreData cap old st) p =
      let r := permute st p
      (r.1, restoreData cap old r.2) := by
  simp only [permute, restoreData_size, restoreData_clearDesired]
  split
  · rfl
  · rename_i h0
    rw [restoreData_regroup cap old st _ _ _ hs]
    cases he : regroup st 0 p (clearDesired st 0 initial) with
    | none => rfl
    | some p' =>
      exact restoreData_permuteLoop cap old _ st p' hn (by bv_omega) hs
        (Unit.Permute.regroup_bij hn hb he)

theorem restoreData_permuteMapping (cap : Nat) (old : Vector StackSlot maxStackSize) (st : St)
    (hn : st.size.toNat ≤ maxStackSize) (hs : st.size.toNat ≤ cap) (hp : Unit.PermOk st) :
    permuteMapping (restoreData cap old st) =
      let r := permuteMapping st
      (r.1, restoreData cap old r.2) := by
  simp only [permuteMapping, restoreData_readDestinations]
  cases he : readDestinations st 0 initial with
  | none => rfl
  | some p =>
    exact restoreData_permute cap old st p hn hs (Unit.Permute.permOk_bij hn hp he)

theorem permuteAtLowestHeight_fields (planned : Vector Word maxStackSize) (l : Locals) (st : St) :
    (permuteAtLowestHeight planned l st).2.size = st.size ∧
      (permuteAtLowestHeight planned l st).2.targetSize = st.targetSize := by
  unfold permuteAtLowestHeight
  split
  · exact ⟨rfl, rfl⟩
  · split
    · exact ⟨rfl, rfl⟩
    · exact permute_fields st _

theorem restoreData_permuteAtLowestHeight (cap : Nat) (old : Vector StackSlot maxStackSize)
    (planned : Vector Word maxStackSize) (l : Locals) (st : St)
    (hn : st.size.toNat ≤ maxStackSize) (hs : st.size.toNat ≤ cap) (hl : LowOk planned st) :
    permuteAtLowestHeight planned l (restoreData cap old st) =
      let r := permuteAtLowestHeight planned l st
      (r.1, restoreData cap old r.2) := by
  simp only [permuteAtLowestHeight, restoreData_scan]
  cases he : scan planned st 0 (Scan.init l) with
  | none => rfl
  | some sc =>
    dsimp only
    by_cases hc : sc.parkedCount = sc.holeCount
    · simp only [hc, ne_eq, not_true_eq_false, ↓reduceIte]
      exact restoreData_permute cap old st _ hn hs (hl l sc he hc)
    · simp only [hc, ne_eq, not_false_eq_true, ↓reduceIte]

end FlatShuffler.Flat
