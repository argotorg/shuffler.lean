import BbuKraken.Unit.Permute.MD
import BbuKraken.Unit.PermuteModelTest

/-!
Tests of the model steps of the `permute` proof (`Permute/ML.lean`, `Permute/MD.lean`) and of the
definitions `AgB`, `LtB`, `Mis` and `V` of `Permute/Inv.lean`.

For each lemma:
* an `example` that applies the lemma to concrete inputs. `decide +kernel` closes the hypotheses,
  so the hypotheses can be satisfied;
* `#guard` checks of the two sides (or of the conclusion) on the same inputs;
* a negative case: an input where a hypothesis is false and the conclusion is false too, when such
  an input exists.

The last section runs the steps of the loop of `permute` on all inputs of `check`
(`PermuteModelTest.lean`) and compares each step with `step_ne` / `step_eq`, `loop_succ` and the
`exchange` lemmas, and checks `Mis` and the conclusion of `Mis.step` at each exchange.

The states for the kernel are structure literals with `Flat.put` vectors (`ks`). The kernel needs
more than 40 s for a state of `mk` (the vectors of `mk` are `Vector.ofFn`); it needs less than 1 s
for a state of `ks`. A `#guard` shows that `ks` gives the same members as `mk`.
-/

namespace Bbu.Unit.Permute.MLTest

open Bbu Bbu.Sep Bbu.Flat.Test Bbu.Unit.Permute.Test

/-! ## Decision procedures for the definitions

`AgB`, `LtB` and `Bij` have quantifiers over `Word`. The instance of core for a quantifier over
`BitVec 64` tries all `2 ^ 64` values. `ballW_iff` and `ballN_iff` change them into quantifiers over
`Nat` below a bound. -/

theorem ballW_iff {k : Word} {P : Word → Prop} :
    (∀ i : Word, i < k → P i) ↔ ∀ i < k.toNat, P (BitVec.ofNat 64 i) := by
  constructor
  · intro h i hi
    apply h
    have e : (BitVec.ofNat 64 i).toNat = i := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := k.isLt; omega)
    rw [BitVec.lt_def, e]; exact hi
  · intro h i hi
    have := h i.toNat (BitVec.lt_def.mp hi)
    rwa [ofNat_toNat] at this

theorem ballN_iff {k : Nat} {P : Word → Prop} :
    (∀ i : Word, i.toNat < k → P i) ↔ ∀ i < k, P (BitVec.ofNat 64 i) := by
  constructor
  · intro h i hi
    apply h
    rw [BitVec.toNat_ofNat]; exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) hi
  · intro h i hi
    have := h i.toNat hi
    rwa [ofNat_toNat] at this

instance (k : Word) (v w : Vector Word MAX_N) : Decidable (AgB k v w) :=
  decidable_of_iff _ (ballW_iff (P := fun i => Flat.get v i = Flat.get w i)).symm

instance (n : Word) (p : Vector Word MAX_N) : Decidable (LtB n p) :=
  decidable_of_iff _ (ballW_iff (P := fun i => Flat.get p i < n)).symm

theorem bij_iff {n : Word} {p : Vector Word MAX_N} :
    Bij n p ↔ (∀ i < n.toNat, Flat.get p (BitVec.ofNat 64 i) < n)
      ∧ ∀ i < n.toNat, ∀ k < n.toNat,
        Flat.get p (BitVec.ofNat 64 i) = Flat.get p (BitVec.ofNat 64 k)
          → BitVec.ofNat 64 i = (BitVec.ofNat 64 k : Word) := by
  unfold Bij
  refine and_congr ballW_iff ?_
  rw [ballW_iff]
  exact forall_congr' fun i => forall_congr' fun _ => ballW_iff

instance (n : Word) (p : Vector Word MAX_N) : Decidable (Bij n p) :=
  decidable_of_iff _ bij_iff.symm

instance (n pos : Word) (p : Vector Word MAX_N) : Decidable (Mis n pos p) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

instance (fs : Flat.St) : Decidable (PermOk fs) :=
  decidable_of_iff
    ((∀ i < fs.size.toNat, (Flat.get fs.dest (BitVec.ofNat 64 i)).toNat < fs.size.toNat)
      ∧ ∀ i < fs.size.toNat, ∀ j < fs.size.toNat,
        Flat.get fs.dest (BitVec.ofNat 64 i) = Flat.get fs.dest (BitVec.ofNat 64 j) → i = j)
    ⟨fun ⟨a, b⟩ => ⟨a, b⟩, fun ⟨a, b⟩ => ⟨a, b⟩⟩

-- The decision procedures on small inputs: positive and negative cases.
#guard AgB 2 (pv [1, 0, 5]) (pv [1, 0, 7])
#guard ¬AgB 3 (pv [1, 0, 5]) (pv [1, 0, 7])
#guard AgB 0 (pv [1]) (pv [2])
#guard LtB 3 (pv [2, 0, 1, 9])
#guard ¬LtB 3 (pv [2, 3, 1])
#guard LtB 0 (pv [5])
#guard Bij 3 (pv [2, 0, 1])
#guard ¬Bij 3 (pv [2, 0, 0])
#guard ¬Bij 3 (pv [2, 0, 3])
#guard Mis 3 0 (pv [1, 2, 0])
#guard Mis 3 0 (pv [1, 0, 2])
#guard ¬Mis 3 1 (pv [0, 1, 2])
#guard ¬Mis 3 2 (pv [1, 2, 0])
#guard ¬Mis 3 3 (pv [1, 2, 3])
#guard PermOk (mk [x, y] [x, y] [1, 0])
#guard ¬PermOk (mk [x, y] [x, y] [0, 0])
#guard ¬PermOk (mk [x, y] [x, y] [0, 2])
-- `bijB` of `PermuteModelTest.lean` agrees with `Bij` on all permutations of 3 offsets and on
-- vectors that are not bijections.
#guard ((perms [0, 1, 2]) ++ [[0, 0, 1], [2, 2, 2], [0, 1, 3]]).all fun l =>
  bijB 3 (pv l) == decide (Bij 3 (pv l))

/-! ## Inputs for the kernel -/

-- A vector of words that holds `l` from offset 0 and `0` above it.
def kw (l : List Nat) : Vector Word MAX_N :=
  l.zipIdx.foldl (fun v (a, i) => Flat.put v (.ofNat 64 i) (.ofNat 64 a)) Flat.initial

-- A vector of slots that holds `l` from offset 0 and `default` above it.
def kv (l : List StackSlot) : Vector StackSlot MAX_N :=
  l.zipIdx.foldl (fun v (a, i) => Flat.put v (.ofNat 64 i) a) (Vector.replicate MAX_N default)

-- A state with the stack `s` (also the target), the destinations `d` and the positions `p`.
def ks (s : List StackSlot) (d p : List Nat) : Flat.St :=
  { target := kv s, targetSize := .ofNat 64 s.length, spills := fun _ => 0, data := kv s,
    size := .ofNat 64 s.length, trace := [], dest := kw d, pos := kw p, pend := 0,
    blockedOffset := 0, blockedExcess := 0 }

-- The members of a state except `spills` (a function, with no `DecidableEq`).
structure Full where
  target : Vector StackSlot MAX_N
  targetSize : Word
  data : Vector StackSlot MAX_N
  size : Word
  trace : List Op
  dest : Vector Word MAX_N
  pos : Vector Word MAX_N
  pend : Word
  blockedOffset : Word
  blockedExcess : Word
  deriving DecidableEq

def full (st : Flat.St) : Full :=
  ⟨st.target, st.targetSize, st.data, st.size, st.trace, st.dest, st.pos, st.pend,
    st.blockedOffset, st.blockedExcess⟩

def fr (r : Flat.Status × Flat.St) : Flat.Status × Full := (r.1, full r.2)

def nextV : Flat.PNext → Option Flat.Status × Full × Option (Vector Word MAX_N)
  | .ret r => (some r.1, full r.2, none)
  | .cont st p => (none, full st, some p)

-- `kw` and `pv` give the same vector.
#guard kw [2, 0, 1] = pv [2, 0, 1]
#guard kw [] = Flat.initial

-- The slots `x y x`, the destinations `2 0 1` and their positions.
def k3 : Flat.St := ks [x, y, x] [2, 0, 1] [1, 2, 0]
-- `ks` gives the members of `mk` that the model reads and writes.
#guard view k3 = view (mk [x, y, x] [x, y, x] [2, 0, 1])
#guard k3.data = (mk [x, y, x] [x, y, x] [2, 0, 1]).data

-- `k` different slots, each in place.
def kd (k : Nat) : Flat.St :=
  ks ((List.range k).map var) (List.range k) (List.range k)
#guard view (kd 18) = view (mk ((List.range 18).map var) ((List.range 18).map var) (List.range 18))

-- A ghost with the size and the destinations of `d`.
def gh (d : List Nat) : G where
  h := { tgt := 0, n := .ofNat 64 d.length, spl := 0, data := 0, len := .ofNat 64 d.length,
         ops := 0, nops := 0, dest := kw d, pos := Flat.initial, pend := 0, blkOff := 0,
         blkExc := 0 }
  stk := Vector.replicate _ 0
  ops := Vector.replicate _ ⟨⟨0, 0, default⟩, 0, 0⟩
  tgt := Vector.replicate _ 0
  spl := fun _ => 0

/-! ## `ML.lean`: the destinations -/

def gP : G := gh [1, 0]
def gBad : G := gh [0, 5]
def gNone : G := gh [Flat.NONE.toNat, 0]

theorem permOk_gP : PermOk (flat gP) := by decide +kernel

example := dest_lt (g := gP) (x := 1) permOk_gP (by decide +kernel)
#guard Flat.get gP.h.dest 1 < gP.h.len
#guard Flat.get gP.h.dest 0 < gP.h.len
-- Negative: not `PermOk`, and the destination of `1` is not below the size.
#guard ¬PermOk (flat gBad)
#guard ¬Flat.get gBad.h.dest 1 < gBad.h.len

example := dest_ne_none (g := gP) (x := 0) permOk_gP (by decide +kernel)
#guard Flat.get gP.h.dest 0 ≠ Flat.NONE
-- Negative: not `PermOk`, and the destination of `0` is `NONE`.
#guard ¬PermOk (flat gNone)
#guard Flat.get gNone.h.dest 0 = Flat.NONE

/-! ## `ML.lean`: the agreement of vectors -/

-- `agB_step`: `P[1] = d[1]` extends the agreement below `1` to `2`.
example := agB_step (P := kw [1, 9]) (d := kw [1, 0]) (x := 1) (by decide +kernel) (by decide)
#guard AgB 1 (kw [1, 9]) (kw [1, 0])
#guard AgB (1 + 1#64) ((kw [1, 9]).set 1 (Flat.get (kw [1, 0]) 1) (by decide)) (kw [1, 0])
#guard ¬AgB 2 (kw [1, 9]) (kw [1, 0])
-- Edge: `x = 0` and `x = MAX_N - 1`.
example := agB_step (P := kw [9]) (d := kw [1]) (x := 0) (by decide +kernel) (by decide)
#guard AgB 1023 Flat.initial (kw [0, 0]) ∧
  AgB 1024 (Flat.initial.set 1023 (Flat.get (kw [0, 0]) 1023) (by decide)) (kw [0, 0])
-- Negative: no agreement at `0`, and none after the step.
#guard ¬AgB 1 (kw [7, 9]) (kw [1, 0])
#guard ¬AgB (1 + 1#64) ((kw [7, 9]).set 1 (Flat.get (kw [1, 0]) 1) (by decide)) (kw [1, 0])

example := AgB.trans (k := 2) (u := kw [1, 0, 5]) (v := kw [1, 0, 6]) (w := kw [1, 0, 7])
  (by decide +kernel) (by decide +kernel)
#guard AgB 2 (kw [1, 0, 5]) (kw [1, 0, 7])
-- Negative: `v` and `w` do not agree, and `u` and `w` do not agree.
#guard ¬AgB 2 (kw [1, 0]) (kw [1, 1]) ∧ ¬AgB 2 (kw [1, 0]) (kw [1, 1])

example := AgB.symm (k := 2) (u := kw [1, 0, 5]) (v := kw [1, 0, 6]) (by decide +kernel)
#guard AgB 2 (kw [1, 0, 6]) (kw [1, 0, 5])
-- Negative: no agreement in each direction.
#guard ¬AgB 2 (kw [1, 0]) (kw [0, 1]) ∧ ¬AgB 2 (kw [0, 1]) (kw [1, 0])

/-! ## `ML.lean`: `readDestinations` and `NONE` -/

def kNone : Flat.St := ks [x, y] [1, Flat.NONE.toNat] [0, 0]

example := rd_some k3 (ballW_iff.mpr (by decide +kernel)) 0 Flat.initial
#guard (Flat.readDestinations k3 0 Flat.initial) = some (kw [2, 0, 1])
-- Negative: the destination of `1` is `NONE`, and `readDestinations` gives none.
#guard ¬∀ i < kNone.size.toNat, Flat.get kNone.dest (.ofNat 64 i) ≠ Flat.NONE
#guard (Flat.readDestinations kNone 0 Flat.initial).isNone

example : Flat.NONE.toInt = -1 := none_toInt
#guard Flat.NONE.toInt = -1
#guard Flat.NONE.toNat = 2 ^ 64 - 1

-- The vector with `NONE` at `0`.
def dN : Vector Word MAX_N := kw [Flat.NONE.toNat]

example := none_step (D := dN) (k := 1) (by decide) (ballN_iff.mpr (by decide +kernel))
#guard ∀ i < (1 : Nat), Flat.get dN (.ofNat 64 i) = Flat.NONE
#guard ∀ i < (2 : Nat), Flat.get (dN.set 1 Flat.NONE (by decide)) (.ofNat 64 i) = Flat.NONE
#guard ¬∀ i < (3 : Nat), Flat.get (dN.set 1 Flat.NONE (by decide)) (.ofNat 64 i) = Flat.NONE
-- Edge: `k = 0` and `k = MAX_N - 1`.
example := none_step (D := Flat.initial) (k := 0) (by decide) (ballN_iff.mpr (by decide +kernel))
#guard ∀ i < (1024 : Nat),
  Flat.get ((Vector.replicate MAX_N Flat.NONE).set 1023 Flat.NONE (by decide)) (.ofNat 64 i)
    = Flat.NONE
-- Negative: `D[0]` is not `NONE`, and it stays so after the step.
#guard ¬∀ i < (1 : Nat), Flat.get (kw [0]) (.ofNat 64 i) = Flat.NONE
#guard ¬∀ i < (2 : Nat),
  Flat.get ((kw [0]).set 1 Flat.NONE (by decide)) (.ofNat 64 i) = Flat.NONE

/-! ## `ML.lean`: a store into a local array -/

example := agB_set (n := 2) (u := kw [1, 0]) (w := kw [1, 0, 3]) (by decide +kernel) (k := 1)
  (by decide) 5
#guard AgB 2 ((kw [1, 0]).set 1 5 (by decide)) (Flat.put (kw [1, 0, 3]) 1 5)
-- Edge: a store at `k ≥ n` and at `MAX_N - 1`.
#guard AgB 2 ((kw [1, 0]).set 3 5 (by decide)) (Flat.put (kw [1, 0]) 3 5)
#guard AgB 1024 (Flat.initial.set 1023 5 (by decide)) (Flat.put Flat.initial 1023 5)
-- Negative: no agreement at `0`, and none after a store at `1`.
#guard ¬AgB 2 (kw [7, 0]) (kw [1, 0])
#guard ¬AgB 2 ((kw [7, 0]).set 1 5 (by decide)) (Flat.put (kw [1, 0]) 1 5)

example := ltB_put (n := 2) (p := kw [1, 0]) (by decide +kernel) 0 (x := 1) (by decide)
#guard LtB 2 (Flat.put (kw [1, 0]) 0 1)
-- Edge: `k ≥ MAX_N` (no store) and `k = MAX_N - 1`.
example := ltB_put (n := 2) (p := kw [1, 0]) (by decide +kernel) 2000 (x := 1) (by decide)
#guard Flat.put (kw [1, 0]) 2000 1 = kw [1, 0]
#guard LtB 1024 (Flat.put Flat.initial 1023 1023)
-- Negative: `x = n`, and the stored entry is not below `n`.
#guard ¬LtB 2 (Flat.put (kw [1, 0]) 0 2)
-- Negative: `p[0]` is not below `n`, and it stays so after a store at `1`.
#guard ¬LtB 2 (kw [5, 0]) ∧ ¬LtB 2 (Flat.put (kw [5, 0]) 1 1)

/-! ## `ML.lean`: the steps of `regroup`

`k3` has the slots `x y x` and the destinations `2 0 1`. The leader of `x` is `2`, of `y` is `1`.
`regroup` gives `1 0 2`: `0` gets the vacant offset `1`, and `2` keeps `2`. -/

def pR : Vector Word MAX_N := kw [2, 0, 1]
def dBc : Vector Word MAX_N := Flat.clearDesired k3 0 Flat.initial
theorem h2 : (2 : Word) < k3.size := by decide
-- `desiredBy` after `markDesired` for the leader `2`: offsets `2` and `1` are desired by `2`.
def dBm : Vector Word MAX_N := Flat.markDesired k3 2 h2 x pR 0 dBc

#guard dBc = kw (List.replicate 3 Flat.NONE.toNat)
#guard dBm = kw [Flat.NONE.toNat, 2, 2]
#guard Flat.regroup k3 0 pR dBc = some (kw [1, 0, 2])
#guard Flat.shallowestCopyPosition k3 x = 2
#guard Flat.shallowestCopyPosition k3 y = 1

example := regroup_ge (st := k3) (l := 3) (by decide +kernel) pR dBc
#guard Flat.regroup k3 3 pR dBc = some pR
-- Edge: `l = 2 ^ 64 - 1`.
#guard Flat.regroup k3 (-1) pR dBc = some pR
-- Negative: `l = 0 < size`, and `regroup` changes `p`.
#guard Flat.regroup k3 0 pR dBc ≠ some pR

example := regroup_skip (st := k3) (l := 0) (by decide +kernel) (by decide +kernel) pR dBc
#guard Flat.regroup k3 0 pR dBc = Flat.regroup k3 1 pR dBc
-- Negative: `2` is a leader, and `regroup` from `2` differs from `regroup` from `3`.
#guard Flat.shallowestCopyPosition k3 (Flat.get k3.data 2) = 2
#guard Flat.regroup k3 2 pR dBc ≠ Flat.regroup k3 3 pR dBc

example := regroup_lead (st := k3) (l := 2) h2 (by decide +kernel) pR dBc
#guard Flat.regroup k3 2 pR dBc
  = pg k3 2 h2 (Flat.get k3.data 2) (Flat.markDesired k3 2 h2 (Flat.get k3.data 2) pR 0 dBc) 0 0 pR
-- Negative: `0` is not a leader, and the group of `0` alone has no vacant offset.
#guard Flat.shallowestCopyPosition k3 (Flat.get k3.data 0) ≠ 0
#guard Flat.regroup k3 0 pR dBc
  ≠ pg k3 0 (by decide) (Flat.get k3.data 0)
      (Flat.markDesired k3 0 (by decide) (Flat.get k3.data 0) pR 0 dBc) 0 0 pR

/-! ## `ML.lean`: the steps of `markDesired` -/

example := md_eq (st := k3) (l := 2) (hl := h2) (σ := x) (p := pR) (dB := dBc) (j := 0)
  (by decide) (by decide +kernel)
#guard Flat.markDesired k3 2 h2 x pR 0 dBc
  = Flat.markDesired k3 2 h2 x pR 1 (Flat.put dBc (Flat.get pR 0) 2)
-- Negative: the slot at `1` is `y`, and a mark at `1` changes the result.
#guard Flat.get k3.data 1 ≠ x
#guard Flat.markDesired k3 2 h2 x pR 1 dBc
  ≠ Flat.markDesired k3 2 h2 x pR 2 (Flat.put dBc (Flat.get pR 1) 2)

example := md_ne (st := k3) (l := 2) (hl := h2) (σ := x) (p := pR) (dB := dBc) (j := 1)
  (by decide) (by decide +kernel)
#guard Flat.markDesired k3 2 h2 x pR 1 dBc = Flat.markDesired k3 2 h2 x pR 2 dBc
-- Negative: the slot at `0` is `x`, and a skip of `0` changes the result.
#guard Flat.markDesired k3 2 h2 x pR 0 dBc ≠ Flat.markDesired k3 2 h2 x pR 1 dBc

example := md_end (st := k3) (l := 2) (hl := h2) (σ := x) (p := pR) (dB := dBc) (j := 3)
  (by decide)
#guard Flat.markDesired k3 2 h2 x pR 3 dBc = dBc
-- Edge: `j = 2 ^ 64 - 1`.
#guard Flat.markDesired k3 2 h2 x pR (-1) dBc = dBc
-- Negative: `j = 2 ≤ l`, and the result has a mark.
#guard Flat.markDesired k3 2 h2 x pR 2 dBc ≠ dBc

/-! ## `ML.lean`: the steps of `placeGroup` and of the `vacant` loop -/

example := pg_end (st := k3) (l := 2) (hl := h2) (σ := x) (dB := dBm) (pos := 3) (vac := 0)
  (pc := pR) (by decide)
#guard pg k3 2 h2 x dBm 3 0 pR = Flat.regroup k3 3 pR dBm
-- Negative: `pos = 0 ≤ l`, and the group changes `pc`.
#guard pg k3 2 h2 x dBm 0 0 pR ≠ Flat.regroup k3 3 pR dBm

example := pg_skip (st := k3) (l := 2) (hl := h2) (σ := x) (dB := dBm) (pos := 1) (vac := 0)
  (pc := pR) (by decide) (by decide +kernel)
#guard pg k3 2 h2 x dBm 1 0 pR = pg k3 2 h2 x dBm 2 0 pR
-- Negative: the slot at `0` is `x`, and a skip of `0` changes the result.
#guard pg k3 2 h2 x dBm 0 0 pR ≠ pg k3 2 h2 x dBm 1 0 pR

example := pg_self (st := k3) (l := 2) (hl := h2) (σ := x) (dB := dBm) (pos := 2) (vac := 0)
  (pc := pR) (by decide) (by decide +kernel) (by decide +kernel)
#guard pg k3 2 h2 x dBm 2 0 pR = pg k3 2 h2 x dBm 3 0 (Flat.put pR 2 2)
-- Negative: `dB[0] ≠ 2`, and `0` does not keep its offset.
#guard Flat.get dBm 0 ≠ 2
#guard pg k3 2 h2 x dBm 0 0 pR ≠ pg k3 2 h2 x dBm 1 0 (Flat.put pR 0 0)

example := pg_nv (st := k3) (l := 2) (hl := h2) (σ := x) (dB := dBm) (pos := 0) (vac := 0)
  (pc := pR) (by decide) (by decide +kernel) (by decide +kernel)
#guard pg k3 2 h2 x dBm 0 0 pR = nv k3 2 h2 x dBm 0 0 pR
-- Negative: `dB[2] = 2`, and the `vacant` loop gives `2` another offset.
#guard pg k3 2 h2 x dBm 2 0 pR ≠ nv k3 2 h2 x dBm 2 0 pR

example := nv_next (st := k3) (l := 2) (hl := h2) (σ := x) (dB := dBm) (pos := 0) (x := 0)
  (pc := pR) (by decide) (by decide +kernel)
#guard nv k3 2 h2 x dBm 0 0 pR = nv k3 2 h2 x dBm 0 1 pR
-- `2` holds `x`: not vacant.
example := nv_next (st := k3) (l := 2) (hl := h2) (σ := x) (dB := dBm) (pos := 0) (x := 2)
  (pc := pR) (by decide) (by decide +kernel)
#guard nv k3 2 h2 x dBm 0 2 pR = nv k3 2 h2 x dBm 0 3 pR
-- Negative: `1` is vacant, and the loop does not go on from `2`.
#guard nv k3 2 h2 x dBm 0 1 pR ≠ nv k3 2 h2 x dBm 0 2 pR

example := nv_found (st := k3) (l := 2) (hl := h2) (σ := x) (dB := dBm) (pos := 0) (x := 1)
  (pc := pR) (by decide) (by decide +kernel) (by decide +kernel)
#guard nv k3 2 h2 x dBm 0 1 pR = pg k3 2 h2 x dBm 1 2 (Flat.put pR 0 1)
-- Negative: `dB[0] ≠ 2`, and `0` is not the vacant offset.
#guard nv k3 2 h2 x dBm 0 0 pR ≠ pg k3 2 h2 x dBm 1 1 (Flat.put pR 0 0)

example := nv_ge (st := k3) (l := 2) (hl := h2) (σ := x) (dB := dBm) (pos := 0) (x := 3)
  (pc := pR) (by decide)
#guard nv k3 2 h2 x dBm 0 3 pR = none
-- Negative: `x = 1 < size`, and the result is not none.
#guard nv k3 2 h2 x dBm 0 1 pR ≠ none

/-! ## `ML.lean`: the end of phase C -/

-- The slots `x x` with the destinations `0 0`: no vacant offset for the second `x`.
def kF : Flat.St := ks [x, x] [0, 0] [1, 0]

/- The kernel does not share the value of a term, and its decision of the equality of two vectors
of `MAX_N` entries takes more than 40 s. Thus the examples get the vectors of `readDestinations`
and `regroup` with `Option.get` (`isSome` takes less than 1 s in the kernel), and a `#guard`
compares them with the expected vectors. -/

theorem rdFs : (Flat.readDestinations kF 0 Flat.initial).isSome := by decide +kernel
-- The destinations of `kF`.
def dF : Vector Word MAX_N := (Flat.readDestinations kF 0 Flat.initial).get rdFs
#guard dF = kw [0, 0]
theorem rdF : Flat.readDestinations kF 0 Flat.initial = some dF := (Option.some_get rdFs).symm
theorem rgFn : (Flat.regroup kF 0 dF (Flat.clearDesired kF 0 Flat.initial)).isNone := by
  decide +kernel
theorem rgF : Flat.regroup kF 0 dF (Flat.clearDesired kF 0 Flat.initial) = none :=
  Option.isNone_iff_eq_none.mp rgFn
theorem szF : kF.size ≠ 0 := by decide +kernel

example := rg_none (st := kF) ⟨dF, rdF, rgF⟩ szF
#guard Flat.regroup kF 0 (kw [0, 0]) (Flat.clearDesired kF 0 Flat.initial) = none
#guard fr (Flat.permute kF) = fr (.assertionFailed, kF)
-- Negative: `regroup` of `k3` does not fail, and `permute` does not fail.
#guard Flat.regroup k3 0 pR dBc ≠ none
#guard (Flat.permute k3).1 ≠ .assertionFailed

def pG : Vector Word MAX_N := kw [1, 0, 2]

theorem rd3s : (Flat.readDestinations k3 0 Flat.initial).isSome := by decide +kernel
-- The destinations of `k3`.
def d3 : Vector Word MAX_N := (Flat.readDestinations k3 0 Flat.initial).get rd3s
#guard d3 = pR
theorem rd3 : Flat.readDestinations k3 0 Flat.initial = some d3 := (Option.some_get rd3s).symm
theorem rg3s : (Flat.regroup k3 0 d3 (Flat.clearDesired k3 0 Flat.initial)).isSome := by
  decide +kernel
-- The result of `regroup` for `k3`.
def pK : Vector Word MAX_N := (Flat.regroup k3 0 d3 (Flat.clearDesired k3 0 Flat.initial)).get rg3s
#guard pK = pG
theorem rg3 : Flat.regroup k3 0 d3 (Flat.clearDesired k3 0 Flat.initial) = some pK :=
  (Option.some_get rg3s).symm
theorem sz3 : k3.size ≠ 0 := by decide +kernel
theorem ok3 : PermOk k3 := by decide +kernel

example := rg_some (st := k3) (p := pK) ⟨d3, rd3, rg3⟩ sz3 (by decide +kernel) ok3
#guard fr (Flat.permute k3) = fr (Flat.permuteLoop (2 * k3.size.toNat) k3 (k3.size - 1) pG)
#guard Bij k3.size pG
-- Negative: the destinations of `notBij` are not `PermOk`, and `regroup` gives a vector that is
-- not a bijection.
#guard ¬PermOk notBij
#guard ((Flat.readDestinations notBij 0 Flat.initial).bind fun p =>
  (Flat.regroup notBij 0 p (Flat.clearDesired notBij 0 Flat.initial)).map
    fun q => decide (Bij notBij.size q)) = some false

/-! ## `MD.lean`: `mu` -/

example := mu_agB (n := 3) (u := kw [1, 0, 2, 5]) (v := kw [1, 0, 2, 7]) (by decide)
  (by decide +kernel)
#guard mu (3 - 1) (kw [1, 0, 2, 5]) = mu (3 - 1) (kw [1, 0, 2, 7])
-- Edge: `n = 1`.
example := mu_agB (n := 1) (u := kw [0, 5]) (v := kw [0]) (by decide) (by decide +kernel)
#guard mu (1 - 1) (kw [0, 5]) = mu (1 - 1) (kw [0])
-- Negative: the vectors differ at the top `n - 1`, and `mu` differs.
#guard ¬AgB 3 (kw [1, 0, 2]) (kw [1, 0, 0])
#guard mu (3 - 1) (kw [1, 0, 2]) ≠ mu (3 - 1) (kw [1, 0, 0])
-- Negative: the vectors differ below the top, and `mu` differs.
#guard ¬AgB 3 (kw [1, 0, 2]) (kw [0, 1, 2])
#guard mu (3 - 1) (kw [1, 0, 2]) ≠ mu (3 - 1) (kw [0, 1, 2])

/-! ## `MD.lean`: the loop of `permute` -/

example := loop_succ 3 k3 2 pG
#guard fr (Flat.permuteLoop (3 + 1) k3 2 pG) = fr (after 3 2 (Flat.permuteStep k3 2 pG))
-- Edge: no fuel after the step.
#guard fr (Flat.permuteLoop (0 + 1) k3 2 pG) = fr (after 0 2 (Flat.permuteStep k3 2 pG))
-- `loop_succ` has no hypothesis. The fuel `f + 1` is necessary: with no fuel the loop fails.
#guard fr (Flat.permuteLoop 0 k3 2 pG) ≠ fr (after 0 2 (Flat.permuteStep k3 2 pG))

example := after_cont 2 2 k3 pG
#guard fr (after 2 2 (.cont k3 pG)) = fr (Flat.permuteLoop 2 k3 2 pG)
example := after_ret 2 2 (.done, k3)
#guard fr (after 2 2 (.ret (.done, k3))) = fr (.done, k3)

-- The identity, and a vector where the top is not in place and the offset below the top is not in
-- place.
def pI : Vector Word MAX_N := kw [0, 1, 2]
def pN : Vector Word MAX_N := kw [1, 2, 0]

example := step_ne (st := k3) (top := 2) (p := pR) (by decide +kernel)
#guard nextV (Flat.permuteStep k3 2 pR) = nextV (Flat.exchange k3 2 pR (Flat.get pR 2))
-- Negative: `p[2] = 2`, and `permuteStep` does not exchange `2`.
#guard Flat.get pG 2 = 2
#guard nextV (Flat.permuteStep k3 2 pG) ≠ nextV (Flat.exchange k3 2 pG (Flat.get pG 2))

-- The right side of `step_eq`.
def stepEq (st : Flat.St) (top : Word) (p : Vector Word MAX_N) : Flat.PNext :=
  if Flat.misplacedBelow p top top = top then .ret (.done, st)
  else Flat.exchange st top p (Flat.misplacedBelow p top top)

example := step_eq (st := k3) (top := 2) (p := pG) (by decide +kernel)
#guard nextV (Flat.permuteStep k3 2 pG) = nextV (stepEq k3 2 pG)
-- Edge: all offsets in place, and the loop ends.
example := step_eq (st := k3) (top := 2) (p := pI) (by decide +kernel)
#guard nextV (Flat.permuteStep k3 2 pI) = nextV (stepEq k3 2 pI)
#guard nextV (stepEq k3 2 pI) = nextV (.ret (.done, k3))
-- Negative: `p[2] = 0 ≠ 2`, and `permuteStep` exchanges `0`, not `1`.
#guard Flat.get pN 2 ≠ 2
#guard nextV (Flat.permuteStep k3 2 pN) ≠ nextV (stepEq k3 2 pN)

example := mb_zero pG 2
#guard Flat.misplacedBelow pG 2 0 = 2
-- Edge: `top = 2 ^ 64 - 1`.
#guard Flat.misplacedBelow pG (-1) 0 = -1

example := mb_in (p := pG) (top := 2) (c := 3) (by decide) (by decide +kernel)
#guard Flat.misplacedBelow pG 2 3 = Flat.misplacedBelow pG 2 (3 - 1)
-- Edge: `c = 1`.
example := mb_in (p := pI) (top := 2) (c := 1) (by decide) (by decide +kernel)
#guard Flat.misplacedBelow pI 2 1 = Flat.misplacedBelow pI 2 (1 - 1)
-- Negative: `p[1] ≠ 1`, and the loop stops at `1`.
#guard Flat.get pG (2 - 1) ≠ 2 - 1
#guard Flat.misplacedBelow pG 2 2 ≠ Flat.misplacedBelow pG 2 (2 - 1)
-- Negative: `c = 0` (and `p[c - 1]` is out of the vector), and the two sides differ.
#guard Flat.get pG (0 - 1) ≠ 0 - 1
#guard Flat.misplacedBelow pG 2 0 ≠ Flat.misplacedBelow pG 2 (0 - 1)

example := mb_out (p := pG) (top := 2) (c := 2) (by decide) (by decide +kernel)
#guard Flat.misplacedBelow pG 2 2 = 2 - 1
-- Negative: `p[2] = 2`, and the result is not `2`.
#guard Flat.get pG (3 - 1) = 3 - 1
#guard Flat.misplacedBelow pG 2 3 ≠ 3 - 1

/-! ## `MD.lean`: `exchange` -/

-- `18` different slots: the slot at `0` has the depth `17`, the slot at `1` has the depth `16`.
def k18 : Flat.St := kd 18
def p18 : Vector Word MAX_N := kw (List.range 18)

example := ex_eq (st := k3) (top := 2) (p := pR) (pos := 0) (by decide +kernel)
#guard nextV (Flat.exchange k3 2 pR 0) = nextV (.cont (Flat.swapDestinations k3 0 2) (swapP pR 2 0))
-- Negative: the slot at `1` is `y`, and `exchange` swaps the slots.
#guard Flat.get k3.data 1 ≠ Flat.get k3.data (k3.size - 1)
#guard nextV (Flat.exchange k3 2 pR 1)
  ≠ nextV (.cont (Flat.swapDestinations k3 1 2) (swapP pR 2 1))

example := ex_unr (st := k18) (top := 17) (p := p18) (pos := 0) (by decide +kernel)
  (by decide +kernel)
#guard nextV (Flat.exchange k18 17 p18 0) = nextV (.ret (Flat.blockSwapUnreachable k18 0))
-- Negative: the slot at `1` has the depth `16`, and `exchange` swaps it.
#guard Flat.isSwapReachable k18 1 = true
#guard nextV (Flat.exchange k18 17 p18 1) ≠ nextV (.ret (Flat.blockSwapUnreachable k18 1))

example := ex_sw (st := k3) (top := 2) (p := pR) (pos := 1) (by decide +kernel) (by decide +kernel)
#guard nextV (Flat.exchange k3 2 pR 1)
  = nextV (.cont (Flat.swapDestinations (Flat.stackSwap k3 1) 1 2) (swapP pR 2 1))
-- Edge: the depth `16`.
example := ex_sw (st := k18) (top := 17) (p := p18) (pos := 1) (by decide +kernel)
  (by decide +kernel)
#guard nextV (Flat.exchange k18 17 p18 1)
  = nextV (.cont (Flat.swapDestinations (Flat.stackSwap k18 1) 1 17) (swapP p18 17 1))
-- Negative: equal slots, and `exchange` does not swap.
#guard nextV (Flat.exchange k3 2 pR 0)
  ≠ nextV (.cont (Flat.swapDestinations (Flat.stackSwap k3 0) 0 2) (swapP pR 2 0))
-- Negative: the depth `17`, and `exchange` does not swap.
#guard Flat.isSwapReachable k18 0 = false
#guard nextV (Flat.exchange k18 17 p18 0)
  ≠ nextV (.cont (Flat.swapDestinations (Flat.stackSwap k18 0) 0 17) (swapP p18 17 0))

-- The right side of `bsu_eq`.
def bsu (st : Flat.St) (pos : Word) : Flat.Status × Flat.St :=
  (.blocked, { st with blockedOffset := pos, blockedExcess := st.size - pos - 17#64 })

-- The depth `17`: the excess is `1`.
example := bsu_eq (st := k18) (pos := 0) (by decide +kernel)
#guard fr (Flat.blockSwapUnreachable k18 0) = fr (bsu k18 0)
#guard (Flat.blockSwapUnreachable k18 0).2.blockedExcess = 1
-- Negative: the depth `16`, and `blockSwapUnreachable` fails.
#guard k18.size - 1 - 1#64 ≤ 16#64
#guard fr (Flat.blockSwapUnreachable k18 1) ≠ fr (bsu k18 1)
#guard (Flat.blockSwapUnreachable k18 1).1 = .assertionFailed
-- Edge: `pos ≥ size`. The depth wraps, and the excess wraps.
example := bsu_eq (st := k3) (pos := 5) (by decide +kernel)
#guard fr (Flat.blockSwapUnreachable k3 5) = fr (bsu k3 5)
#guard (Flat.blockSwapUnreachable k3 5).2.blockedExcess = -19

/-! ## `MD.lean`: the permutation -/

-- `p[n - 1] = pos`.
example := Mis.step (n := 3) (pos := 1) (p := pR) (by decide) (by decide +kernel)
  (by decide +kernel)
#guard Bij 3 (swapP pR (3 - 1) 1)
#guard mu (3 - 1) (swapP pR (3 - 1) 1) < mu (3 - 1) pR
-- `p[n - 1] = n - 1` and `p[pos] ≠ pos`.
example := Mis.step (n := 3) (pos := 1) (p := pG) (by decide) (by decide +kernel)
  (by decide +kernel)
#guard Bij 3 (swapP pG (3 - 1) 1)
#guard mu (3 - 1) (swapP pG (3 - 1) 1) < mu (3 - 1) pG
-- Negative: `pos = n - 1`, and the swap does not make `mu` smaller.
#guard ¬Mis 3 2 pR
#guard Bij 3 pR
#guard ¬mu (3 - 1) (swapP pR (3 - 1) 2) < mu (3 - 1) pR
-- Negative: `p` is not a bijection (`Mis` holds), and the swap gives no bijection.
#guard ¬Bij 3 (kw [0, 0, 1]) ∧ Mis 3 1 (kw [0, 0, 1])
#guard ¬Bij 3 (swapP (kw [0, 0, 1]) (3 - 1) 1)

-- The left vector of the conclusion of `agB_swap`.
def set2 (P : Vector Word MAX_N) (top pos : Word) (htM : top.toNat < MAX_N)
    (hpM : pos.toNat < MAX_N) : Vector Word MAX_N :=
  (P.set pos.toNat P[top.toNat] hpM).set top.toNat P[pos.toNat] htM

example := agB_swap (n := 3) (top := 2) (pos := 1) (P := kw [2, 0, 1, 7]) (p := pR)
  (by decide +kernel) (by decide) (by decide) (by decide) (by decide)
#guard AgB 3 (set2 (kw [2, 0, 1, 7]) 2 1 (by decide) (by decide)) (swapP pR 2 1)
-- Edge: `top = pos`.
example := agB_swap (n := 3) (top := 2) (pos := 2) (P := kw [2, 0, 1, 7]) (p := pR)
  (by decide +kernel) (by decide) (by decide) (by decide) (by decide)
#guard AgB 3 (set2 (kw [2, 0, 1, 7]) 2 2 (by decide) (by decide)) (swapP pR 2 2)
-- Negative: no agreement at `2`, and none after the swap.
#guard ¬AgB 3 (kw [2, 0, 5]) pR
#guard ¬AgB 3 (set2 (kw [2, 0, 5]) 2 0 (by decide) (by decide)) (swapP pR 2 0)
-- Negative: `top = n`, where the vectors differ, and no agreement after the swap.
#guard AgB 3 (kw [2, 0, 1, 7]) (kw [2, 0, 1, 9])
#guard ¬AgB 3 (set2 (kw [2, 0, 1, 7]) 3 0 (by decide) (by decide)) (swapP (kw [2, 0, 1, 9]) 3 0)

example := ltB_swapD (n := 3) (a := 0) (b := 2) (d := pR) (by decide +kernel) (by decide)
  (by decide)
#guard LtB 3 (swapD pR 0 2)
-- Negative: `a = n`, and a destination is not below `n`.
#guard LtB 3 (kw [2, 0, 1, 5])
#guard ¬LtB 3 (swapD (kw [2, 0, 1, 5]) 3 0)
-- Negative: not `LtB`, and not `LtB` after the swap.
#guard ¬LtB 3 (kw [2, 0, 7])
#guard ¬LtB 3 (swapD (kw [2, 0, 7]) 0 1)

/-! ## `Inv.lean`: the variant on the back edge of phase D

A concrete `MachineData` has a memory of `2 ^ 64` bytes, and `mD` reads `MAX_N` words of it. Thus
these examples are symbolic: `pm_dec` (the tactic of the proofs) unfolds `V`. -/

example (s t : MachineData) (g : G) : V s g ".LB.Emission.permute.22" t = 2048 * mD s g t := by pm_dec
example (s t : MachineData) (g : G) : V s g ".LB.Emission.permute.23" t = 2048 * mD s g t + 1101 := by pm_dec
example (s t : MachineData) (g : G) : V s g ".LB.Emission.permute.15" t = 2048 * mD s g t + 1101 := by pm_dec

-- The edge `.LB.Emission.permute.22` to `.LB.Emission.permute.23` (`lt80` of `D2.lean`): `V` gets smaller if and only if `mD` gets
-- smaller.
example (s t u : MachineData) (g : G) (h : mD s g u < mD s g t) :
    V s g ".LB.Emission.permute.23" u < V s g ".LB.Emission.permute.22" t := by pm_dec
example (s t u : MachineData) (g : G) :
    V s g ".LB.Emission.permute.23" u < V s g ".LB.Emission.permute.22" t ↔ mD s g u < mD s g t := by pm_dec
-- Negative: `mD` does not change, and `V` does not get smaller.
example (s t u : MachineData) (g : G) (h : mD s g u = mD s g t) :
    ¬V s g ".LB.Emission.permute.23" u < V s g ".LB.Emission.permute.22" t := by pm_dec
-- The arithmetic of the edge on small values.
#guard (List.range 5).all fun a => (List.range 5).all fun b =>
  decide (2048 * a + 1101 < 2048 * b) == decide (a < b)

/-! ## The loop of `permute` on all inputs of `check`

At each iteration, `stepsOk` compares the model with the lemmas:
* `permuteStep` with the right side of `step_ne` or `step_eq`;
* `permuteLoop (f + 1)` with `after f top (permuteStep ..)` (`loop_succ`);
* `exchange` with the right side of `ex_eq`, `ex_unr` or `ex_sw`;
* at the exchanged offset `pos`: `Bij`, `Mis` and the conclusion of `Mis.step`. -/

-- The right side of `step_ne` or `step_eq`.
def stepR (st : Flat.St) (top : Word) (p : Vector Word MAX_N) : Flat.PNext :=
  if Flat.get p top ≠ top then Flat.exchange st top p (Flat.get p top) else stepEq st top p

-- The right side of `ex_eq`, `ex_unr` or `ex_sw`.
def exR (st : Flat.St) (top : Word) (p : Vector Word MAX_N) (pos : Word) : Flat.PNext :=
  if Flat.get st.data pos = Flat.get st.data (st.size - 1) then
    .cont (Flat.swapDestinations st pos top) (swapP p top pos)
  else if Flat.isSwapReachable st pos = false then .ret (Flat.blockSwapUnreachable st pos)
  else .cont (Flat.swapDestinations (Flat.stackSwap st pos) pos top) (swapP p top pos)

def stepsOk (top : Word) : Nat → Flat.St → Vector Word MAX_N → Bool
  | 0, _, _ => true
  | f + 1, st, p =>
    let n := st.size
    let r := Flat.permuteStep st top p
    let pos := if Flat.get p top ≠ top then Flat.get p top else Flat.misplacedBelow p top top
    let okStep := nextV r == nextV (stepR st top p)
    let okLoop := fr (Flat.permuteLoop (f + 1) st top p) == fr (after f top r)
    let okEx := pos == top || nextV (Flat.exchange st top p pos) == nextV (exR st top p pos)
    let okMis := pos == top
      || (decide (Bij n p) && decide (Mis n pos p) && decide (Bij n (swapP p (n - 1) pos))
        && decide (mu (n - 1) (swapP p (n - 1) pos) < mu (n - 1) p))
    okStep && okLoop && okEx && okMis && match r with
      | .ret _ => true
      | .cont st p => stepsOk top f st p

-- The facts for the slots `s` and the destinations `d`, from the vector of `regroup`.
def propOk (s : List StackSlot) (d : List Nat) : Bool :=
  let st := mk s s d
  match Flat.readDestinations st 0 Flat.initial with
  | none => false
  | some p0 =>
    match Flat.regroup st 0 p0 (Flat.clearDesired st 0 Flat.initial) with
    | none => false
    | some p => decide (Bij st.size p) && stepsOk (st.size - 1) (2 * s.length) st p

#guard inputs.length = 442
#guard inputs.all fun (s, d) => propOk s d

-- The forms of the iterations of a run: `3 * s + e`, with `s = 0` for `step_ne` and `s = 1` for
-- `step_eq`, and `e = 0` for `ex_eq`, `e = 1` for `ex_unr` and `e = 2` for `ex_sw`. `6` is the end.
def forms (top : Word) : Nat → Flat.St → Vector Word MAX_N → List Nat
  | 0, _, _ => []
  | f + 1, st, p =>
    let s := if Flat.get p top ≠ top then 0 else 1
    let pos := if Flat.get p top ≠ top then Flat.get p top else Flat.misplacedBelow p top top
    if pos = top then [6] else
    let e := if Flat.get st.data pos = Flat.get st.data (st.size - 1) then 0
      else if Flat.isSwapReachable st pos = false then 1 else 2
    (3 * s + e) :: match Flat.permuteStep st top p with
      | .ret _ => []
      | .cont st p => forms top f st p

def formsOf (s : List StackSlot) (d : List Nat) : List Nat :=
  let st := mk s s d
  match Flat.readDestinations st 0 Flat.initial with
  | none => []
  | some p0 =>
    match Flat.regroup st 0 p0 (Flat.clearDesired st 0 Flat.initial) with
    | none => []
    | some p => forms (st.size - 1) (2 * s.length) st p

-- The inputs reach the end of the loop, and each form of `exchange` except `ex_unr`. `ex_unr` needs
-- a depth above `16` (see `k18`), and the sizes `1` to `4` do not give one.
#guard [0, 2, 3, 5, 6].all fun c => inputs.any fun (s, d) => (formsOf s d).contains c
#guard inputs.all fun (s, d) => (formsOf s d).contains 6
#guard inputs.all fun (s, d) => !(formsOf s d).contains 1 && !(formsOf s d).contains 4
-- Negative: the destinations of `notBij` are not a bijection, and the checks fail.
#guard !propOk [x, y] [0, 0]
#guard !stepsOk 1 4 notBij (pv [0, 0])

end Bbu.Unit.Permute.MLTest
