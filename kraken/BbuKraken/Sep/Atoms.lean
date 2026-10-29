import BbuKraken.Layout
import Kraken.SepCancel

/-!
# Separation atoms

The atoms are `List.AtM` of the bytes that a store of the asm writes: `Wd` for a word (`movq`),
`B8`, `B16` and `B32` for 1, 2 and 4 bytes (`movb`, `movw`, `movl`). `Arr` is a list of words.
Each atom has a load lemma (`rd` or `isSome`) and a store lemma on a hypothesis
`(A ∗ F).get m`, with the atom first. Use `ecancel` to move an atom to the front.

The atoms are irreducible: a lemma of one atom on a hypothesis with another atom first fails at
once. (With reducible atoms, `B8.isSome` on a hypothesis with a `B32` first took a `whnf` timeout.)
-/

namespace Bbu.Sep

/-! ## Atoms -/

-- The word `v` at `a`. The bytes are those that a 64-bit store of `v` writes.
@[irreducible] def Wd (a : Addr) (v : Word) : MProp 64 := (Int.toBytes 8 v.toInt).AtM a
-- 1, 2 and 4 bytes.
@[irreducible] def B8 (a : Addr) (v : BitVec 8) : MProp 64 := (Int.toBytes 1 v.toInt).AtM a
@[irreducible] def B16 (a : Addr) (v : BitVec 16) : MProp 64 := (Int.toBytes 2 v.toInt).AtM a
@[irreducible] def B32 (a : Addr) (v : BitVec 32) : MProp 64 := (Int.toBytes 4 v.toInt).AtM a

-- The words `vs` from `a`.
def Arr (a : Addr) : List Word → MProp 64
  | [] => MProp.emp
  | v :: vs => Wd a v ∗ Arr (a + 8#64) vs

theorem toBytes_ofInt (n w : Nat) (hw : w = 8 * n) (x : Int) :
    Int.toBytes n (BitVec.ofInt w x).toInt = Int.toBytes n x := by
  subst hw
  rw [← Int.toBytes_emod n x, ← Int.toBytes_emod n (BitVec.ofInt (8 * n) x).toInt]
  congr 1
  simp only [Int.take, BitVec.toInt_ofInt]
  have : ((2 ^ (8 * n) : Nat) : Int) = (2 : Int) ^ (8 * n) := by push_cast; rfl
  rw [← this, Int.bmod_emod]

section
variable {a : Addr} {F : MProp 64} {m : Mem 64}

theorem Wd.rd {v : Word} (h : (Wd a v ∗ F).get m) : rd m a = v := by
  unfold Wd at h
  simp only [Bbu.rd, Mem.loadInt_eq_of_AtM h (Int.toBytes_length _ _) (by decide), Option.get!_some,
    BitVec.ofInt_ofBytes_toBytes 64 8 rfl]

theorem Wd.isSome {v : Word} (h : (Wd a v ∗ F).get m) : (m.loadInt a 8).isSome = true := by
  unfold Wd at h
  simp only [Mem.loadInt_eq_of_AtM h (Int.toBytes_length _ _) (by decide), Option.isSome_some]

-- The load of the return address (`MachineData.retAddr`).
theorem Wd.retAddr {v : Word} (h : (Wd a v ∗ F).get m) :
    (m.loadInt a 8).map (fun i => Int64.ofBitVec (BitVec.ofInt 64 i)) = some (Int64.ofBitVec v) := by
  unfold Wd at h
  rw [Mem.loadInt_eq_of_AtM h (Int.toBytes_length _ _) (by decide), Option.map_some,
    BitVec.ofInt_ofBytes_toBytes 64 8 rfl]

theorem Wd.store {v : Word} (h : (Wd a v ∗ F).get m) (w : Word) :
    (Wd a w ∗ F).get (m.storeInt a 8 w.toInt) := by
  unfold Wd at h ⊢
  exact Mem.get_AtM_sep_storeInt h (Int.toBytes_length _ _) _

theorem B8.isSome {v : BitVec 8} (h : (B8 a v ∗ F).get m) : (m.loadInt a 1).isSome = true := by
  unfold B8 at h
  simp only [Mem.loadInt_eq_of_AtM h (Int.toBytes_length _ _) (by decide), Option.isSome_some]

theorem B8.store {v : BitVec 8} (h : (B8 a v ∗ F).get m) (x : Int) :
    (B8 a (BitVec.ofInt 8 x) ∗ F).get (m.storeInt a 1 x) := by
  unfold B8 at h ⊢; rw [toBytes_ofInt 1 8 rfl]
  exact Mem.get_AtM_sep_storeInt h (Int.toBytes_length _ _) _

theorem B32.isSome {v : BitVec 32} (h : (B32 a v ∗ F).get m) : (m.loadInt a 4).isSome = true := by
  unfold B32 at h
  simp only [Mem.loadInt_eq_of_AtM h (Int.toBytes_length _ _) (by decide), Option.isSome_some]

theorem B32.store {v : BitVec 32} (h : (B32 a v ∗ F).get m) (x : Int) :
    (B32 a (BitVec.ofInt 32 x) ∗ F).get (m.storeInt a 4 x) := by
  unfold B32 at h ⊢; rw [toBytes_ofInt 4 32 rfl]
  exact Mem.get_AtM_sep_storeInt h (Int.toBytes_length _ _) _

end

/-! ## Arrays -/

-- The rest of an array after its first word, moved to the front.
private theorem Arr.rot (a : Addr) (v : Word) (vs : List Word) (F : MProp 64) :
    Arr a (v :: vs) ∗ F = Arr (a + 8#64) vs ∗ (Wd a v ∗ F) := by
  simp only [Arr]
  rw [MProp.sep_assoc, ← MProp.sep_assoc (Arr _ _), MProp.sep_comm (Arr _ _) (Wd _ _),
    MProp.sep_assoc]

private theorem addr_succ (a : Addr) (i : Nat) :
    a + BitVec.ofNat 64 (8 * (i + 1)) = a + 8#64 + BitVec.ofNat 64 (8 * i) := by
  rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp; omega

theorem Arr.isSome {a : Addr} {vs : List Word} {F : MProp 64} {m : Mem 64} {i : Nat}
    (h : (Arr a vs ∗ F).get m) (hi : i < vs.length) :
    (m.loadInt (a + BitVec.ofNat 64 (8 * i)) 8).isSome = true := by
  induction vs generalizing a F i with
  | nil => simp at hi
  | cons v vs ih =>
    cases i with
    | zero =>
      simp only [Arr, MProp.sep_assoc] at h
      simpa using Wd.isSome h
    | succ i =>
      rw [Arr.rot] at h
      rw [addr_succ]
      exact ih h (by simpa using hi)

theorem Arr.rd {a : Addr} {vs : List Word} {F : MProp 64} {m : Mem 64} {i : Nat}
    (h : (Arr a vs ∗ F).get m) (hi : i < vs.length) :
    Bbu.rd m (a + BitVec.ofNat 64 (8 * i)) = vs[i] := by
  induction vs generalizing a F i with
  | nil => simp at hi
  | cons v vs ih =>
    cases i with
    | zero =>
      simp only [Arr, MProp.sep_assoc] at h
      simpa using Wd.rd h
    | succ i =>
      rw [Arr.rot] at h
      rw [addr_succ]
      exact ih h (by simpa using hi)

theorem Arr.store {a : Addr} {vs : List Word} {F : MProp 64} {m : Mem 64} {i : Nat}
    (h : (Arr a vs ∗ F).get m) (hi : i < vs.length) (w : Word) :
    (Arr a (vs.set i w) ∗ F).get (m.storeInt (a + BitVec.ofNat 64 (8 * i)) 8 w.toInt) := by
  induction vs generalizing a F i with
  | nil => simp at hi
  | cons v vs ih =>
    cases i with
    | zero =>
      simp only [Arr, MProp.sep_assoc, List.set_cons_zero] at h ⊢
      simpa using Wd.store h w
    | succ i =>
      rw [Arr.rot] at h
      rw [List.set_cons_succ, Arr.rot, addr_succ]
      exact ih h (by simpa using hi)

theorem Arr.append (a : Addr) (xs ys : List Word) :
    Arr a (xs ++ ys) = Arr a xs ∗ Arr (a + BitVec.ofNat 64 (8 * xs.length)) ys := by
  induction xs generalizing a with
  | nil => simp [Arr, MProp.emp_sep]
  | cons x xs ih =>
    simp only [List.cons_append, Arr, ih, MProp.sep_assoc, List.length_cons]
    congr 3
    rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp; omega

/-! ## A word as bytes (the slot store of `swapWith`: 4 + 1 + 1 bytes) -/

theorem toBytes_add (n k : Nat) (v : Int) :
    Int.toBytes (n + k) v = Int.toBytes n v ++ Int.toBytes k (v >>> (8 * n)) := by
  induction n generalizing v with
  | zero => simp [Int.toBytes]
  | succ n ih =>
    rw [show n + 1 + k = (n + k) + 1 by omega]
    simp only [Int.toBytes, ih, List.cons_append]
    rw [show (256 : Int) = ((2 ^ 8 : Nat) : Int) by rfl, ← Int.shiftRight_eq_div_pow,
      ← Int.shiftRight_add]
    rw [show 8 + 8 * n = 8 * (n + 1) by omega]

theorem AtM_append (bs cs : List UInt8) (a : Addr) (h : bs.length + cs.length ≤ 2 ^ 64) :
    (bs ++ cs).AtM a = bs.AtM a ∗ cs.AtM (a + BitVec.ofNat 64 bs.length) :=
  by unfold MProp.sep; rw [List.get_AtM, List.get_AtM, ← Mem.At_append_sep bs cs a h]; rfl

theorem toBytes_sext (k : Nat) (x : Word) :
    Int.toBytes k x.toInt = Int.toBytes k (x.signExtend (8 * k)).toInt :=
  (toBytes_ofInt k (8 * k) rfl x.toInt).symm

theorem Wd.split (a : Addr) (v : Word) :
    Wd a v = B32 a (v.extractLsb' 0 32) ∗ B8 (a + 4#64) (v.extractLsb' 32 8)
      ∗ B8 (a + 5#64) (v.extractLsb' 40 8) ∗ B16 (a + 6#64) (v.extractLsb' 48 16) := by
  unfold Wd B32 B8 B16
  rw [show Int.toBytes 8 v.toInt = Int.toBytes (4 + (1 + (1 + 2))) v.toInt from rfl, toBytes_add,
    toBytes_add, toBytes_add, AtM_append _ _ _ (by simp [Int.toBytes_length]),
    AtM_append _ _ _ (by simp [Int.toBytes_length]), AtM_append _ _ _ (by simp [Int.toBytes_length])]
  simp only [Int.toBytes_length, ← BitVec.toInt_sshiftRight]
  rw [toBytes_sext 4, toBytes_sext 1, toBytes_sext 1, toBytes_sext 2]
  have e1 : v.signExtend (8 * 4) = v.extractLsb' 0 32 := by bv_decide
  have e2 : (v.sshiftRight (8 * 4)).signExtend (8 * 1) = v.extractLsb' 32 8 := by bv_decide
  have e3 : ((v.sshiftRight (8 * 4)).sshiftRight (8 * 1)).signExtend (8 * 1) = v.extractLsb' 40 8 := by
    bv_decide
  have e4 : (((v.sshiftRight (8 * 4)).sshiftRight (8 * 1)).sshiftRight (8 * 1)).signExtend (8 * 2)
      = v.extractLsb' 48 16 := by bv_decide
  have a1 : a + BitVec.ofNat 64 4 + BitVec.ofNat 64 1 = a + 5#64 := by bv_decide
  have a2 : a + BitVec.ofNat 64 4 + BitVec.ofNat 64 1 + BitVec.ofNat 64 1 = a + 6#64 := by bv_decide
  rw [e1, e2, e3, e4, a2, a1]

theorem sep_lc (P Q R : MProp 64) : P ∗ Q ∗ R = Q ∗ P ∗ R := by
  rw [← MProp.sep_assoc, MProp.sep_comm P, MProp.sep_assoc]

-- `movl` to `a`, `movb` to `a + 4` and `a + 5`. Bytes 6 and 7 do not change.
theorem Wd.store411 {a : Addr} {v : Word} {F : MProp 64} {m : Mem 64} (h : (Wd a v ∗ F).get m)
    (x : BitVec 32) (y z : BitVec 8) :
    (Wd a (v.extractLsb' 48 16 ++ z ++ y ++ x) ∗ F).get
      (((m.storeInt a 4 x.toInt).storeInt (a + 4#64) 1 y.toInt).storeInt (a + 5#64) 1 z.toInt) := by
  rw [Wd.split] at h ⊢
  simp only [MProp.sep_assoc] at h ⊢
  have h1 := B32.store h x.toInt
  rw [sep_lc] at h1
  have h2 := B8.store h1 y.toInt
  rw [sep_lc (B8 (a + 4#64) _), sep_lc (B8 (a + 4#64) _), sep_lc (B32 a _)] at h2
  have h3 := B8.store h2 z.toInt
  simp only [BitVec.ofInt_toInt] at h3
  have e1 : (v.extractLsb' 48 16 ++ z ++ y ++ x).extractLsb' 0 32 = x := by bv_decide
  have e2 : (v.extractLsb' 48 16 ++ z ++ y ++ x).extractLsb' 32 8 = y := by bv_decide
  have e3 : (v.extractLsb' 48 16 ++ z ++ y ++ x).extractLsb' 40 8 = z := by bv_decide
  have e4 : (v.extractLsb' 48 16 ++ z ++ y ++ x).extractLsb' 48 16 = v.extractLsb' 48 16 := by
    bv_decide
  rw [e1, e2, e3, e4, sep_lc (B8 (a + 4#64) _), sep_lc (B32 a _)]
  exact h3

end Bbu.Sep
