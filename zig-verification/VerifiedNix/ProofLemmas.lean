module

public import Kraken.X64.WP.Spec
import all Kraken.SeparationMem
import all Kraken.X64.Semantics

@[expose] public section

/-! Memory regions and load prefixes. -/

theorem Mem.WritesOnly.mono {w : Nat} {bs cs : List (BitVec w × Nat)} {m m' : Mem w}
    (h : Mem.WritesOnly bs m m')
    (hs : ∀ a, Mem.Blocks.Inside a 1 bs → Mem.Blocks.Inside a 1 cs) :
    Mem.WritesOnly cs m m' :=
  ⟨fun a ha => h.1 a (fun hb => ha (hs a hb)), h.2⟩

theorem Mem.WritesOnly.trans_append {w : Nat} {bs cs : List (BitVec w × Nat)}
    {m m' m'' : Mem w} (h : Mem.WritesOnly bs m m') (h' : Mem.WritesOnly cs m' m'') :
    Mem.WritesOnly (bs ++ cs) m m'' :=
  (h.mono (fun _ ha => Mem.Blocks.Inside.append_iff.mpr (Or.inl ha))).trans
    (h'.mono (fun _ ha => Mem.Blocks.Inside.append_iff.mpr (Or.inr ha)))

theorem Mem.loadBytes_take {w n k : Nat} {m : Mem w} {a : BitVec w} {bs : List UInt8}
    (hn : n ≤ k) (h : m.loadBytes a k = some bs) :
    m.loadBytes a n = some (bs.take n) := by
  obtain ⟨hlen, hb⟩ := Mem.loadBytes_eq_some_iff.mp h
  apply Mem.loadBytes_eq_some_iff.mpr
  refine ⟨by simp [List.length_take, hlen, hn], fun i hi => ?_⟩
  simpa only [List.getElem_take] using hb i (by simp only [List.length_take] at hi; omega)

theorem Mem.loadInt_take {w n k : Nat} {m : Mem w} {a : BitVec w} {v : Int}
    (hn : n ≤ k) (h : m.loadInt a k = some v) :
    BitVec.ofInt (8 * n) (m.loadInt a n).get! = BitVec.ofInt (8 * n) v := by
  obtain ⟨bs, hb, rfl⟩ := Option.map_eq_some_iff.mp h
  rw [Mem.loadInt, Mem.loadBytes_take hn hb, Option.map_some, Option.get!_some]
  exact (BitVec.ofInt_ofBytes_take (8 * n) n rfl bs).symm

/-- Truncation commutes with conversion from an integer. -/
theorem BitVec.setWidth_ofInt {n w : Nat} (h : n ≤ w) (i : Int) :
    (BitVec.ofInt w i).setWidth n = BitVec.ofInt n i := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofInt]
  have hw : 0 ≤ i % ((2 ^ w : Nat) : Int) := Int.emod_nonneg _ (by
    exact_mod_cast Nat.ne_of_gt (Nat.two_pow_pos w))
  have hn : 0 ≤ i % ((2 ^ n : Nat) : Int) := Int.emod_nonneg _ (by
    exact_mod_cast Nat.ne_of_gt (Nat.two_pow_pos n))
  apply Int.ofNat_inj.mp
  rw [Int.natCast_emod]
  rw [Int.toNat_of_nonneg hw, Int.toNat_of_nonneg hn]
  exact Int.emod_emod_of_dvd i (Int.ofNat_dvd.mpr (Nat.pow_dvd_pow 2 h))

theorem Mem.Contains.loadInt_add {w : Nat} {m : Mem w} {a x : BitVec w} {bs : List UInt8}
    (h : Mem.Contains m a bs) (hx : x.toNat < bs.length) :
    m.loadInt (a + x) 1 = some (bs[x.toNat]!.toNat : Int) := by
  have he : a + x - a = x := by rw [BitVec.add_comm, BitVec.add_sub_cancel]
  simpa only [he] using h.loadInt (addr := a + x) (by rwa [he])

theorem Mem.Contains.drop {w : Nat} {m : Mem w} {a : BitVec w} {bs : List UInt8}
    (h : Mem.Contains m a bs) (k : Nat) :
    Mem.Contains m (a + BitVec.ofNat w k) (bs.drop k) := by
  apply Mem.Contains.iff.mpr
  intro i hi
  have hb := Mem.Contains.iff.mp h (k + i) (by simp only [List.length_drop] at hi; omega)
  simpa only [List.getElem_drop, BitVec.ofNat_add, BitVec.add_assoc] using hb

theorem MachineData.stackAtOrBelow_of_rsp {s t : MachineData}
    (h : t.regs.get64 .rsp = s.regs.get64 .rsp) : t.StackAtOrBelow s := by
  simp only [MachineData.StackAtOrBelow, MachineData.StackBelow, h]
  exact BitVec.not_serialLt_self _

/-! Condition-code normal forms. -/

@[simp, grind =, vcgen_simp] theorem CondCode.interp_o (s : StatusFlags) :
    CondCode.o.interp s = s.of := rfl

@[simp 1100, grind =, vcgen_simp] theorem CondCode.interp_nc_ofSub {w : Nat} (a b : BitVec w) :
    CondCode.nc.interp (StatusFlags.ofSub a b) = b.ule a := by
  apply Bool.eq_iff_iff.mpr
  simp [BitVec.usubOverflow, BitVec.ule_eq_decide]

@[simp 1100, grind =, vcgen_simp] theorem CondCode.interp_z_ofSub {w : Nat} (a b : BitVec w) :
    CondCode.z.interp (StatusFlags.ofSub a b) = (a == b) := by
  apply Bool.eq_iff_iff.mpr
  simp [BitVec.sub_eq_iff_eq_add]

@[simp 1100, grind =, vcgen_simp] theorem CondCode.interp_nz_ofSub {w : Nat} (a b : BitVec w) :
    CondCode.nz.interp (StatusFlags.ofSub a b) = (a != b) := by
  rw [bne_eq, CondCode.interp_nz, ← CondCode.interp_z, CondCode.interp_z_ofSub]

@[simp 1100, grind =, vcgen_simp] theorem CondCode.interp_z_ofLogic {w : Nat} (a : BitVec w) (af : Bool) :
    CondCode.z.interp (StatusFlags.ofLogic a af) = (a == 0) := by simp

@[simp 1100, grind =, vcgen_simp] theorem CondCode.interp_nz_ofLogic {w : Nat} (a : BitVec w) (af : Bool) :
    CondCode.nz.interp (StatusFlags.ofLogic a af) = (a != 0) := by
  rw [bne_eq, CondCode.interp_nz, ← CondCode.interp_z, CondCode.interp_z_ofLogic]
