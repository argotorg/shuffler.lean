module

public import FlatShuffler.Sep.Contract
import all FlatShuffler.Sep.Contract

@[expose] public section

/-!
# Atoms from mapped memory

A caller that has only `Mem.Mapped` facts gives a callee a `∗` assertion: `cut m p` is the part
of `m` at the addresses in `p`, and an atom holds on the part at its bytes, with the values that
`m` holds (`Wd.cut`, `Arr.cut`). `sep_cut` joins two parts with disjoint address sets. The rest of
the memory is `cut m (¬ p)`, an exact frame.

After the call, `Single` (an assertion holds on at most one memory) and `Dom` (the addresses of
the memory of an assertion) give which bytes the callee did not change (`frame_eq`).
-/

namespace FlatShuffler.Sep

open Std

/-! ## Address sets -/

-- The `n` bytes from `a`, modulo `2 ^ 64`.
def In (a : Addr) (n : Nat) (b : Addr) : Prop := (b - a).toNat < n

-- The bytes `o .. o + k` from `S`.
def Rng (S : Addr) (o k : Nat) (b : Addr) : Prop := o ≤ (b - S).toNat ∧ (b - S).toNat < o + k

theorem in_ofNat {S b : Addr} {o k : Nat} (h : o + k ≤ 2 ^ 64) :
    In (S + BitVec.ofNat 64 o) k b ↔ Rng S o k b := by
  unfold In Rng
  rw [show b - (S + BitVec.ofNat 64 o) = b - S - BitVec.ofNat 64 o by bv_omega]
  generalize b - S = x
  have := x.isLt
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat]
  by_cases ho : o < 2 ^ 64
  · rw [Nat.mod_eq_of_lt ho]
    by_cases hx : o ≤ x.toNat
    · rw [show 2 ^ 64 - o + x.toNat = 2 ^ 64 + (x.toNat - o) by omega, Nat.add_mod_left,
        Nat.mod_eq_of_lt (by omega)]
      omega
    · rw [Nat.mod_eq_of_lt (by omega)]; omega
  · omega

theorem in_iff_rng {S b : Addr} {k : Nat} : In S k b ↔ Rng S 0 k b := by
  unfold In Rng; omega

theorem rng_split {S b : Addr} {o k l : Nat} : Rng S o (k + l) b ↔ Rng S o k b ∨ Rng S (o + k) l b := by
  unfold Rng; omega

theorem rng_disj {S b : Addr} {o k l : Nat} (h1 : Rng S o k b) (h2 : Rng S (o + k) l b) : False := by
  unfold Rng at h1 h2; omega

theorem in_split {a b : Addr} {k l : Nat} (h : k + l ≤ 2 ^ 64) :
    In a (k + l) b ↔ In a k b ∨ In (a + BitVec.ofNat 64 k) l b := by
  rw [in_iff_rng, in_iff_rng, in_ofNat (by omega), rng_split, Nat.zero_add]

theorem in_disj {a b : Addr} {k l : Nat} (h : k + l ≤ 2 ^ 64) (h1 : In a k b)
    (h2 : In (a + BitVec.ofNat 64 k) l b) : False := by
  rw [in_iff_rng] at h1; rw [in_ofNat h] at h2
  exact rng_disj h1 (by simpa using h2)

/-! ## Parts of a memory -/

open Classical in
-- The part of `m` at the addresses in `p`.
noncomputable def cut (m : Mem 64) (p : Addr → Prop) : Mem 64 := m.filter fun a _ => decide (p a)

open Classical in
theorem get?_cut (m : Mem 64) (p : Addr → Prop) (b : Addr) :
    (cut m p)[b]? = if p b then m[b]? else none := by
  unfold cut
  rw [ExtHashMap.getElem?_filter']
  by_cases h : p b <;> cases m[b]? <;> simp [h]

theorem mem_cut {m : Mem 64} {p : Addr → Prop} {b : Addr} : b ∈ cut m p ↔ p b ∧ b ∈ m := by
  classical
  rw [ExtHashMap.mem_iff_isSome_getElem?, ExtHashMap.mem_iff_isSome_getElem?, get?_cut]
  by_cases h : p b <;> simp [h]

theorem cut_congr (m : Mem 64) {p q : Addr → Prop} (h : ∀ b, p b ↔ q b) : cut m p = cut m q := by
  have : p = q := funext fun b => propext (h b)
  subst this; rfl

theorem cut_univ (m : Mem 64) {p : Addr → Prop} (h : ∀ b, p b) : cut m p = m := by
  classical
  apply ExtHashMap.ext_getElem?; intro b
  rw [get?_cut]; simp only [h b, ↓reduceIte]

theorem cut_none (m : Mem 64) {p : Addr → Prop} (h : ∀ b, ¬p b) : cut m p = ∅ := by
  classical
  apply ExtHashMap.ext_getElem?; intro b
  rw [get?_cut]; simp only [h b, ↓reduceIte, ExtHashMap.getElem?_empty]

theorem get?_cut_of {m : Mem 64} {p : Addr → Prop} {b : Addr} (h : p b) : (cut m p)[b]? = m[b]? := by
  classical
  rw [get?_cut]; simp only [h, ↓reduceIte]

-- Two parts with disjoint address sets.
theorem sep_cut {P Q : MProp 64} {m : Mem 64} {R₁ R₂ R : Addr → Prop}
    (hP : P.get (cut m R₁)) (hQ : Q.get (cut m R₂))
    (hd : ∀ b, R₁ b → R₂ b → False) (he : ∀ b, R b ↔ R₁ b ∨ R₂ b) :
    (P ∗ Q).get (cut m R) := by
  classical
  rw [MProp.get_sep_apply_iff]
  refine ⟨cut m R₁, cut m R₂, ?_, ?_, hP, hQ⟩
  · rw [ExtHashMap.union_eq]; apply ExtHashMap.ext_getElem?; intro b
    rw [ExtHashMap.getElem?_union, get?_cut, get?_cut, get?_cut]
    by_cases h1 : R₁ b
    · have h2 : ¬R₂ b := fun h2 => hd b h1 h2
      have h3 : R b := (he b).mpr (Or.inl h1)
      simp [h1, h2, h3]
    · by_cases h2 : R₂ b
      · have h3 : R b := (he b).mpr (Or.inr h2)
        cases m[b]? <;> simp [h1, h2, h3]
      · have h3 : ¬R b := fun h3 => ((he b).mp h3).elim h1 h2
        simp [h1, h2, h3]
  · rw [ExtHashMap.inter_eq, ExtHashMap.eq_empty_iff_forall_not_mem]
    intro b hb
    rw [ExtHashMap.mem_inter_iff, mem_cut, mem_cut] at hb
    exact hd b hb.1.1 hb.2.1

-- The whole memory: a part and the frame of the rest.
theorem sep_cut_frame {P : MProp 64} {m : Mem 64} {R : Addr → Prop} (hP : P.get (cut m R)) :
    (P ∗ MProp.mk (Eq (cut m fun b => ¬R b))).get m := by
  have := sep_cut (Q := MProp.mk (Eq (cut m fun b => ¬R b))) (R₂ := fun b => ¬R b)
    (R := fun _ => True) hP (by rw [MProp.get_mk]) (fun b h1 h2 => h2 h1) (fun b => by simp [Classical.em])
  rwa [cut_univ m (fun _ => trivial)] at this

theorem emp_cut {m : Mem 64} {R : Addr → Prop} (h : ∀ b, ¬R b) : MProp.emp.get (cut m R) := by
  rw [MProp.get_emp_apply_iff, cut_none m h]

/-! ## Atoms -/

theorem AtM_cut {m : Mem 64} {a : Addr} {n : Nat} {bs : List UInt8}
    (hl : m.loadBytes a n = some bs) (hn : n ≤ 2 ^ 64) : (bs.AtM a).get (cut m (In a n)) := by
  classical
  have e := List.allSome_eq_map_some hl
  have hlen : bs.length = n := by simpa using (congrArg List.length e).symm
  have hb : ∀ i (hi : i < n), m[a + BitVec.ofNat 64 i]? = some (bs[i]'(hlen ▸ hi)) := by
    intro i hi
    have := congrArg (fun l => l[i]?) e
    simpa [List.getElem?_range hi, hi, hlen] using this
  simp only [List.AtM, MProp.get_mk]
  apply ExtHashMap.ext_getElem?; intro b
  rw [get?_At bs a b (hlen ▸ hn), get?_cut]
  by_cases h : In a n b
  · simp only [h, ↓reduceIte]
    unfold In at h
    have e2 : a + BitVec.ofNat 64 (b - a).toNat = b := by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
    rw [← e2, hb _ h, e2, List.getElem?_eq_getElem]
  · simp only [h, ↓reduceIte]
    unfold In at h
    exact List.getElem?_eq_none (by omega)

theorem loadBytes_of_isSome {m : Mem 64} {a : Addr} {n : Nat} (h : (m.loadInt a n).isSome) :
    ∃ bs, m.loadBytes a n = some bs ∧ m.loadInt a n = some (Int.ofBytes bs) := by
  unfold Mem.loadInt at h ⊢
  cases hl : m.loadBytes a n with
  | none => rw [hl] at h; simp at h
  | some bs => exact ⟨bs, rfl, rfl⟩

-- The `k` bytes at `a`, as `m` holds them.
theorem bytes_cut {m : Mem 64} {a : Addr} {k : Nat} (h : (m.loadInt a k).isSome)
    (hk : k ≤ 2 ^ 64) : ((Int.toBytes k (m.loadInt a k).get!).AtM a).get (cut m (In a k)) := by
  obtain ⟨bs, hl, hi⟩ := loadBytes_of_isSome h
  have hlen : bs.length = k := by
    have := congrArg List.length (List.allSome_eq_map_some hl); simpa using this.symm
  rw [hi, Option.get!_some, Int.toBytes_ofBytes k bs (by omega), List.take_of_length_le (by omega)]
  exact AtM_cut hl hk

-- The 2 and 4 bytes at `a` (`movw`, `movl`).
def rd16 (m : Mem 64) (a : Addr) : BitVec 16 := BitVec.ofInt 16 (m.loadInt a 2).get!
def rd32 (m : Mem 64) (a : Addr) : BitVec 32 := BitVec.ofInt 32 (m.loadInt a 4).get!

theorem Wd.cut {m : Mem 64} {a : Addr} (h : (m.loadInt a 8).isSome) :
    (Wd a (FlatShuffler.rd m a)).get (cut m (In a 8)) := by
  unfold Wd; rw [FlatShuffler.rd, toBytes_ofInt 8 64 rfl]; exact bytes_cut h (by decide)

theorem B8.cut {m : Mem 64} {a : Addr} (h : (m.loadInt a 1).isSome) :
    (B8 a (FlatShuffler.rdb m a)).get (cut m (In a 1)) := by
  unfold B8; rw [FlatShuffler.rdb, toBytes_ofInt 1 8 rfl]; exact bytes_cut h (by decide)

theorem B16.cut {m : Mem 64} {a : Addr} (h : (m.loadInt a 2).isSome) :
    (B16 a (rd16 m a)).get (cut m (In a 2)) := by
  unfold B16; rw [rd16, toBytes_ofInt 2 16 rfl]; exact bytes_cut h (by decide)

theorem B32.cut {m : Mem 64} {a : Addr} (h : (m.loadInt a 4).isSome) :
    (B32 a (rd32 m a)).get (cut m (In a 4)) := by
  unfold B32; rw [rd32, toBytes_ofInt 4 32 rfl]; exact bytes_cut h (by decide)

/-! ## Arrays and records -/

theorem addr_succ (a : Addr) (i : Nat) :
    a + BitVec.ofNat 64 (8 * (i + 1)) = a + 8#64 + BitVec.ofNat 64 (8 * i) := by
  rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp; omega

-- Two parts at `a` and at `a + k`.
theorem sep_in {P Q : MProp 64} {m : Mem 64} {a : Addr} {k l : Nat}
    (hP : P.get (cut m (In a k))) (hQ : Q.get (cut m (In (a + BitVec.ofNat 64 k) l)))
    (h : k + l ≤ 2 ^ 64) : (P ∗ Q).get (cut m (In a (k + l))) :=
  sep_cut hP hQ (fun _ h1 h2 => in_disj h h1 h2) (fun _ => in_split h)

theorem Arr.cut {m : Mem 64} : ∀ {a : Addr} (l : List Word), 8 * l.length ≤ 2 ^ 64 →
    (∀ i (hi : i < l.length), (m.loadInt (a + BitVec.ofNat 64 (8 * i)) 8).isSome ∧
      FlatShuffler.rd m (a + BitVec.ofNat 64 (8 * i)) = l[i]) →
    (Arr a l).get (Sep.cut m (In a (8 * l.length)))
  | a, [], _, _ => emp_cut fun b h => by unfold In at h; simp at h
  | a, v :: vs, hn, h => by
    simp only [Arr, List.length_cons] at hn ⊢
    have h0 := h 0 (by simp)
    simp only [Nat.mul_zero, BitVec.add_zero, List.getElem_cons_zero] at h0
    have hv : (Wd a v).get (Sep.cut m (In a 8)) := by rw [← h0.2]; exact Wd.cut h0.1
    have hvs := Arr.cut (a := a + 8#64) vs (by omega) fun i hi => by
      have := h (i + 1) (by simp; omega)
      rw [addr_succ] at this; simpa using this
    rw [show 8 * (vs.length + 1) = 8 + 8 * vs.length by omega]
    exact sep_in hv hvs (by omega)

-- The 12 bytes of a record, as `m` holds them.
def rdOp (m : Mem 64) (a : Addr) : OpR :=
  ⟨⟨FlatShuffler.rdb m a, FlatShuffler.rdb m (a + 1#64), ⟨rd32 m (a + 4#64), FlatShuffler.rdb m (a + 8#64), FlatShuffler.rdb m (a + 9#64)⟩⟩,
    rd16 m (a + 2#64), rd16 m (a + 10#64)⟩

-- The bytes of a load that succeeds are mapped.
theorem mapped_of_isSome {m : Mem 64} {a : Addr} {n : Nat} (h : (m.loadInt a n).isSome) :
    Mem.Mapped [(a, n)] m := fun x hx => by
  obtain ⟨bs, hl, -⟩ := loadBytes_of_isSome h
  have e := List.allSome_eq_map_some hl
  have hlen : bs.length = n := by simpa using (congrArg List.length e).symm
  simp only [Mem.Blocks.Inside, or_false] at hx
  have hi : (x - a).toNat < n := by omega
  have := congrArg (fun l => l[(x - a).toNat]?) e
  simp only [List.getElem?_map, List.getElem?_range hi, Option.map_some] at this
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, show a + (x - a) = x by bv_omega] at this
  rw [List.getElem?_eq_getElem (hlen ▸ hi), Option.map_some, Option.some_inj] at this
  rw [this]; rfl

-- Two parts at `a` and at `b = a + k`.
theorem sep_in' {P Q : MProp 64} {m : Mem 64} {a b : Addr} {k l : Nat}
    (hP : P.get (cut m (In a k))) (hQ : Q.get (cut m (In b l)))
    (hb : a + BitVec.ofNat 64 k = b) (h : k + l ≤ 2 ^ 64) : (P ∗ Q).get (cut m (In a (k + l))) :=
  sep_in hP (hb ▸ hQ) h

theorem OpM.cut {m : Mem 64} {a : Addr} (h : (m.loadInt a 12).isSome) :
    (OpM a (rdOp m a)).get (Sep.cut m (In a 12)) := by
  have hm := mapped_of_isSome h
  have ld : ∀ (o k : Nat), o + k ≤ 12 → (m.loadInt (a + BitVec.ofNat 64 o) k).isSome :=
    fun o k hk => hm.loadInt_isSome (Mem.Blocks.Inside.base_add (by simp; omega))
  have h0 := B8.cut (ld 0 1 (by omega))
  have h1 := B8.cut (ld 1 1 (by omega))
  have h2 := B16.cut (ld 2 2 (by omega))
  have h4 := B32.cut (ld 4 4 (by omega))
  have h8 := B8.cut (ld 8 1 (by omega))
  have h9 := B8.cut (ld 9 1 (by omega))
  have h10 := B16.cut (ld 10 2 (by omega))
  simp only [BitVec.add_zero] at h0
  have s9 := sep_in' h9 h10 (by bv_decide) (by decide)
  have s8 := sep_in' h8 s9 (by bv_decide) (by decide)
  have s4 := sep_in' h4 s8 (by bv_decide) (by decide)
  have s2 := sep_in' h2 s4 (by bv_decide) (by decide)
  have s1 := sep_in' h1 s2 (by bv_decide) (by decide)
  have s0 := sep_in' h0 s1 (by bv_decide) (by decide)
  exact s0

-- Two parts at `S + o` and at `S + o'`, `o' = o + k`.
theorem sep_rng {P Q : MProp 64} {m : Mem 64} {S : Addr} {o o' k l : Nat}
    (hP : P.get (Sep.cut m (Rng S o k))) (hQ : Q.get (Sep.cut m (Rng S o' l))) (ho : o + k = o') :
    (P ∗ Q).get (Sep.cut m (Rng S o (k + l))) := by
  subst ho; exact sep_cut hP hQ (fun _ h1 h2 => rng_disj h1 h2) (fun _ => rng_split)

theorem rng_of_in {P : MProp 64} {m : Mem 64} {S : Addr} {o k : Nat}
    (h : P.get (Sep.cut m (In (S + BitVec.ofNat 64 o) k))) (hk : o + k ≤ 2 ^ 64) :
    P.get (Sep.cut m (Rng S o k)) := by
  rwa [cut_congr m fun _ => in_ofNat hk] at h

theorem Ops.cut {m : Mem 64} {o : Addr} : ∀ (k : Nat) (rs : List OpR), 12 * (k + rs.length) ≤ 2 ^ 64 →
    (∀ i (hi : i < rs.length), (m.loadInt (opAt o (k + i)) 12).isSome ∧ rdOp m (opAt o (k + i)) = rs[i]) →
    (Ops o k rs).get (Sep.cut m (Rng o (12 * k) (12 * rs.length)))
  | k, [], _, _ => emp_cut fun b h => by unfold Rng at h; simp at h; omega
  | k, r :: rs, hn, h => by
    simp only [Ops, List.length_cons] at hn ⊢
    have h0 := h 0 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at h0
    have hr := rng_of_in (h0.2 ▸ OpM.cut h0.1) (by omega)
    have hrs := Ops.cut (k + 1) rs (by omega) fun i hi => by
      have := h (i + 1) (by simp; omega)
      rw [show k + (i + 1) = k + 1 + i by omega] at this; simpa using this
    rw [show 12 * (rs.length + 1) = 12 + 12 * rs.length by omega]
    exact sep_rng hr hrs (by omega)

theorem in_one {a b : Addr} : In a 1 b ↔ b = a := by
  unfold In
  constructor
  · intro h; have : b - a = 0#64 := by bv_omega
    bv_omega
  · rintro rfl; simp

theorem Spl.cut {m : Mem 64} {a : Addr} {f : BitVec 32 → BitVec 8} : ∀ (is : List Nat), is.Nodup →
    (∀ i ∈ is, i < 2 ^ 64 ∧ (m.loadInt (a + BitVec.ofNat 64 i) 1).isSome
      ∧ FlatShuffler.rdb m (a + BitVec.ofNat 64 i) = f (BitVec.ofNat 32 i)) →
    (Spl a f is).get (Sep.cut m fun b => ∃ i ∈ is, b = a + BitVec.ofNat 64 i)
  | [], _, _ => emp_cut fun b ⟨i, hi, _⟩ => by cases hi
  | i :: is, hnd, h => by
    simp only [Spl]
    have h0 := h i (List.mem_cons_self ..)
    have hi := h0.2.2 ▸ B8.cut h0.2.1
    have his := Spl.cut is (List.nodup_cons.mp hnd).2 fun j hj => h j (List.mem_cons_of_mem _ hj)
    refine sep_cut hi his (fun b h1 ⟨j, hj, e⟩ => ?_) (fun b => ?_)
    · rw [in_one] at h1
      have hji : j ≠ i := fun e' => (List.nodup_cons.mp hnd).1 (e' ▸ hj)
      have hj64 := (h j (List.mem_cons_of_mem _ hj)).1
      apply hji
      have : BitVec.ofNat 64 j = BitVec.ofNat 64 i := by have := h1.symm.trans e; bv_omega
      have := congrArg BitVec.toNat this
      simp only [BitVec.toNat_ofNat] at this
      rwa [Nat.mod_eq_of_lt hj64, Nat.mod_eq_of_lt h0.1] at this
    · rw [in_one]
      simp only [List.mem_cons, exists_eq_or_imp]

theorem Stk.cut {m : Mem 64} {sp : Addr} {fr : List Word} (hn : 8 * fr.length + 8 ≤ 2 ^ 64)
    (hf : ∀ i (hi : i < fr.length),
      (m.loadInt (sp - 8#64 - BitVec.ofNat 64 (8 * fr.length) + BitVec.ofNat 64 (8 * i)) 8).isSome ∧
      FlatShuffler.rd m (sp - 8#64 - BitVec.ofNat 64 (8 * fr.length) + BitVec.ofNat 64 (8 * i)) = fr[i])
    (hv : (m.loadInt (sp - 8#64) 8).isSome) :
    (Stk sp fr (FlatShuffler.rd m (sp - 8#64))).get
      (Sep.cut m (In (sp - 8#64 - BitVec.ofNat 64 (8 * fr.length)) (8 * fr.length + 8))) :=
  sep_in' (Arr.cut fr (by omega) hf) (Wd.cut hv) (BitVec.sub_add_cancel _ _) hn

-- A word at offset `o` of a mapped block of `N` bytes.
theorem Wd.cut_rng {m : Mem 64} {S : Addr} {o N : Nat} {v : Word} (hm : Mem.Mapped [(S, N)] m)
    (ho : o + 8 ≤ N) (hv : FlatShuffler.rd m (S + BitVec.ofNat 64 o) = v) (hN : N ≤ 2 ^ 64 := by decide) :
    (Wd (S + BitVec.ofNat 64 o) v).get (Sep.cut m (Rng S o 8)) :=
  rng_of_in (hv ▸ Wd.cut (hm.loadInt_isSome (Mem.Blocks.Inside.base_add (by
    simp; omega)))) (by omega)

-- An array at offset `o` of a mapped block of `N` bytes.
theorem Arr.cut_rng {m : Mem 64} {S : Addr} {o N : Nat} {vs : Vector Word MAX_N}
    (hm : Mem.Mapped [(S, N)] m) (ho : o + 8 * MAX_N ≤ N)
    (hv : ∀ i (hi : i < MAX_N), FlatShuffler.rd m (S + BitVec.ofNat 64 o + BitVec.ofNat 64 (8 * i)) = vs[i])
    (hN : N ≤ 2 ^ 64 := by decide) :
    (Arr (S + BitVec.ofNat 64 o) vs.toList).get (Sep.cut m (Rng S o (8 * MAX_N))) := by
  have := Arr.cut (m := m) (a := S + BitVec.ofNat 64 o) vs.toList (by rw [Vector.length_toList]; decide) fun i hi => by
    simp only [Vector.length_toList] at hi
    refine ⟨hm.loadInt_isSome (Mem.Blocks.Inside.base_add_add ?_), by simpa using hv i hi⟩
    simp only [MAX_N] at ho hi ⊢; simp; omega
  simp only [Vector.length_toList] at this
  exact rng_of_in this (by simp only [MAX_N] at ho ⊢; omega)

theorem Em.cut {m : Mem 64} {S : Addr} {h : Hdr} (hm : Mem.Mapped [(S, EmSize)] m)
    (h0 : FlatShuffler.rd m (Fld.target S) = h.tgt) (h1 : FlatShuffler.rd m (Fld.targetSize S) = h.n)
    (h2 : FlatShuffler.rd m (Fld.spills S) = h.spl) (h3 : FlatShuffler.rd m (Fld.stack_data S) = h.data)
    (h4 : FlatShuffler.rd m (Fld.stack_size S) = h.len) (h5 : FlatShuffler.rd m (Fld.stack_trace S) = h.ops)
    (h6 : FlatShuffler.rd m (Fld.stack_traceSize S) = h.nops)
    (hd : ∀ i (hi : i < MAX_N), FlatShuffler.rd m (Fld.mapping_destinationOf S i) = h.dest[i])
    (hp : ∀ i (hi : i < MAX_N), FlatShuffler.rd m (Fld.mapping_positionOf S i) = h.pos[i])
    (h9 : FlatShuffler.rd m (Fld.pendingGenerations S) = h.pend)
    (h10 : FlatShuffler.rd m (Fld.blocked_offset S) = h.blkOff)
    (h11 : FlatShuffler.rd m (Fld.blocked_excess S) = h.blkExc) :
    (Em S h).get (Sep.cut m (In S EmSize)) := by
  rw [Fld.eq_target] at h0
  have w0 := Wd.cut_rng (o := 0) hm (by decide) h0
  have w1 := Wd.cut_rng (o := 8) hm (by decide) h1
  have w2 := Wd.cut_rng (o := 16) hm (by decide) h2
  have w3 := Wd.cut_rng (o := 24) hm (by decide) h3
  have w4 := Wd.cut_rng (o := 32) hm (by decide) h4
  have w5 := Wd.cut_rng (o := 40) hm (by decide) h5
  have w6 := Wd.cut_rng (o := 48) hm (by decide) h6
  have w7 := Arr.cut_rng (o := 56) (vs := h.dest) hm (by decide) hd
  have w8 := Arr.cut_rng (o := 8248) (vs := h.pos) hm (by decide) hp
  have w9 := Wd.cut_rng (o := 16440) hm (by decide) h9
  have w10 := Wd.cut_rng (o := 16448) hm (by decide) h10
  have w11 := Wd.cut_rng (o := 16456) hm (by decide) h11
  have s := sep_rng w0 (sep_rng w1 (sep_rng w2 (sep_rng w3 (sep_rng w4 (sep_rng w5 (sep_rng w6
    (sep_rng w7 (sep_rng w8 (sep_rng w9 (sep_rng w10 w11 rfl) rfl) rfl) rfl) rfl) rfl) rfl) rfl)
    rfl) rfl) rfl
  rw [← Fld.eq_target] at s
  rw [cut_congr m fun _ => in_iff_rng]
  exact s

/-! ## The addresses of an assertion -/

-- Each memory of `P` has the addresses in `D`, and no other address.
def Own (P : MProp 64) (D : Addr → Prop) : Prop := ∀ m, P.get m → ∀ b, b ∈ m ↔ D b

-- `P` holds on at most one memory.
def Single (P : MProp 64) : Prop := ∀ m₁ m₂, P.get m₁ → P.get m₂ → m₁ = m₂

section
variable {P Q : MProp 64} {D D₁ D₂ : Addr → Prop}

theorem Own.congr (h : Own P D₁) (e : ∀ b, D₁ b ↔ D₂ b) : Own P D₂ :=
  fun m hm b => (h m hm b).trans (e b)

theorem Own.emp : Own MProp.emp fun _ => False := fun m hm b => by
  rw [MProp.get_emp_apply_iff] at hm; subst hm; simp

theorem Own.sep (h1 : Own P D₁) (h2 : Own Q D₂) : Own (P ∗ Q) fun b => D₁ b ∨ D₂ b := by
  intro m hm b
  obtain ⟨m₁, m₂, hu, -, hp, hq⟩ := (MProp.get_sep_apply_iff P Q m).mp hm
  rw [← hu, ExtHashMap.union_eq, ExtHashMap.mem_union_iff, h1 m₁ hp, h2 m₂ hq]

theorem Single.mk (m₀ : Mem 64) : Single (MProp.mk (Eq m₀)) := fun _ _ h1 h2 => by
  rw [MProp.get_mk] at h1 h2; rw [← h1, ← h2]

theorem Single.emp : Single MProp.emp := fun _ _ h1 h2 => by
  rw [MProp.get_emp_apply_iff] at h1 h2; rw [h1, h2]

theorem Single.sep (h1 : Single P) (h2 : Single Q) : Single (P ∗ Q) := by
  intro m m' hm hm'
  obtain ⟨a, b, hu, -, hp, hq⟩ := (MProp.get_sep_apply_iff P Q m).mp hm
  obtain ⟨a', b', hu', -, hp', hq'⟩ := (MProp.get_sep_apply_iff P Q m').mp hm'
  rw [← hu, ← hu', h1 a a' hp hp', h2 b b' hq hq']

end

theorem Own.atM (bs : List UInt8) (a : Addr) (h : bs.length ≤ 2 ^ 64) :
    Own (bs.AtM a) (In a bs.length) := by
  intro m hm b
  simp only [List.AtM, MProp.get_mk] at hm
  subst hm
  rw [mem_At_iff]
  unfold In
  constructor
  · rintro ⟨i, hi, rfl⟩
    rw [BitVec.add_comm a, BitVec.add_sub_cancel, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact hi
  · intro hb
    refine ⟨(b - a).toNat, hb, ?_⟩
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]

theorem Single.atM (bs : List UInt8) (a : Addr) : Single (bs.AtM a) := Single.mk _

theorem Wd.own (a : Addr) (v : Word) : Own (Wd a v) (In a 8) := by
  unfold Wd; exact Int.toBytes_length 8 _ ▸ Own.atM _ a (by simp [Int.toBytes_length])
theorem B8.own (a : Addr) (v : BitVec 8) : Own (B8 a v) (In a 1) := by
  unfold B8; exact Int.toBytes_length 1 _ ▸ Own.atM _ a (by simp [Int.toBytes_length])
theorem B16.own (a : Addr) (v : BitVec 16) : Own (B16 a v) (In a 2) := by
  unfold B16; exact Int.toBytes_length 2 _ ▸ Own.atM _ a (by simp [Int.toBytes_length])
theorem B32.own (a : Addr) (v : BitVec 32) : Own (B32 a v) (In a 4) := by
  unfold B32; exact Int.toBytes_length 4 _ ▸ Own.atM _ a (by simp [Int.toBytes_length])

theorem Wd.single (a : Addr) (v : Word) : Single (Wd a v) := by unfold Wd; exact Single.atM _ _
theorem B8.single (a : Addr) (v : BitVec 8) : Single (B8 a v) := by unfold B8; exact Single.atM _ _
theorem B16.single (a : Addr) (v : BitVec 16) : Single (B16 a v) := by
  unfold B16; exact Single.atM _ _
theorem B32.single (a : Addr) (v : BitVec 32) : Single (B32 a v) := by
  unfold B32; exact Single.atM _ _

-- Two assertions at `a` and at `b = a + k`.
theorem Own.sep_in {P Q : MProp 64} {a b : Addr} {k l : Nat} (hP : Own P (In a k))
    (hQ : Own Q (In b l)) (hb : a + BitVec.ofNat 64 k = b) (h : k + l ≤ 2 ^ 64) :
    Own (P ∗ Q) (In a (k + l)) := by
  subst hb; exact (hP.sep hQ).congr fun _ => (in_split h).symm

-- Two assertions at `S + o` and at `S + o'`, `o' = o + k`.
theorem Own.sep_rng {P Q : MProp 64} {S : Addr} {o o' k l : Nat} (hP : Own P (Rng S o k))
    (hQ : Own Q (Rng S o' l)) (ho : o + k = o') : Own (P ∗ Q) (Rng S o (k + l)) := by
  subst ho; exact (hP.sep hQ).congr fun _ => rng_split.symm

theorem Arr.own : ∀ (a : Addr) (l : List Word), 8 * l.length ≤ 2 ^ 64 → Own (Arr a l) (In a (8 * l.length))
  | a, [], _ => Own.emp.congr fun b => by unfold In; simp
  | a, v :: vs, hn => by
    simp only [Arr, List.length_cons] at hn ⊢
    rw [show 8 * (vs.length + 1) = 8 + 8 * vs.length by omega]
    exact (Wd.own a v).sep_in (Arr.own (a + 8#64) vs (by omega)) rfl (by omega)

theorem Arr.single : ∀ (a : Addr) (l : List Word), Single (Arr a l)
  | _, [] => Single.emp
  | a, v :: vs => (Wd.single a v).sep (Arr.single (a + 8#64) vs)

theorem OpM.own (a : Addr) (r : OpR) : Own (OpM a r) (In a 12) := by
  unfold OpM
  have s9 := (B8.own (a + 9#64) r.op.slot.valueOpcode).sep_in (B16.own (a + 10#64) r.pad10)
    (by bv_decide) (by decide)
  have s8 := (B8.own (a + 8#64) r.op.slot.kind).sep_in s9 (by bv_decide) (by decide)
  have s4 := (B32.own (a + 4#64) r.op.slot.payload).sep_in s8 (by bv_decide) (by decide)
  have s2 := (B16.own (a + 2#64) r.pad2).sep_in s4 (by bv_decide) (by decide)
  have s1 := (B8.own (a + 1#64) r.op.depth).sep_in s2 (by bv_decide) (by decide)
  have s0 := (B8.own a r.op.kind).sep_in s1 (by bv_decide) (by decide)
  simpa using s0

theorem OpM.single (a : Addr) (r : OpR) : Single (OpM a r) := by
  unfold OpM
  exact (B8.single _ _).sep <| (B8.single _ _).sep <| (B16.single _ _).sep <| (B32.single _ _).sep <|
    (B8.single _ _).sep <| (B8.single _ _).sep (B16.single _ _)

theorem Ops.own {o : Addr} : ∀ (k : Nat) (rs : List OpR), 12 * (k + rs.length) ≤ 2 ^ 64 →
    Own (Ops o k rs) (Rng o (12 * k) (12 * rs.length))
  | k, [], _ => Own.emp.congr fun b => by unfold Rng; simp
  | k, r :: rs, hn => by
    simp only [Ops, List.length_cons] at hn ⊢
    rw [show 12 * (rs.length + 1) = 12 + 12 * rs.length by omega]
    refine Own.sep_rng ((OpM.own _ r).congr fun _ => in_ofNat (by omega)) (Ops.own (k + 1) rs (by omega)) (by omega)

theorem Ops.single (o : Addr) : ∀ (k : Nat) (rs : List OpR), Single (Ops o k rs)
  | _, [] => Single.emp
  | k, r :: rs => (OpM.single _ r).sep (Ops.single o (k + 1) rs)

theorem Spl.own (a : Addr) (f : BitVec 32 → BitVec 8) :
    ∀ is : List Nat, Own (Spl a f is) fun b => ∃ i ∈ is, b = a + BitVec.ofNat 64 i
  | [] => Own.emp.congr fun b => by simp
  | i :: is => ((B8.own _ _).sep (Spl.own a f is)).congr fun b => by
    rw [in_one]; simp only [List.mem_cons, exists_eq_or_imp]

theorem Spl.single (a : Addr) (f : BitVec 32 → BitVec 8) : ∀ is : List Nat, Single (Spl a f is)
  | [] => Single.emp
  | _ :: is => (B8.single _ _).sep (Spl.single a f is)

theorem Stk.own (sp : Addr) (fr : List Word) (v : Word) (hn : 8 * fr.length + 8 ≤ 2 ^ 64) :
    Own (Stk sp fr v) (In (sp - 8#64 - BitVec.ofNat 64 (8 * fr.length)) (8 * fr.length + 8)) :=
  (Arr.own _ fr (by omega)).sep_in (Wd.own _ v) (BitVec.sub_add_cancel _ _) hn

theorem Stk.single (sp : Addr) (fr : List Word) (v : Word) : Single (Stk sp fr v) :=
  (Arr.single _ fr).sep (Wd.single _ v)

theorem Wd.own_rng (S : Addr) {o : Nat} (v : Word) (ho : o + 8 ≤ 2 ^ 64) :
    Own (Wd (S + BitVec.ofNat 64 o) v) (Rng S o 8) :=
  (Wd.own _ v).congr fun _ => in_ofNat ho

theorem Arr.own_rng (S : Addr) {o : Nat} (vs : Vector Word MAX_N) (ho : o + 8 * MAX_N ≤ 2 ^ 64) :
    Own (Arr (S + BitVec.ofNat 64 o) vs.toList) (Rng S o (8 * MAX_N)) := by
  have := Arr.own (S + BitVec.ofNat 64 o) vs.toList (by rw [Vector.length_toList]; decide)
  rw [Vector.length_toList] at this
  exact this.congr fun _ => in_ofNat ho

theorem Em.own (S : Addr) (h : Hdr) : Own (Em S h) (In S EmSize) := by
  unfold Em
  have w0 := Wd.own_rng S (o := 0) h.tgt (by decide)
  rw [← Fld.eq_target] at w0
  have s := w0.sep_rng ((Wd.own_rng S (o := 8) h.n (by decide)).sep_rng
    ((Wd.own_rng S (o := 16) h.spl (by decide)).sep_rng
    ((Wd.own_rng S (o := 24) h.data (by decide)).sep_rng
    ((Wd.own_rng S (o := 32) h.len (by decide)).sep_rng
    ((Wd.own_rng S (o := 40) h.ops (by decide)).sep_rng
    ((Wd.own_rng S (o := 48) h.nops (by decide)).sep_rng
    ((Arr.own_rng S (o := 56) h.dest (by decide)).sep_rng
    ((Arr.own_rng S (o := 8248) h.pos (by decide)).sep_rng
    ((Wd.own_rng S (o := 16440) h.pend (by decide)).sep_rng
    ((Wd.own_rng S (o := 16448) h.blkOff (by decide)).sep_rng
    (Wd.own_rng S (o := 16456) h.blkExc (by decide)) rfl) rfl) rfl) rfl) rfl) rfl) rfl) rfl) rfl)
    rfl) rfl
  exact s.congr fun _ => in_iff_rng.symm

theorem Em.single (S : Addr) (h : Hdr) : Single (Em S h) := by
  unfold Em
  exact (Wd.single _ _).sep <| (Wd.single _ _).sep <| (Wd.single _ _).sep <| (Wd.single _ _).sep <|
    (Wd.single _ _).sep <| (Wd.single _ _).sep <| (Wd.single _ _).sep <| (Arr.single _ _).sep <|
    (Arr.single _ _).sep <| (Wd.single _ _).sep <| (Wd.single _ _).sep (Wd.single _ _)

/-! ## The bytes that an assertion does not own -/

section
variable {A A' B : MProp 64} {D : Addr → Prop} {m m' mB : Mem 64} {b : Addr}

-- A byte outside `D` is the byte of the rest.
theorem get?_rest (h : (A ∗ B).get m) (hA : Own A D) (hB : ∀ m', B.get m' → m' = mB) (hb : ¬D b) :
    m[b]? = mB[b]? := by
  obtain ⟨m₁, m₂, hu, -, hp, hq⟩ := (MProp.get_sep_apply_iff A B m).mp h
  have h1 : m₁[b]? = none := ExtHashMap.getElem?_eq_none fun hm => hb ((hA m₁ hp b).mp hm)
  rw [← hu, ExtHashMap.union_eq, ExtHashMap.getElem?_union, h1, hB m₂ hq, Option.or_none]

theorem get?_mk (h : (A ∗ MProp.mk (Eq mB)).get m) (hA : Own A D) (hb : ¬D b) : m[b]? = mB[b]? :=
  get?_rest h hA (fun _ h => (MProp.get_mk _ ▸ h).symm) hb

-- A call that keeps the rest `B` keeps the bytes outside `D`.
theorem get?_call (h : (A ∗ B).get m) (h' : (A' ∗ B).get m') (hA : Own A D) (hA' : Own A' D)
    (hB : Single B) (hb : ¬D b) : m'[b]? = m[b]? := by
  obtain ⟨m₁, m₂, -, -, -, hq⟩ := (MProp.get_sep_apply_iff A B m).mp h
  rw [get?_rest h hA (fun m' h => hB _ _ h hq) hb, get?_rest h' hA' (fun m' h => hB _ _ h hq) hb]

-- A byte in `D` is in the memory.
theorem mem_own (h : (A ∗ B).get m) (hA : Own A D) (hb : D b) : b ∈ m := by
  obtain ⟨m₁, m₂, hu, -, hp, -⟩ := (MProp.get_sep_apply_iff A B m).mp h
  rw [← hu, ExtHashMap.union_eq, ExtHashMap.mem_union_iff]
  exact Or.inl ((hA m₁ hp b).mpr hb)

end

end FlatShuffler.Sep
