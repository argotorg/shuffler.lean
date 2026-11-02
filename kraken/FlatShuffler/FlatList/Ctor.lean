module

public import FlatShuffler.FlatList.Basic
import all FlatShuffler.FlatList.Basic

@[expose] public section

/-!
The constructor of the flat model against `init` of the list model: the state of `ctor` holds
the initial state of the list model (`sim_ctor`).
-/

namespace FlatShuffler.Flat

/-! ## The three loops of the constructor -/

def clearF (st : St) (d : Word) : St := { st with pos := put st.pos d NONE }

def bindF (dests : Vector Word maxStackSize) (st : St) (p : Word) : St := bind st p (get dests p)

def countF (st : St) (d : Word) : St :=
  if get st.pos d = NONE then { st with pend := st.pend + 1 } else st

def ctor0 (data : Vector StackSlot maxStackSize) (m : Word) (target : Vector StackSlot maxStackSize) (n : Word)
    (spills : BitVec 32 → BitVec 8) (u : Uninit) : St :=
  { target, targetSize := n, spills, data, size := m, trace := [],
    dest := u.dest, pos := u.pos, pend := 0,
    blockedOffset := u.blockedOffset, blockedExcess := u.blockedExcess }

theorem ctor_eq (data : Vector StackSlot maxStackSize) (m : Word) (target : Vector StackSlot maxStackSize)
    (n : Word) (dests : Vector Word maxStackSize) (spills : BitVec 32 → BitVec 8) (u : Uninit) :
    ctor data m target n dests spills u = (offsets n).foldl countF ((offsets m).foldl (bindF dests)
      ((offsets n).foldl clearF (ctor0 data m target n spills u))) := rfl

/-! ## Loops over the offsets -/

def ofs (k : Nat) : List Word := (List.range k).map (BitVec.ofNat 64)

theorem offsets_eq (k : Word) : offsets k = ofs k.toNat := rfl

theorem foldl_ofs_succ {α : Type} (f : α → Word → α) (a : α) (k : Nat) :
    (ofs (k + 1)).foldl f a = f ((ofs k).foldl f a) (BitVec.ofNat 64 k) := by
  simp [ofs, List.range_succ]

theorem MAX_N_eq : maxStackSize = 1024 := rfl

theorem toNat_ofNat_small {k : Nat} (hk : k < maxStackSize) : (BitVec.ofNat 64 k).toNat = k :=
  toNat_ofNat_of_lt (by rw [MAX_N_eq] at hk; omega)


-- An offset below `k + 1` that is not `k` is below `k`.
theorem lt_of_ne_ofNat {d : Word} {k : Nat} (hk : k < maxStackSize) (hd : d.toNat < k + 1)
    (h : d ≠ BitVec.ofNat 64 k) : d.toNat < k := by
  have : d.toNat ≠ k := fun he => h (eq_of_toNat (by rw [toNat_ofNat_small hk]; exact he))
  omega

-- A loop keeps each projection `g` that each of its steps keeps.
theorem proj_foldl {α β γ : Type} (g : α → γ) {f : α → β → α} (hf : ∀ a b, g (f a b) = g a)
    (l : List β) (a : α) : g (l.foldl f a) = g a := by
  induction l generalizing a with
  | nil => rfl
  | cons b l ih => rw [List.foldl_cons, ih, hf]

-- The members that the three loops do not write.
def frame (st : St) :=
  (st.target, st.targetSize, st.spills, st.data, st.size, st.trace, st.blockedOffset,
    st.blockedExcess)

/-! ## The first loop: no destination has a position -/

theorem clear_pos (st : St) {k : Nat} (hk : k ≤ maxStackSize) {d : Word} (hd : d.toNat < k) :
    get ((ofs k).foldl clearF st).pos d = NONE := by
  induction k with
  | zero => omega
  | succ k ih =>
    rw [foldl_ofs_succ]
    show get (put _ _ NONE) d = NONE
    by_cases h : d = BitVec.ofNat 64 k
    · subst h; exact get_put_self _ _ (by rw [toNat_ofNat_small (by omega)]; omega)
    · rw [get_put_ne _ _ h]; exact ih (by omega) (lt_of_ne_ofNat (by omega) hd h)

/-! ## The second loop: each source slot is bound for its destination -/

theorem listDests_length {M : Nat} (dest : Vector Word maxStackSize) (hM : M ≤ maxStackSize) :
    (listDests M dest).length = M := by
  simp [listDests]; omega

theorem listDests_get {M : Nat} {dest : Vector Word maxStackSize} (hM : M ≤ maxStackSize) {i : Nat}
    (hi : i < M) : (listDests M dest)[i]! = (get dest (BitVec.ofNat 64 i)).toNat := by
  rw [getElem!_pos _ _ (by rw [listDests_length dest hM]; exact hi)]
  simp [listDests, get, toNat_ofNat_small (show i < maxStackSize by omega), show i < maxStackSize by omega]

-- The positions after `k` steps of `initPositionOf`.
def initPos (n : Nat) (dests : List Nat) (k : Nat) : List (Option Nat) :=
  (List.range k).foldl (fun p i => p.set dests[i]! (some i)) (List.replicate n none)

theorem initPos_succ (n : Nat) (dests : List Nat) (k : Nat) :
    initPos n dests (k + 1) = (initPos n dests k).set dests[k]! (some k) := by
  simp [initPos, List.range_succ]

theorem initPos_length (n : Nat) (dests : List Nat) (k : Nat) : (initPos n dests k).length = n := by
  induction k with
  | zero => simp [initPos]
  | succ k ih => rw [initPos_succ, List.length_set, ih]

theorem bind_loop {n M : Nat} (hn : n ≤ maxStackSize) (hM : M ≤ n) {dest : Vector Word maxStackSize}
    (hd : Dests n (listDests M dest)) (st : St)
    (h0 : ∀ d : Word, d.toNat < n → get st.pos d = NONE) {k : Nat} (hk : k ≤ M) :
    (∀ i : Word, i.toNat < k → get ((ofs k).foldl (bindF dest) st).dest i = get dest i) ∧
    (∀ d : Word, d.toNat < n → get ((ofs k).foldl (bindF dest) st).pos d =
      optW ((initPos n (listDests M dest) k)[d.toNat]?.join)) := by
  induction k with
  | zero =>
    refine ⟨fun i hi => by omega, fun d hd' => ?_⟩
    show get st.pos d = _
    rw [h0 d hd']
    simp [initPos, hd']
    rfl
  | succ k ih =>
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    have hkM : k < maxStackSize := by omega
    have hx := hd.1 k (by rw [listDests_length dest (by omega)]; omega)
    rw [← getElem!_pos, listDests_get (by omega) (by omega)] at hx
    rw [foldl_ofs_succ]
    refine ⟨fun i hi => ?_, fun d hd' => ?_⟩
    · show get (put _ _ _) i = _
      by_cases h : i = BitVec.ofNat 64 k
      · subst h; exact get_put_self _ _ (by rw [toNat_ofNat_small hkM]; omega)
      · rw [get_put_ne _ _ h]; exact ih1 i (lt_of_ne_ofNat hkM hi h)
    · show get (put _ _ _) d = _
      rw [initPos_succ, listDests_get (by omega) (by omega)]
      by_cases h : d = get dest (BitVec.ofNat 64 k)
      · subst h
        rw [get_put_self _ _ (by omega), List.getElem?_set_self (by rw [initPos_length]; exact hx)]
        rfl
      · rw [get_put_ne _ _ h, List.getElem?_set_ne (toNat_ne_of_ne h).symm]
        exact ih2 d hd'

/-! ## The third loop: the count of the destinations without a position -/

theorem count_loop (st : St) (h0 : st.pend = 0) {k : Nat} (hk : k ≤ maxStackSize) :
    ((ofs k).foldl countF st).pos = st.pos ∧ ((ofs k).foldl countF st).dest = st.dest ∧
    ((ofs k).foldl countF st).pend.toNat =
      (List.range k).countP (fun d => get st.pos (BitVec.ofNat 64 d) == NONE) := by
  induction k with
  | zero => simp [ofs, h0]
  | succ k ih =>
    obtain ⟨ih1, ih2, ih3⟩ := ih (by omega)
    have hc := List.countP_le_length (p := fun d => get st.pos (BitVec.ofNat 64 d) == NONE)
      (l := List.range k)
    rw [List.length_range] at hc
    rw [foldl_ofs_succ, List.range_succ, List.countP_append]
    generalize (ofs k).foldl countF st = s at ih1 ih2 ih3
    unfold countF
    split
    · rename_i h
      rw [ih1] at h
      refine ⟨ih1, ih2, ?_⟩
      simp only [List.countP_singleton, h, beq_self_eq_true, ite_true]
      rw [MAX_N_eq] at hk
      rw [BitVec.toNat_add, ih3]
      simp
      omega
    · rename_i h
      rw [ih1] at h
      refine ⟨ih1, ih2, ?_⟩
      simp [h, ih3]

/-! ## The constructor -/

theorem listEnv_n {n : Nat} (target : Vector StackSlot maxStackSize) (spills : BitVec 32 → BitVec 8)
    (hn : n ≤ maxStackSize) : (listEnv n target spills).n = n := by
  simp [listEnv, Env.n]; omega

theorem listSource_length {M : Nat} (data : Vector StackSlot maxStackSize) (hM : M ≤ maxStackSize) :
    (listSource M data).length = M := by
  simp [listSource]; omega

theorem init_len {e : Env} {source : List StackSlot} {dests : List Nat}
    (hl : source.length = dests.length) : (init e source dests).len = source.length := by
  simp [init, St.len, hl]

theorem init_val {e : Env} {source : List StackSlot} {dests : List Nat}
    (hl : source.length = dests.length) {i : Nat} (hi : i < source.length) :
    (init e source dests).val i = source[i] := by
  simp [St.val, init, List.getElem?_zipWith, hi, hl ▸ hi]

theorem sim_ctor {m n : Word} {data target : Vector StackSlot maxStackSize} {dest : Vector Word maxStackSize}
    {spilled : BitVec 32 → BitVec 8} (u : Uninit) (hm : m ≤ n) (hn : n.toNat ≤ maxStackSize)
    (hd : Dests n.toNat (listDests m.toNat dest)) :
    Sim (listEnv n.toNat target spilled) (ctor data m target n dest spilled u)
      (init (listEnv n.toNat target spilled) (listSource m.toNat data) (listDests m.toNat dest)) := by
  have hmn : m.toNat ≤ n.toNat := hm
  have hM : m.toNat ≤ maxStackSize := by omega
  have hen := listEnv_n target spilled hn
  have hl : (listSource m.toNat data).length = (listDests m.toNat dest).length := by
    rw [listSource_length data hM, listDests_length dest hM]
  have hd' : Dests (listEnv n.toNat target spilled).n (listDests m.toNat dest) := by
    rw [hen]; exact hd
  have hp := Pos_init hl hd'
  rw [hen] at hp
  have hds : (init (listEnv n.toNat target spilled) (listSource m.toNat data)
      (listDests m.toNat dest)).dests = listDests m.toNat dest := map_dest_zipWith _ _ hl
  have hlen := init_len (e := listEnv n.toNat target spilled) hl
  rw [listSource_length data hM] at hlen
  rw [ctor_eq, offsets_eq, offsets_eq]
  generalize hs0 : ctor0 data m target n spilled u = s0
  generalize hs1 : (ofs n.toNat).foldl clearF s0 = s1
  generalize hs2 : (ofs m.toNat).foldl (bindF dest) s1 = s2
  have hf1 : frame s1 = frame s0 := hs1 ▸ proj_foldl frame (f := clearF) (fun _ _ => rfl) _ _
  have hf2 : frame s2 = frame s1 := hs2 ▸ proj_foldl frame (f := bindF dest) (fun _ _ => rfl) _ _
  have hf3 : frame ((ofs n.toNat).foldl countF s2) = frame s2 :=
    proj_foldl frame (f := countF) (fun _ _ => by unfold countF; split <;> rfl) _ _
  have hp1 : ∀ d : Word, d.toNat < n.toNat → get s1.pos d = NONE :=
    fun d h => hs1 ▸ clear_pos s0 hn h
  obtain ⟨hb1, hb2⟩ := hs2 ▸ bind_loop hn hmn hd s1 hp1 (Nat.le_refl _)
  have hpend : s2.pend = 0 := by
    rw [← hs2, proj_foldl St.pend (f := bindF dest) (fun _ _ => rfl), ← hs1,
      proj_foldl St.pend (f := clearF) (fun _ _ => rfl), ← hs0]
    rfl
  have hpos2 : ∀ d : Word, d.toNat < n.toNat → get s2.pos d = optW (positionOf
      (init (listEnv n.toNat target spilled) (listSource m.toNat data) (listDests m.toNat dest))
      d.toNat) := by
    intro d hd
    rw [hb2 d hd]
    show _ = optW ((initPositionOf _ _)[d.toNat]?.join)
    rw [hen, initPositionOf, listDests_length dest hM]
    rfl
  have hF : frame ((ofs n.toNat).foldl countF s2) = frame (ctor0 data m target n spilled u) := by
    rw [hf3, hf2, hf1, hs0]
  simp only [frame, ctor0, Prod.mk.injEq] at hF
  obtain ⟨hT, hN, hSp, hD, hSz, hTr, -, -⟩ := hF
  obtain ⟨hc1, hc2, hc3⟩ := count_loop s2 hpend hn
  generalize (ofs n.toNat).foldl countF s2 = s3 at hT hN hSp hD hSz hTr hc1 hc2 hc3
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hT, hN, hSp]
  · rw [hN]; exact hn
  · rw [hSz, hlen]
  · rw [hN, hlen]; exact hmn
  · intro i hi
    rw [hlen] at hi
    rw [hD, init_val hl (by rw [listSource_length data hM]; exact hi)]
    simp [listSource, get, show i.toNat < maxStackSize by omega]
  · intro i hi
    rw [hlen] at hi
    rw [hc2, hb1 i hi, St.dest_eq, hds, listDests_get hM hi]
    simp [BitVec.ofNat_toNat]
  · intro d hd
    rw [hN] at hd
    rw [hc1, hpos2 d hd]
  · rw [hc3]
    show _ = (List.range (listEnv n.toNat target spilled).n).countP fun d => (positionOf (init
      (listEnv n.toNat target spilled) (listSource m.toNat data) (listDests m.toNat dest)) d).isNone
    rw [hen]
    refine List.countP_congr fun x hx => ?_
    rw [List.mem_range] at hx
    have hxw : (BitVec.ofNat 64 x).toNat = x := toNat_ofNat_small (by omega)
    rw [hpos2 _ (by rw [hxw]; exact hx), hxw]
    cases h : positionOf (init (listEnv n.toNat target spilled) (listSource m.toNat data)
      (listDests m.toNat dest)) x with
    | none => simp [optW]
    | some i =>
      obtain ⟨hi, -⟩ := (hp.iff x i).mp h
      rw [hds, listDests_length dest hM] at hi
      have hne : BitVec.ofNat 64 i ≠ NONE :=
        ne_NONE (by rw [toNat_ofNat_small (by omega)]; rw [MAX_N_eq] at hM; omega)
      simp [optW, hne]
  · rw [hTr]; rfl
  · rw [hN]; exact hp

end FlatShuffler.Flat
