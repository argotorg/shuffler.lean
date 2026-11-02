module

public import FlatShuffler.Unit.Plan.PlannerRunInitDefs
import all FlatShuffler.Unit.Plan.PlannerRunInitDefs
public import FlatShuffler.Unit.Plan.PlannerRunMapping
import all FlatShuffler.Unit.Plan.PlannerRunMapping

@[expose] public section

namespace FlatShuffler.Unit.PlannerRunU
open FlatShuffler.Sep Flat

def localMapping (locals : List Word) (hl : locals.length = 4121) : Flat.Mapping where
  dest := ⟨((locals.drop 12).take 1024).toArray, by simp [hl, MAX_N]⟩
  pos := ⟨((locals.drop 1036).take 1024).toArray, by simp [hl, MAX_N]⟩

theorem local_partition (locals : List Word) :
    locals = locals.take 12 ++ (locals.drop 12).take 1024 ++
      (locals.drop 1036).take 1024 ++ locals.drop 2060 := by
  have h1 : (locals.drop 12).drop 1024 = locals.drop 1036 := by rw [List.drop_drop]
  have h2 : (locals.drop 1036).drop 1024 = locals.drop 2060 := by rw [List.drop_drop]
  rw [← h2, ← h1, List.append_assoc, List.append_assoc,
    List.take_append_drop, List.take_append_drop, List.take_append_drop]

theorem local_mapping (sp : Addr) (locals : List Word) (hl : locals.length = 4121)
    (sv : List Word) :
    Arr sp (locals ++ sv) = MapM (sp + 96#64) (localMapping locals hl) ∗
      Arr sp (locals.take 12) ∗ Arr (sp + 16480#64) (locals.drop 2060 ++ sv) := by
  have hfront : (locals.take 12).length = 12 := by simp [hl]
  have hdest : ((locals.drop 12).take 1024).length = 1024 := by simp [hl]
  have hpos : ((locals.drop 1036).take 1024).length = 1024 := by simp [hl]
  conv => lhs; rw [local_partition locals]
  rw [List.append_assoc, List.append_assoc, List.append_assoc, Arr.append, hfront,
    Arr.append, hdest, Arr.append, hpos]
  simp only [Nat.reduceMul, BitVec.add_assoc, BitVec.reduceAdd]
  simp only [MapM, localMapping,
    BitVec.add_assoc, BitVec.reduceAdd]
  ecancel

theorem localMapping_dest (locals : List Word) (hl : locals.length = 4121)
    {p : Word} (hp : p.toNat < MAX_N) :
    get (localMapping locals hl).dest p =
      locals[12 + p.toNat]'(by change p.toNat < 1024 at hp; omega) := by
  rw [get_eq _ hp]
  change ((locals.drop 12).take 1024)[p.toNat]'(by simpa [hl, MAX_N] using hp) = _
  simp only [List.getElem_take, List.getElem_drop]

theorem localMapping_pos (locals : List Word) (hl : locals.length = 4121)
    {p : Word} (hp : p.toNat < MAX_N) :
    get (localMapping locals hl).pos p =
      locals[1036 + p.toNat]'(by change p.toNat < 1024 at hp; omega) := by
  rw [get_eq _ hp]
  change ((locals.drop 1036).take 1024)[p.toNat]'(by simpa [hl, MAX_N] using hp) = _
  simp only [List.getElem_take, List.getElem_drop]

theorem localMapping_inv (locals : List Word) (hl : locals.length = 4121)
    {m n : Word} (hm : m.toNat ≤ MAX_N) (hn : n.toNat ≤ MAX_N)
    (hd : InitPrefix locals 12 m.toNat) (hp : InitPrefix locals 1036 n.toNat) :
    MapInv m n (localMapping locals hl) := by
  have hd' : ∀ p, p < m → get (localMapping locals hl).dest p = NONE := by
    intro p hpm
    have hpN := Nat.lt_of_lt_of_le (BitVec.lt_def.mp hpm) hm
    rw [localMapping_dest locals hl hpN]
    have he := hd p.toNat (BitVec.lt_def.mp hpm)
    rw [List.getElem?_eq_getElem (by change p.toNat < 1024 at hpN; omega)] at he
    exact Option.some.inj he
  have hp' : ∀ p, p < n → get (localMapping locals hl).pos p = NONE := by
    intro p hpn
    have hpN := Nat.lt_of_lt_of_le (BitVec.lt_def.mp hpn) hn
    rw [localMapping_pos locals hl hpN]
    have he := hp p.toNat (BitVec.lt_def.mp hpn)
    rw [List.getElem?_eq_getElem (by change p.toNat < 1024 at hpN; omega)] at he
    exact Option.some.inj he
  refine ⟨hm, hn, fun p h => Or.inl (hd' p h), fun p h => Or.inl (hp' p h), ?_, ?_⟩
  · intro p h hne
    exact False.elim (hne (hd' p h))
  · intro p h hne
    exact False.elim (hne (hp' p h))

theorem mapping_init_eq {M : Flat.Mapping} {m n : Word}
    (hm : m.toNat ≤ MAX_N) (hn : n.toNat ≤ MAX_N)
    (hd : ∀ p, p < m → get M.dest p = NONE)
    (hp : ∀ p, p < n → get M.pos p = NONE) : M.init m n = M := by
  have fill_eq (v : Vector Word MAX_N) (k : Word) (hk : k.toNat ≤ MAX_N)
      (hv : ∀ p, p < k → get v p = NONE) :
      (offsets k).foldl (fun v p => put v p NONE) v = v := by
    apply Vector.ext
    intro i hi
    simp only [offsets, List.foldl_map]
    rw [fold_put_get' (fun _ => NONE) v hk hi]
    split
    · rename_i hik
      have he := hv (BitVec.ofNat 64 i) (by
        simpa only [BitVec.lt_def, toNat_ofNat_lt hi] using hik)
      exact he.symm.trans (get_ofNat v hi)
    · rfl
  cases M
  simp only [Mapping.init, fill_eq _ _ hm hd, fill_eq _ _ hn hp]

theorem localMapping_init (locals : List Word) (hl : locals.length = 4121)
    {m n : Word} (hm : m.toNat ≤ MAX_N) (hn : n.toNat ≤ MAX_N)
    (hd : InitPrefix locals 12 m.toNat) (hp : InitPrefix locals 1036 n.toNat) :
    (localMapping locals hl).init m n = localMapping locals hl := by
  apply mapping_init_eq hm hn
  · intro p hpm
    have hpN := Nat.lt_of_lt_of_le (BitVec.lt_def.mp hpm) hm
    rw [localMapping_dest locals hl hpN]
    have he := hd p.toNat (BitVec.lt_def.mp hpm)
    rw [List.getElem?_eq_getElem (by change p.toNat < 1024 at hpN; omega)] at he
    exact Option.some.inj he
  · intro p hpn
    have hpN := Nat.lt_of_lt_of_le (BitVec.lt_def.mp hpn) hn
    rw [localMapping_pos locals hl hpN]
    have he := hp p.toNat (BitVec.lt_def.mp hpn)
    rw [List.getElem?_eq_getElem (by change p.toNat < 1024 at hpN; omega)] at he
    exact Option.some.inj he

end FlatShuffler.Unit.PlannerRunU
