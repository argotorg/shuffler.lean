module

public import BbuKraken.FlatList.Ctor
import all BbuKraken.FlatList.Ctor
public import BbuKraken.FlatList.Produce
import all BbuKraken.FlatList.Produce

@[expose] public section

/-!
The loop of the flat `permute` (`permuteLoop`) against `Bbu.go`. The vector `permutation`
of the flat model holds the list of `Bbu.Permutation.Perm` (`PermV`).
-/

namespace Bbu.Flat

open Bbu.Permutation (lastMisplaced target measure Perm)

-- The vector `v` holds the list `l` of length `k`.
def PermV (k : Nat) (v : Vector Word MAX_N) (l : List Nat) : Prop :=
  l.length = k ∧ ∀ i : Word, i.toNat < k → (get v i).toNat = l[i.toNat]!

/-! ## `misplacedBelow` -/

theorem lastMisplaced_succ (l : List Nat) (k : Nat) :
    lastMisplaced l (k + 1) = if l[k]! ≠ k then some k else lastMisplaced l k := by
  unfold lastMisplaced
  rw [List.range_succ, List.foldl_append]
  rfl

theorem misplacedBelow_eq {n : Nat} {v : Vector Word MAX_N} {l : List Nat} (hn : n ≤ MAX_N)
    (hv : PermV n v l) (top : Word) :
    ∀ k, k ≤ n → misplacedBelow v top (BitVec.ofNat 64 k) =
      (lastMisplaced l k).elim top (BitVec.ofNat 64) := by
  intro k
  induction k with
  | zero =>
    intro _
    rw [misplacedBelow, dite_eq_left (show BitVec.ofNat 64 0 = (0 : Word) from rfl)]
    rfl
  | succ k ih =>
    intro hk
    have hk' : k < MAX_N := by omega
    have hk1' : k + 1 < 2 ^ 64 := by rw [MAX_N_eq] at hn; omega
    rw [misplacedBelow, dite_eq_right (by
      intro h; have := congrArg BitVec.toNat h; rw [toNat_ofNat_of_lt hk1'] at this; simp at this)]
    have hk1 : BitVec.ofNat 64 (k + 1) - 1 = BitVec.ofNat 64 k := by
      apply eq_of_toNat; rw [MAX_N_eq] at hn; simp; omega
    have hg := hv.2 (BitVec.ofNat 64 k) (by rw [toNat_ofNat_small hk']; omega)
    rw [toNat_ofNat_small hk'] at hg
    rw [hk1, lastMisplaced_succ]
    by_cases hm : l[k]! = k
    · have hx : get v (BitVec.ofNat 64 k) = BitVec.ofNat 64 k :=
        eq_of_toNat (by rw [hg, toNat_ofNat_small hk', hm])
      rw [ite_eq_right (c := get v (BitVec.ofNat 64 k) ≠ BitVec.ofNat 64 k) (fun h => h hx),
        ite_eq_right (c := l[k]! ≠ k) (fun h => h hm), ih (by omega)]
    · have hx : get v (BitVec.ofNat 64 k) ≠ BitVec.ofNat 64 k := fun h => hm (by
        rw [← hg, h, toNat_ofNat_small hk'])
      rw [ite_eq_left (c := get v (BitVec.ofNat 64 k) ≠ BitVec.ofNat 64 k) hx,
        ite_eq_left (c := l[k]! ≠ k) hm]
      rfl

/-! ## `permuteStep` -/

theorem permuteStep_eq {n : Nat} {v : Vector Word MAX_N} (p : Perm) (fs : St) {top : Word}
    (hn : n ≤ MAX_N) (h0 : 0 < n) (hv : PermV n v p.toList) (htop : top.toNat = n - 1) :
    permuteStep fs top v =
      match target p.toList with
      | none => .ret (.done, fs)
      | some pos => exchange fs top v (BitVec.ofNat 64 pos) := by
  have hl := hv.1
  have hg := hv.2 top (by omega)
  rw [htop] at hg
  have hlt := p.getElem!_lt (i := n - 1) (by omega)
  rw [hl] at hlt
  have hN : n < 2 ^ 64 := by rw [MAX_N_eq] at hn; omega
  have htop' : top = BitVec.ofNat 64 (n - 1) :=
    eq_of_toNat (by rw [htop, toNat_ofNat_of_lt (by omega)])
  unfold permuteStep target
  dsimp only
  rw [hl]
  by_cases hm : p.toList[n - 1]! = n - 1
  · have hx : get v top = top := eq_of_toNat (by rw [hg, hm, htop])
    have hlm : lastMisplaced p.toList n = lastMisplaced p.toList (n - 1) := by
      have := lastMisplaced_succ p.toList (n - 1)
      rw [Nat.sub_add_cancel h0, ite_eq_right (c := p.toList[n - 1]! ≠ n - 1) (fun h => h hm)]
        at this
      exact this
    have hmb : misplacedBelow v top top =
        (lastMisplaced p.toList (n - 1)).elim top (BitVec.ofNat 64) := by
      have := misplacedBelow_eq hn hv top (n - 1) (by omega)
      rw [← htop'] at this
      exact this
    rw [ite_eq_left (c := get v top = top) hx,
      ite_eq_right (c := p.toList[n - 1]! ≠ n - 1) (fun h => h hm), hlm, hmb]
    cases hc : lastMisplaced p.toList (n - 1) with
    | none =>
      simp only [Option.elim_none]
      exact ite_eq_left trivial
    | some i =>
      have hi := (Bbu.Permutation.lastMisplaced_spec p.toList (n - 1) i hc).1
      have hne : BitVec.ofNat 64 i ≠ top := fun h => by
        have := congrArg BitVec.toNat h
        rw [toNat_ofNat_of_lt (by omega), htop] at this; omega
      simp only [Option.elim_some]
      exact ite_eq_right hne
  · have hx : get v top ≠ top := fun h => hm (by rw [← hg, h, htop])
    have hx' : get v top = BitVec.ofNat 64 p.toList[n - 1]! :=
      eq_of_toNat (by rw [hg, toNat_ofNat_of_lt (by omega)])
    rw [ite_eq_right (c := get v top = top) hx, ite_eq_left (c := p.toList[n - 1]! ≠ n - 1) hm, hx']

theorem permuteStep_none {n : Nat} {v : Vector Word MAX_N} (p : Perm) (fs : St) {top : Word}
    (hn : n ≤ MAX_N) (h0 : 0 < n) (hv : PermV n v p.toList) (htop : top.toNat = n - 1)
    (ht : target p.toList = none) : permuteStep fs top v = .ret (.done, fs) := by
  rw [permuteStep_eq p fs hn h0 hv htop, ht]

theorem permuteStep_some {n : Nat} {v : Vector Word MAX_N} (p : Perm) (fs : St) {top : Word}
    (hn : n ≤ MAX_N) (h0 : 0 < n) (hv : PermV n v p.toList) (htop : top.toNat = n - 1) {pos : Nat}
    (ht : target p.toList = some pos) :
    permuteStep fs top v = exchange fs top v (BitVec.ofNat 64 pos) := by
  rw [permuteStep_eq p fs hn h0 hv htop, ht]

/-! ## `exchange` -/

-- The exchange of the entries `a` and `b` of `permutation`.
def swapV (v : Vector Word MAX_N) (a b : Word) : Vector Word MAX_N :=
  put (put v a (get v b)) b (get v a)

theorem exchange_same {fs : St} {top pos : Word} (v : Vector Word MAX_N)
    (h : get fs.data pos = get fs.data (fs.size - 1)) :
    exchange fs top v pos = .cont (swapDestinations fs pos top) (swapV v pos top) := by
  unfold exchange
  rw [ite_eq_left h]
  rfl

theorem exchange_block {fs : St} {top pos : Word} (v : Vector Word MAX_N)
    (h : get fs.data pos ≠ get fs.data (fs.size - 1)) (hr : ¬isSwapReachable fs pos = true) :
    exchange fs top v pos = .ret (blockSwapUnreachable fs pos) := by
  unfold exchange
  rw [ite_eq_right h, ite_eq_left (c := (!isSwapReachable fs pos) = true) (by simpa using hr)]

theorem exchange_swap {fs : St} {top pos : Word} (v : Vector Word MAX_N)
    (h : get fs.data pos ≠ get fs.data (fs.size - 1)) (hr : isSwapReachable fs pos = true) :
    exchange fs top v pos =
      .cont (swapDestinations (stackSwap fs pos) pos top) (swapV v pos top) := by
  unfold exchange
  rw [ite_eq_right h, ite_eq_right (c := (!isSwapReachable fs pos) = true) (by simpa using hr)]
  rfl

theorem PermV.swap {n : Nat} {v : Vector Word MAX_N} (p : Perm) (hn : n ≤ MAX_N)
    (hv : PermV n v p.toList) {w top : Word} {pos : Nat} (hw : w.toNat = pos)
    (htop : top.toNat = n - 1) (hpos : pos < n - 1) (hi hj) :
    PermV n (swapV v w top) (p.swap (p.toList.length - 1) pos hi hj).toList := by
  refine ⟨by rw [p.length_swap, hv.1], fun i hi' => ?_⟩
  rw [p.getElem!_swap, hv.1]
  unfold swapV
  rw [get_put _ _ _ (by omega), get_put _ _ _ (by omega)]
  by_cases h1 : i = top
  · have hi1 : i.toNat = n - 1 := by rw [h1, htop]
    rw [ite_eq_left h1, ite_eq_right (c := i.toNat = pos) (by omega),
      ite_eq_left (c := i.toNat = n - 1) hi1, hv.2 w (by omega), hw]
  · have hi1 : i.toNat ≠ n - 1 := fun h => h1 (eq_of_toNat (by rw [h, htop]))
    rw [ite_eq_right h1]
    by_cases h2 : i = w
    · have hi2 : i.toNat = pos := by rw [h2, hw]
      rw [ite_eq_left h2, ite_eq_left (c := i.toNat = pos) hi2, hv.2 top (by omega), htop]
    · have hi2 : i.toNat ≠ pos := fun h => h2 (eq_of_toNat (by rw [h, hw]))
      rw [ite_eq_right h2, ite_eq_right (c := i.toNat = pos) hi2,
        ite_eq_right (c := i.toNat = n - 1) hi1, hv.2 i hi']

/-! ## The loop -/

theorem permuteLoop_ret {f : Nat} {fs : St} {top : Word} {v : Vector Word MAX_N} {r : Status × St}
    (h : permuteStep fs top v = .ret r) : permuteLoop (f + 1) fs top v = r := by
  simp [permuteLoop, h]

theorem permuteLoop_cont {f : Nat} {fs fs' : St} {top : Word} {v v' : Vector Word MAX_N}
    (h : permuteStep fs top v = .cont fs' v') :
    permuteLoop (f + 1) fs top v = permuteLoop f fs' top v' := by
  simp [permuteLoop, h]

theorem swapPos_len (st : Bbu.St) (pos : Nat) : (swapPos st pos).len = st.len := by
  unfold swapPos
  rw [swapDest_len]
  simp [Bbu.St.len]

section
variable {e : Env}

theorem sim_permuteLoop {top : Word} :
    ∀ (fuel : Nat) (fs : St) (st : Bbu.St) (p : Perm) (v : Vector Word MAX_N),
      Sim e fs st → PermV st.len v p.toList → 0 < st.len → top.toNat = st.len - 1 →
      measure p.toList < fuel → SimR e (permuteLoop fuel fs top v) (go st p) := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _ _ _ _ hf; omega
  | succ f ih =>
    intro fs st p v hs hv h0 htop hf
    have hle := hs.len_lt
    have hsz := hs.size
    rw [go]
    split
    · next ht =>
      rw [permuteLoop_ret (permuteStep_none p fs hle h0 hv htop ht)]
      exact ⟨rfl, hs⟩
    · next pos ht =>
      dsimp only
      have hpl := p.target_lt ht
      rw [hv.1] at hpl
      have hpos : pos < st.len - 1 := hpl.1
      have hw : (BitVec.ofNat 64 pos).toNat = pos := toNat_ofNat_small (by omega)
      generalize hW : BitVec.ofNat 64 pos = w at hw
      have hstep := permuteStep_some p fs hle h0 hv htop ht
      rw [hW] at hstep
      have hwl : w.toNat < st.len := by omega
      have hval : get fs.data w = st.val pos := by rw [hs.data w hwl, hw]
      have htl : (fs.size - 1).toNat = st.len - 1 := by bv_omega
      have hvt : get fs.data (fs.size - 1) = st.val (st.len - 1) := by
        rw [hs.data _ (by omega), htl]
      have hl1 := hv.1
      have hm := p.measure_target_lt ht (by omega) (by omega)
      have hv' := PermV.swap p hle hv hw htop hpos (by omega) (by omega)
      by_cases h1 : st.val pos = st.val (st.len - 1)
      · rw [ite_eq_left h1]
        rw [permuteLoop_cont (hstep.trans (exchange_same v (by rw [hval, hvt, h1])))]
        have hs' := hs.swapDest' (a := w) (b := top) hwl htop (by omega)
        rw [hw] at hs'
        have hl' := swapDest_len st pos (st.len - 1)
        exact ih _ _ _ _ hs' (by rw [hl']; exact hv') (by omega) (by rw [hl']; exact htop)
          (by omega)
      · rw [ite_eq_right h1]
        have hne : get fs.data w ≠ get fs.data (fs.size - 1) := by rw [hval, hvt]; exact h1
        have hd : (depthOf fs w).toNat = st.len - 1 - pos := by unfold depthOf; bv_omega
        by_cases h2 : MAX_SWAP_DEPTH < st.len - 1 - pos
        · rw [ite_eq_left h2]
          have hr : ¬isSwapReachable fs w = true := by
            unfold isSwapReachable maxSwapDepth; unfold MAX_SWAP_DEPTH at h2
            simp only [decide_eq_true_eq]; bv_omega
          rw [permuteLoop_ret (hstep.trans (exchange_block v hne hr))]
          have hb := sim_blockSwap hs hwl (by rw [hw]; exact h2)
          rw [hw] at hb
          exact hb
        · rw [ite_eq_right h2]
          have hr : isSwapReachable fs w = true := by
            unfold isSwapReachable maxSwapDepth; unfold MAX_SWAP_DEPTH at h2
            simp only [decide_eq_true_eq]; bv_omega
          rw [permuteLoop_cont (hstep.trans (exchange_swap v hne hr))]
          have hs' : Sim e (swapDestinations (stackSwap fs w) w top) (swapPos st w.toNat) := by
            unfold swapPos
            refine Sim.swapDest' ?_ ?_ ?_ ?_
            · exact Sim.swapVals hs hwl rfl rfl rfl rfl
            · simp [Bbu.St.len]; simp only [Bbu.St.len] at hwl; omega
            · exact htop
            · simp [Bbu.St.len]; simp only [Bbu.St.len] at h0; omega
          rw [hw] at hs'
          have hl' := swapPos_len st pos
          exact ih _ _ _ _ hs' (by rw [hl']; exact hv') (by omega) (by rw [hl']; exact htop)
            (by omega)

end

end Bbu.Flat
