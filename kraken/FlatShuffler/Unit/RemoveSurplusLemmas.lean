module

public import FlatShuffler.Unit.Generate
import all FlatShuffler.Unit.Generate
public import FlatShuffler.Unit.ProduceLemmas
import all FlatShuffler.Unit.ProduceLemmas
public import FlatShuffler.Unit.Pop
import all FlatShuffler.Unit.Pop
public import FlatShuffler.FlatSurplusRel
import all FlatShuffler.FlatSurplusRel

@[expose] public section

/-!
# Lemmas for the `removeSurplus` unit proof

The model part splits `Flat.removeSurplus` at the points of the asm: `afterR r` is the rest of
`removeSurplus` after the action `r` of a pass (the pop and the next passes), `inner` is the
action of a pass, and `eqStep` is the action after the scan of `equalBelow` from `q`.

The stack part: `removeSurplus` pushes `rbx` and keeps the struct in `rbx`. `Bx` is the state
between the push and the pop. `Extras` owns the two free words for `swapWith` and `pop`.
-/

open Std.WP Lean.Order
open scoped Program.WP
open ProofKit

namespace FlatShuffler.Unit.Surplus

open FlatShuffler.Sep Generate

/-! ## The flat model -/

-- The rest of `removeSurplus` after the pop.
def afterPop (st : Flat.St) : Flat.Status × Flat.St :=
  if (Flat.pop st).1 = .done then Flat.removeSurplus (Flat.pop st).2 else Flat.pop st

-- The rest of `removeSurplus` after the action `r` of a pass.
def afterR (r : Flat.Status × Flat.St) : Flat.Status × Flat.St :=
  if r.1 = .done then afterPop r.2 else r

-- The action after the scan of `equalBelow` from `q`. `top` is the top slot.
def eqStep (st : Flat.St) (q top dp : Word) : Flat.Status × Flat.St :=
  if Flat.equalBelow st q ≠ Flat.NONE then (.done, Flat.swapDestinations st (Flat.equalBelow st q) top)
  else Flat.swapWith st dp

-- The action of a pass, after the scan: `sh` is the shallowest surplus slot, `dp` the deepest
-- reachable one.
def inner (st : Flat.St) (sh dp : Word) : Flat.Status × Flat.St :=
  if sh = st.size - 1 then (.done, st) else eqStep st (st.size - 1) (st.size - 1) dp

theorem swapDestinations_size (st : Flat.St) (a b : Word) :
    (Flat.swapDestinations st a b).size = st.size := rfl

theorem inner_size (st : Flat.St) (sh dp : Word) : (inner st sh dp).2.size = st.size := by
  unfold inner eqStep
  split
  · rfl
  · split
    · rfl
    · exact Flat.swapWith_size st dp

theorem afterR_ne {r : Flat.Status × Flat.St} (h : r.1 ≠ .done) : afterR r = r := by
  unfold afterR; rw [ite_eq_right h]

theorem afterR_done {r : Flat.Status × Flat.St} (h : r.1 = .done) : afterR r = afterPop r.2 := by
  unfold afterR; rw [ite_eq_left h]

theorem afterPop_ne {st : Flat.St} (h : (Flat.pop st).1 ≠ .done) : afterPop st = Flat.pop st := by
  unfold afterPop; rw [ite_eq_right h]

theorem afterPop_done {st : Flat.St} (h : (Flat.pop st).1 = .done) :
    afterPop st = Flat.removeSurplus (Flat.pop st).2 := by
  unfold afterPop; rw [ite_eq_left h]

-- A `pop` that is done.
theorem pop_done {st : Flat.St} (h : (Flat.pop st).1 = .done) :
    st.size ≠ 0 ∧ (Flat.pop st).2.size = st.size - 1 ∧ (Flat.pop st).2.dest = st.dest
      ∧ (Flat.pop st).2.targetSize = st.targetSize
      ∧ (Flat.pop st).2.trace = st.trace ++ [Op.pop] := by
  by_cases h0 : st.size = 0
  · rw [Pop.pop_zero st h0] at h; cases h
  · by_cases hd : Flat.get st.dest (st.size - 1) = Flat.NONE
    · rw [Pop.pop_none st h0 hd]; exact ⟨h0, rfl, rfl, rfl, rfl⟩
    · rw [Pop.pop_some st h0 hd]; exact ⟨h0, rfl, rfl, rfl, rfl⟩

theorem rs_zero {st : Flat.St} (h : st.size = 0) : Flat.removeSurplus st = (.done, st) := by
  unfold Flat.removeSurplus
  rw [h]
  rfl

-- The end of a pass: the match of `surplusLoop` on the result of the action `r`.
theorem loop_tail (r : Flat.Status × Flat.St) (k : Nat)
    (hk : r.1 = .done → (Flat.pop r.2).1 = .done → (Flat.pop r.2).2.size.toNat = k) :
    (match (if r.1 ≠ .done then Except.error r
        else if (Flat.pop r.2).1 ≠ .done then Except.error (Flat.pop r.2)
        else Except.ok (Flat.pop r.2).2) with
      | .error r => r
      | .ok st => Flat.surplusLoop st k) = afterR r := by
  by_cases h1 : r.1 = .done
  · rw [afterR_done h1, ite_eq_right (fun e => e h1)]
    by_cases h2 : (Flat.pop r.2).1 = .done
    · rw [afterPop_done h2, ite_eq_right (fun e => e h2)]
      unfold Flat.removeSurplus
      rw [hk h1 h2]
    · rw [afterPop_ne h2, ite_eq_left h2]
  · rw [afterR_ne h1, ite_eq_left h1]

-- One pass of `removeSurplus`, after the scan.
theorem rs_step {st : Flat.St} (h : st.size ≠ 0) {sh dp : Word}
    (hsc : Flat.surplusScan st st.size Flat.NONE Flat.NONE = (sh, dp)) :
    Flat.removeSurplus st =
      if sh = Flat.NONE then (.done, st)
      else if dp = Flat.NONE then Flat.blockSwapUnreachable st sh
      else afterR (inner st sh dp) := by
  have h0 : st.size.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq (by simpa using e))
  obtain ⟨k, hk⟩ : ∃ k, st.size.toNat = k + 1 := ⟨st.size.toNat - 1, by omega⟩
  unfold Flat.removeSurplus
  rw [hk, Flat.surplusLoop, ite_eq_right h]
  unfold Flat.surplusPass
  dsimp only
  rw [hsc]
  dsimp only
  by_cases h1 : sh = Flat.NONE
  · rw [ite_eq_left h1, ite_eq_left h1]
  · rw [ite_eq_right h1, ite_eq_right h1]
    by_cases h2 : dp = Flat.NONE
    · rw [ite_eq_left h2, ite_eq_left h2]
    · rw [ite_eq_right h2, ite_eq_right h2]
      refine loop_tail (inner st sh dp) k fun _ hp => ?_
      have hs := (pop_done hp).2.1
      rw [hs, inner_size]
      bv_omega

-- A `swapWith` that is done.
theorem swap_done {st : Flat.St} {p : Word} (h : (Flat.swapWith st p).1 = .done) :
    p < st.size ∧ (Flat.swapWith st p).2 = Flat.swapDestinations (Flat.stackSwap st p) p (st.size - 1) := by
  unfold Flat.swapWith at h ⊢
  dsimp only at h ⊢
  by_cases h1 : p < st.size
  · rw [ite_eq_right (fun hn => hn h1)] at h ⊢
    by_cases h2 : Flat.isFinal st p = true
    · rw [ite_eq_left h2] at h; cases h
    · rw [ite_eq_right h2] at h ⊢
      by_cases h3 : 1 ≤ Flat.depthOf st p ∧ Flat.depthOf st p ≤ Flat.maxSwapDepth
      · rw [ite_eq_right (fun hn => hn h3)]; exact ⟨h1, rfl⟩
      · rw [ite_eq_left h3] at h; cases h
  · rw [ite_eq_left h1] at h; cases h

-- A `swapWith` that is not done keeps the state.
theorem swap_ne {st : Flat.St} {p : Word} (h : (Flat.swapWith st p).1 ≠ .done) :
    (Flat.swapWith st p).2 = st := by
  unfold Flat.swapWith at h ⊢
  dsimp only at h ⊢
  by_cases h1 : p < st.size
  · rw [ite_eq_right (fun hn => hn h1)] at h ⊢
    by_cases h2 : Flat.isFinal st p = true
    · rw [ite_eq_left h2]
    · rw [ite_eq_right h2] at h ⊢
      by_cases h3 : 1 ≤ Flat.depthOf st p ∧ Flat.depthOf st p ≤ Flat.maxSwapDepth
      · rw [ite_eq_right (fun hn => hn h3)] at h; exact absurd rfl h
      · rw [ite_eq_left h3]
  · rw [ite_eq_left h1]

/-! ## `DestOk` -/

section
variable {st : Flat.St}

theorem destOk_dsw (hd : DestOk st) (hN : st.size.toNat ≤ maxStackSize) {a b : Word} (ha : a < st.size)
    (hb : b < st.size) : DestOk (dsw st a b) := by
  intro i hi
  have hi' : i < st.size.toNat := hi
  have haN : a.toNat < maxStackSize := by have := BitVec.lt_def.mp ha; omega
  have hbN : b.toNat < maxStackSize := by have := BitVec.lt_def.mp hb; omega
  have hda := hd a.toNat (BitVec.lt_def.mp ha)
  have hdb := hd b.toNat (BitVec.lt_def.mp hb)
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq] at hda hdb
  show Flat.get (Flat.put (Flat.put st.dest a (Flat.get st.dest b)) b (Flat.get st.dest a))
      (BitVec.ofNat 64 i) = Flat.NONE
    ∨ (Flat.get (Flat.put (Flat.put st.dest a (Flat.get st.dest b)) b (Flat.get st.dest a))
      (BitVec.ofNat 64 i)).toNat < st.targetSize.toNat
  by_cases eb : BitVec.ofNat 64 i = b
  · rw [eb, get_put_self _ hbN]; exact hda
  · rw [get_put_ne _ _ eb]
    by_cases ea : BitVec.ofNat 64 i = a
    · rw [ea, get_put_self _ haN]; exact hdb
    · rw [get_put_ne _ _ ea]; exact hd i hi'

theorem destOk_posAt (hd : DestOk st) (i : Word) : DestOk (posAt st i) := hd

-- `DestOk` of the ghost after the store of the swapped destinations and of `positionOf`. A
-- separate lemma: the check of `flat (withDest …)` against `dsw (flat g)` unfolds `flat`.
theorem destOk_withDest {g : G} {a b : Word} (h : DestOk (dsw (flat g) a b)) :
    DestOk (flat (withDest g (dsw (flat g) a b).dest)) := h

theorem destOk_withPos {g : G} {p : Vector Word maxStackSize} (h : DestOk (flat g)) :
    DestOk (flat (withPos g p)) := h

theorem destOk_swapDest (hd : DestOk st) (hN : st.size.toNat ≤ maxStackSize) {a b : Word}
    (ha : a < st.size) (hb : b < st.size) : DestOk (Flat.swapDestinations st a b) := by
  rw [swapDestinations_eq]
  exact destOk_posAt (destOk_posAt (destOk_dsw hd hN ha hb) a) b

theorem destOk_swapWith (hd : DestOk st) (hN : st.size.toNat ≤ maxStackSize) (p : Word) :
    DestOk (Flat.swapWith st p).2 := by
  by_cases h : (Flat.swapWith st p).1 = .done
  · obtain ⟨hp, e⟩ := swap_done h
    rw [e]
    have ht : st.size - 1 < st.size := by bv_omega
    exact destOk_swapDest (st := Flat.stackSwap st p) hd hN hp ht
  · rw [swap_ne h]; exact hd

theorem destOk_pop (hd : DestOk st) : DestOk (Flat.pop st).2 := by
  by_cases h : (Flat.pop st).1 = .done
  · obtain ⟨h0, hs, hde, ht, -⟩ := pop_done h
    intro i hi
    rw [hs] at hi
    rw [hde, ht]
    exact hd i (by bv_omega)
  · by_cases h0 : st.size = 0
    · rw [Pop.pop_zero st h0]; exact hd
    · by_cases hd' : Flat.get st.dest (st.size - 1) = Flat.NONE
      · rw [Pop.pop_none st h0 hd'] at h; exact absurd rfl h
      · rw [Pop.pop_some st h0 hd'] at h; exact absurd rfl h

end

-- The length of the trace is `nops`.
theorem trace_len {g : G} (h : g.Ok) : (flat g).trace.length = g.h.nops.toNat := by
  simp only [flat, List.length_map, List.length_take, Vector.length_toList]
  have := h.nops
  omega

/-! ## The scans -/

-- The literals are `0#64` and `1#64`, the form of the goals after `symexec_norm`.
theorem scan_zero (st : Flat.St) (sh dp : Word) : Flat.surplusScan st 0#64 sh dp = (sh, dp) := by
  rw [Flat.surplusScan]; exact dite_eq_left rfl

theorem scan_succ (st : Flat.St) {p : Word} (hp : p + 1#64 ≠ 0#64) (sh dp : Word) :
    Flat.surplusScan st (p + 1#64) sh dp =
      if Flat.isSurplus st p then
        Flat.surplusScan st p (if sh = Flat.NONE then p else sh)
          (if Flat.isSwapReachable st p then p else dp)
      else Flat.surplusScan st p sh dp := by
  rw [Flat.surplusScan, dite_eq_right (c := p + 1#64 = 0) hp, show p + 1#64 - 1 = p by bv_omega]

theorem eqb_zero (st : Flat.St) : Flat.equalBelow st 0#64 = Flat.NONE := by
  rw [Flat.equalBelow]; exact dite_eq_left rfl

theorem eqb_ne (st : Flat.St) {q : Word} (h : q ≠ 0#64) :
    Flat.equalBelow st q =
      if Flat.isSurplus st (q - 1#64) ∧ Flat.get st.data (q - 1#64) = Flat.get st.data (st.size - 1#64)
      then q - 1#64 else Flat.equalBelow st (q - 1#64) := by
  rw [Flat.equalBelow]; exact dite_eq_right h

section
variable {st : Flat.St} {q top dp : Word}

theorem eqStep_zero : eqStep st 0#64 top dp = Flat.swapWith st dp := by
  unfold eqStep; rw [eqb_zero, ite_eq_right (fun h => h rfl)]

theorem eqStep_skip (h : q ≠ 0#64)
    (hn : ¬(Flat.isSurplus st (q - 1#64) ∧ Flat.get st.data (q - 1#64) = Flat.get st.data (st.size - 1#64))) :
    eqStep st q top dp = eqStep st (q - 1#64) top dp := by
  unfold eqStep; rw [eqb_ne st h, ite_eq_right hn]

theorem eqStep_hit (h : q ≠ 0#64) (hq : q.toNat ≤ maxStackSize)
    (hs : Flat.isSurplus st (q - 1#64) ∧ Flat.get st.data (q - 1#64) = Flat.get st.data (st.size - 1#64)) :
    eqStep st q top dp = (.done, Flat.swapDestinations st (q - 1#64) top) := by
  unfold eqStep
  rw [eqb_ne st h, ite_eq_left hs]
  have : q - 1#64 ≠ Flat.NONE := by
    unfold Flat.NONE; simp only [maxStackSize] at hq; bv_omega
  rw [ite_eq_left this]

end

-- `subq $17, %r8; subq %rdx, %r8`: the excess of `blockSwapUnreachable`.
theorem exc_eq (st : Flat.St) (x : Word) :
    st.size - 17#64 - x = Flat.depthOf st x - Flat.maxSwapDepth := by
  unfold Flat.depthOf Flat.maxSwapDepth
  bv_omega


/-! ## The stack: the pushed `rbx` -/

-- The frame of the callees: the pushed `rbx`, the return address and `F`.
def Fr (s : MachineData) (ra : Int64) (F : MProp 64) : MProp 64 :=
  Wd (rsp s - 16#64) s.regs.rbx.toBitVec ∗ Wd (rsp s - 8#64) ra.toBitVec ∗ F

-- The callees use two words below their return slot.
def Extras (s : MachineData) (F : MProp 64) : MProp 64 :=
  ExArr (rsp s - 40#64) 2 ∗ F

theorem stk2_free (P : MProp 64) (sp : Addr) (fr : List Word) (w x v : Word)
    (F : MProp 64) :
    P ∗ Stk sp (fr ++ [w, x]) v ∗ F =
      P ∗ Stk (sp - 16#64) fr w ∗ (Wd (sp - 16#64) x ∗ Wd (sp - 8#64) v ∗ F) := by
  rw [show fr ++ [w, x] = (fr ++ [w]) ++ [x] by simp,
    Stk.call, Stk.call, show sp - 8#64 - 8#64 = sp - 16#64 by bv_omega]

theorem extras_pre {S : Addr} {g : G} {F : MProp 64} {s : MachineData}
    {A : G → MachineData → Prop} (hp : Sep.Pre S g F A 4 s) :
    Sep.Pre S g (Extras s F) A 2 s := by
  obtain ⟨fr, v, hl, hm⟩ := hp.mem
  have htake : (fr.take 2).length = 2 := by simp [hl]
  have hdrop : (fr.drop 2).length = 2 := by simp [hl]
  rw [← List.take_append_drop 2 fr, Stk.frame_below] at hm
  have ha : rsp s - 8#64 - BitVec.ofNat 64 (8 * ((fr.take 2).length + (fr.drop 2).length)) =
      rsp s - 40#64 := by rw [htake, hdrop]; bv_omega
  rw [ha] at hm
  have he : View S g ∗ Stk (rsp s) (fr.drop 2) v ∗ (Arr (rsp s - 40#64) (fr.take 2) ∗ F) =
      Arr (rsp s - 40#64) (fr.take 2) ∗ (View S g ∗ Stk (rsp s) (fr.drop 2) v ∗ F) := by ac_rfl
  have hm' := ExArr.intro htake (he ▸ hm)
  refine ⟨hp.rdi, hp.ok, ⟨fr.drop 2, v, hdrop, ?_⟩, hp.args⟩
  unfold Extras
  have he' : ExArr (rsp s - 40#64) 2 ∗ (View S g ∗ Stk (rsp s) (fr.drop 2) v ∗ F) =
      View S g ∗ Stk (rsp s) (fr.drop 2) v ∗ (ExArr (rsp s - 40#64) 2 ∗ F) := by ac_rfl
  exact he' ▸ hm'

theorem extras_post {S : Addr} {F : MProp 64} {s t : MachineData}
    {Q : G → MachineData → Prop} (hp : Sep.Post S (Extras s F) 2 Q s t) :
    Sep.Post S F 4 Q s t := by
  obtain ⟨g, fr, v, hq, hok, hl, hm⟩ := hp
  have he : View S g ∗ Stk (rsp s) fr v ∗ Extras s F =
      ExArr (rsp s - 40#64) 2 ∗ (View S g ∗ Stk (rsp s) fr v ∗ F) := by
    unfold Extras
    ac_rfl
  obtain ⟨lo, hlo, hm⟩ := ExArr.elim (he ▸ hm)
  refine ⟨g, lo ++ fr, v, hq, hok, by simp [hlo, hl], ?_⟩
  rw [Stk.frame_below]
  have ha : rsp s - 8#64 - BitVec.ofNat 64 (8 * (lo.length + fr.length)) =
      rsp s - 40#64 := by rw [hlo, hl]; bv_omega
  rw [ha]
  have he' : Arr (rsp s - 40#64) lo ∗ (View S g ∗ Stk (rsp s) fr v ∗ F) =
      View S g ∗ Stk (rsp s) fr v ∗ (Arr (rsp s - 40#64) lo ∗ F) := by ac_rfl
  exact he' ▸ hm

-- The two free words: the return address of a callee and `rbx`.
theorem stk2 (P : MProp 64) (sp : Addr) (w x v : Word) (F : MProp 64) :
    P ∗ Stk sp [w, x] v ∗ F
      = P ∗ Stk (sp - 16#64) [] w ∗ (Wd (sp - 16#64) x ∗ Wd (sp - 8#64) v ∗ F) := by
  have e : [w, x] = ([] ++ [w]) ++ [x] := rfl
  rw [e, Stk.call, Stk.call, show sp - 8#64 - 8#64 = sp - 16#64 by bv_omega]

theorem split2 {fr : List Word} (h : fr.length = 2) : ∃ w x, fr = [w, x] :=
  match fr, h with
  | [w, x], _ => ⟨w, x, rfl⟩

-- A state between the push and the pop: `rbx` is the struct, and the stack holds the return
-- address slot `w` of a callee and `Fr`.
structure Bx (S : Addr) (g : G) (F : MProp 64) (s : MachineData) (ra : Int64) (w : Word)
    (t : MachineData) : Prop where
  mem : (View S g ∗ Stk (rsp s - 16#64) [] w ∗ Fr s ra F).get t.dmem
  sp : t.regs.rsp.toBitVec = rsp s - 16#64
  bx : t.regs.rbx.toBitVec = S
  bp : t.regs.rbp = s.regs.rbp
  r12 : t.regs.r12 = s.regs.r12
  r13 : t.regs.r13 = s.regs.r13
  r14 : t.regs.r14 = s.regs.r14
  r15 : t.regs.r15 = s.regs.r15

section
variable {S : Addr} {g : G} {F : MProp 64} {s : MachineData} {ra : Int64} {w : Word}

-- The address of `pushq %rbx` (`r` is `rsp` after the call).
theorem push_isSome {m : Mem 64} {x v : Word} (hm : (View S g ∗ Stk (rsp s) [w, x] v ∗ F).get m)
    {r : Addr} (hr : r = rsp s - 8#64) : (m.loadInt (r - 8#64) 8).isSome = true := by
  rw [stk2] at hm
  rw [show r - 8#64 = rsp s - 16#64 by subst hr; bv_omega]
  exact isSome_of_eq x hm (by ecancel)

-- `pushq %rbx; movq %rdi, %rbx` from the entry stack.
theorem Bx.push {m₀ : Mem 64} {x : Word} {c : MachineData}
    (hm : (View S g ∗ Stk (rsp s) [w, x] ra.toBitVec ∗ F).get m₀)
    {r : Addr} (hr : r = rsp s - 8#64)
    (hc : c.dmem = m₀.storeInt (r - 8#64) 8 s.regs.rbx.toBitVec.toInt)
    (hsp : c.regs.rsp.toBitVec = r - 8#64) (hbx : c.regs.rbx.toBitVec = S)
    (hbp : c.regs.rbp = s.regs.rbp) (h12 : c.regs.r12 = s.regs.r12)
    (h13 : c.regs.r13 = s.regs.r13) (h14 : c.regs.r14 = s.regs.r14)
    (h15 : c.regs.r15 = s.regs.r15) : Bx S g F s ra w c := by
  have e1 : r - 8#64 = rsp s - 16#64 := by subst hr; bv_omega
  rw [e1] at hc hsp
  refine ⟨?_, hsp, hbx, hbp, h12, h13, h14, h15⟩
  rw [stk2] at hm
  have h1 : (Wd (rsp s - 16#64) x ∗ (View S g ∗ Stk (rsp s - 16#64) [] w
      ∗ Wd (rsp s - 8#64) ra.toBitVec ∗ F)).get m₀ := by
    have e : View S g ∗ Stk (rsp s - 16#64) [] w ∗ (Wd (rsp s - 16#64) x
        ∗ Wd (rsp s - 8#64) ra.toBitVec ∗ F)
        = Wd (rsp s - 16#64) x ∗ (View S g ∗ Stk (rsp s - 16#64) [] w
          ∗ Wd (rsp s - 8#64) ra.toBitVec ∗ F) := by ecancel
    exact e ▸ hm
  have h2 := Wd.store h1 s.regs.rbx.toBitVec
  rw [hc]
  have e : Wd (rsp s - 16#64) s.regs.rbx.toBitVec ∗ (View S g ∗ Stk (rsp s - 16#64) [] w
      ∗ Wd (rsp s - 8#64) ra.toBitVec ∗ F)
      = View S g ∗ Stk (rsp s - 16#64) [] w ∗ Fr s ra F := by unfold Fr; ecancel
  exact e ▸ h2

-- The precondition of a callee with no free word.
theorem Bx.pre0 {A : G → MachineData → Prop} {c : MachineData} (h : Bx S g F s ra w c)
    (hdi : rdi c = S) (hok : g.Ok) (hA : A g c) : Sep.Pre S g (Fr s ra F) A 0 c :=
  ⟨hdi, hok, ⟨[], w, rfl, by simpa only [rsp, Reg64s.get64_rsp, h.sp] using h.mem⟩, hA⟩

-- After a callee with no free word.
theorem Bx.agree0 {c t : MachineData} {g' : G} {fr' : List Word} {w' : Word}
    (h : Bx S g F s ra w c) (hag : Sep.mod.Agree c t) (hl : fr'.length = 0)
    (hm : (View S g' ∗ Stk (rsp c) fr' w' ∗ Fr s ra F).get t.dmem) : Bx S g' F s ra w' t := by
  obtain rfl := List.eq_nil_of_length_eq_zero hl
  exact {
    mem := by simpa only [rsp, Reg64s.get64_rsp, h.sp] using hm
    sp := by rw [mod_keep hag (by simp [Sep.mod]) Reg64s.get64_rsp]; exact h.sp
    bx := by rw [mod_keep hag (by simp [Sep.mod]) Reg64s.get64_rbx]; exact h.bx
    bp := (mod_keep hag (by simp [Sep.mod]) Reg64s.get64_rbp).trans h.bp
    r12 := (mod_keep hag (by simp [Sep.mod]) Reg64s.get64_r12).trans h.r12
    r13 := (mod_keep hag (by simp [Sep.mod]) Reg64s.get64_r13).trans h.r13
    r14 := (mod_keep hag (by simp [Sep.mod]) Reg64s.get64_r14).trans h.r14
    r15 := (mod_keep hag (by simp [Sep.mod]) Reg64s.get64_r15).trans h.r15 }

-- The call rule of a callee with no free word, from a `Bx` state.
theorem Bx.call0 {A : G → MachineData → Prop} {Q : G → G → MachineData → MachineData → Prop}
    {c : MachineData} {K : MachineData → Prop} (h : Bx S g F s ra w c) (hdi : rdi c = S)
    (hok : g.Ok) (hA : A g c)
    (hK : ∀ t g' w', Bx S g' F s ra w' t → Q g g' c t → g'.Ok → K t) :
    ∃ S' g' F', Sep.Pre S' g' F' A 0 c
      ∧ ∀ s', Sep.Post S' F' 0 (fun g'' t => Q g' g'' c t) c s' → Sep.mod.Agree c s' → K s' :=
  ⟨S, g, Fr s ra F, h.pre0 hdi hok hA, fun s' ⟨g', _, v', hQ, hok', hl, hm⟩ hag =>
    hK s' g' v' (h.agree0 hag hl hm) hQ hok'⟩

-- Expose the two free words only at the callee boundary.
theorem Bx.call2 {A : G → MachineData → Prop}
    {Q X : G → G → MachineData → MachineData → Prop}
    {c : MachineData} {K E : MachineData → Prop}
    (h : Bx S g (Extras s F) s ra w c) (hdi : rdi c = S) (hok : g.Ok) (hA : A g c)
    (hK : ∀ t g' w', Bx S g' (Extras s F) s ra w' t → Q g g' c t → g'.Ok → K t)
    (hX : ∀ t, Sep.Post S F 4 (fun g' t => X g g' c t) s t →
      t.regs.get64 .rdi = 1#64 → E t) :
    ∃ S' g' F', Sep.Pre S' g' F' A 2 c
      ∧ (∀ t, Sep.Post S' F' 2 (fun g'' t => Q g' g'' c t) c t →
        Sep.mod.Agree c t → K t)
      ∧ (∀ t, Sep.Post S' F' 2 (fun g'' t => X g' g'' c t) c t →
        t.regs.get64 .rdi = 1#64 → E t) := by
  have split : ∀ (g' : G) (fr : List Word) (w' : Word), fr.length = 2 →
      View S g' ∗ Stk (rsp s - 16#64) fr w' ∗ Fr s ra F =
        Arr (rsp s - 40#64) fr ∗
          (View S g' ∗ Stk (rsp s - 16#64) [] w' ∗ Fr s ra F) := by
    intro g' fr w' hl
    rw [Stk.frame]
    have ha : rsp s - 16#64 - 8#64 - BitVec.ofNat 64 (8 * fr.length) =
        rsp s - 40#64 := by rw [hl]; bv_omega
    rw [ha]
    ac_rfl
  have packed : ∀ (g' : G) (w' : Word),
      View S g' ∗ Stk (rsp s - 16#64) [] w' ∗ Fr s ra (Extras s F) =
        ExArr (rsp s - 40#64) 2 ∗
          (View S g' ∗ Stk (rsp s - 16#64) [] w' ∗ Fr s ra F) := by
    intro g' w'
    unfold Fr Extras
    ac_rfl
  obtain ⟨fr, hl, hm⟩ := ExArr.elim ((packed g w) ▸ h.mem)
  have hsp : rsp c = rsp s - 16#64 := h.sp
  have hm' : (View S g ∗ Stk (rsp c) fr w ∗ Fr s ra F).get c.dmem := by
    rw [hsp, split g fr w hl]
    exact hm
  refine ⟨S, g, Fr s ra F, ⟨hdi, hok, ⟨fr, w, hl, hm'⟩, hA⟩, ?_, ?_⟩
  · rintro t ⟨g', fr', w', hq, hok', hl', hm⟩ hag
    have hm' : (Arr (rsp s - 40#64) fr' ∗
        (View S g' ∗ Stk (rsp s - 16#64) [] w' ∗ Fr s ra F)).get t.dmem := by
      rw [hsp, split g' fr' w' hl'] at hm
      exact hm
    have hpack := ExArr.intro hl' hm'
    apply hK t g' w' (h.agree0 (fr' := []) hag rfl ?_) hq hok'
    rw [hsp, packed]
    exact hpack
  · rintro t ⟨g', fr', w', hx, hok', hl', hm⟩ harg
    apply hX t ?_ harg
    refine ⟨g', fr' ++ [w', s.regs.rbx.toBitVec], ra.toBitVec, hx, hok', by simp [hl'], ?_⟩
    rw [stk2_free]
    change (View S g' ∗ Stk (rsp s - 16#64) fr' w' ∗ Fr s ra F).get t.dmem
    simpa only [rsp, Reg64s.get64_rsp, h.sp] using hm

theorem Bx.exitPost {t u : MachineData} (h : Bx S g (Extras s F) s ra w t)
    (hok : g.Ok) (exitra : Int64) {X : G → MachineData → Prop}
    (hm : u.dmem = t.dmem.storeInt (t.regs.rsp.toBitVec - 8#64) 8 exitra.toBitVec.toInt)
    (hx : X g u) : Sep.Post S F 4 X s u := by
  apply extras_post
  refine ⟨g, [exitra.toBitVec, s.regs.rbx.toBitVec], ra.toBitVec, hx, hok, rfl, ?_⟩
  rw [hm, stk2]
  change (View S g ∗ Stk (rsp s - 16#64) [] exitra.toBitVec ∗
    Fr s ra (Extras s F)).get
      (t.dmem.storeInt (t.regs.rsp.toBitVec - 8#64) 8 exitra.toBitVec.toInt)
  have hs := Generate.stk_store h.mem exitra.toBitVec
  simpa only [h.sp] using hs

-- A step that keeps the stack registers: the struct is now `g'`.
theorem Bx.step {t P : MachineData} {g' : G} (h : Bx S g F s ra w t)
    (hm : (View S g' ∗ Stk (rsp s - 16#64) [] w ∗ Fr s ra F).get P.dmem)
    (hsp : P.regs.rsp = t.regs.rsp) (hbx : P.regs.rbx = t.regs.rbx)
    (hbp : P.regs.rbp = t.regs.rbp) (h12 : P.regs.r12 = t.regs.r12)
    (h13 : P.regs.r13 = t.regs.r13) (h14 : P.regs.r14 = t.regs.r14)
    (h15 : P.regs.r15 = t.regs.r15) : Bx S g' F s ra w P :=
  ⟨hm, by rw [hsp]; exact h.sp, by rw [hbx]; exact h.bx, hbp.trans h.bp, h12.trans h.r12,
    h13.trans h.r13, h14.trans h.r14, h15.trans h.r15⟩

-- A step that keeps the memory and the stack registers.
theorem Bx.next {t P : MachineData} (h : Bx S g F s ra w t) (hm : P.dmem = t.dmem)
    (hsp : P.regs.rsp = t.regs.rsp) (hbx : P.regs.rbx = t.regs.rbx)
    (hbp : P.regs.rbp = t.regs.rbp) (h12 : P.regs.r12 = t.regs.r12)
    (h13 : P.regs.r13 = t.regs.r13) (h14 : P.regs.r14 = t.regs.r14)
    (h15 : P.regs.r15 = t.regs.r15) : Bx S g F s ra w P :=
  h.step (hm ▸ h.mem) hsp hbx hbp h12 h13 h14 h15

theorem Bx.stack {t : MachineData} (h : Bx S g F s ra w t) : t.StackAtOrBelow (s.pushRa ra) :=
  MachineData.stackAtOrBelow_of_toNat_lt (by
    rw [Reg64s.get64_rsp, Reg64s.get64_rsp, h.sp]
    simp only [MachineData.pushRa, rsp, Reg64s.get64_rsp, Reg64s.set64_rsp]
    bv_omega)

theorem Bx.isSome_bx {t : MachineData} (h : Bx S g F s ra w t) :
    (t.dmem.loadInt t.regs.rsp.toBitVec 8).isSome = true := by
  rw [h.sp]; exact isSome_of_eq _ h.mem (by unfold Fr; ecancel)

-- `popq %rbx`: the state `P` before the `ret` is a `Kp` state with 2 free words.
theorem Bx.pop {t P : MachineData} (h : Bx S g F s ra w t) (hm : P.dmem = t.dmem)
    (hsp : P.regs.rsp.toBitVec = t.regs.rsp.toBitVec + 8#64)
    (hbx : P.regs.rbx.toBitVec = rd t.dmem t.regs.rsp.toBitVec)
    (hbp : P.regs.rbp = t.regs.rbp)
    (h12 : P.regs.r12 = t.regs.r12) (h13 : P.regs.r13 = t.regs.r13)
    (h14 : P.regs.r14 = t.regs.r14) (h15 : P.regs.r15 = t.regs.r15) :
    Kp S g F s ra [w, s.regs.rbx.toBitVec] P where
  mem := by rw [hm, stk2]; exact h.mem
  sp := by
    apply UInt64.toBitVec_inj.mp
    rw [hsp, h.sp]
    show _ = rsp s - 8#64
    bv_omega
  bx := by
    apply UInt64.toBitVec_inj.mp
    rw [hbx, h.sp]
    exact rd_of_eq h.mem (by unfold Fr; ecancel)
  bp := hbp.trans h.bp
  r12 := h12.trans h.r12
  r13 := h13.trans h.r13
  r14 := h14.trans h.r14
  r15 := h15.trans h.r15

end

-- `m_size` of the struct at `S` in the state `t`: the variant of the loop.
def lenAt (S : Addr) (t : MachineData) : Nat :=
  (BitVec.ofInt 64 (t.dmem.loadInt (S + 32#64) 8).get!).toNat

theorem Bx.lenAt {S : Addr} {g : G} {F : MProp 64} {s : MachineData} {ra : Int64} {w : Word}
    {t : MachineData} (h : Bx S g F s ra w t) : lenAt S t = g.h.len.toNat := by
  unfold Surplus.lenAt; rw [rd_len' h.mem]

end FlatShuffler.Unit.Surplus
