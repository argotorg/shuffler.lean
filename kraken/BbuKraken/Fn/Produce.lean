import BbuKraken.Contracts
import BbuKraken.ModelLemmas
import BbuKraken.Kit

/-!
The body triple of `produce` (`c/bbu/produce.S`). The saved registers `rbx`,
`rbp`, `r12` and `r13` hold the struct, the offset `d`, the target value `v` of
`d` and the encoded copy of `v`. Every call is at `rsp s - 40`.
-/

open Std.WP Lean.Order
open scoped Program.WP

set_option experimental.vcgen true

namespace Bbu
namespace Produce

/-! ## Model lemmas -/

-- The part of `produce` after `emit`.
def tail (d : Nat) (st : St) : M St :=
  if positionOf st d ≠ some (st.len - 1) then .error .assertion
  else .ok { st with pending := st.pending - 1 }

theorem produce_eq (e : Env) (st : St) (d : Nat) : produce e st d = (emit e st d).bind (tail d) := rfl

-- No copy of `v` is in reach.
abbrev Far (st : St) (v : Word) : Prop := ∀ c, shallowestCopy st v = some c → 15 < st.len - 1 - c

section
variable {e : Env} {st : St} {d c : Nat}

theorem filter_none {v : Word} (hf : Far st v) :
    (shallowestCopy st v).filter (fun c => st.len - 1 - c ≤ MAX_DUP_DEPTH) = none := by
  cases hc : shallowestCopy st v with
  | none => rfl
  | some c => have := hf c hc; simp [MAX_DUP_DEPTH]; omega

theorem emit_zero (h : e.target[d]! = 0) : emit e st d = add st 0 d (.push 0) := by
  simp [emit, h]

theorem emit_dup (h0 : e.target[d]! ≠ 0) (hc : shallowestCopy st e.target[d]! = some c)
    (hb : st.len - 1 - c ≤ 15) : emit e st d = add st e.target[d]! d (.dup (st.len - c)) := by
  have hf : (shallowestCopy st e.target[d]!).filter (fun c => st.len - 1 - c ≤ MAX_DUP_DEPTH)
      = some c := by
    simp only [hc, Option.filter_some, MAX_DUP_DEPTH, hb, decide_true, ite_true]
  unfold emit
  simp only [h0, ite_false]
  rw [hf]

theorem emit_push (h0 : e.target[d]! ≠ 0) (hf : Far st e.target[d]!)
    (hp : (isFree e.target[d]! || isSpilled e e.target[d]!) = true) :
    emit e st d = add st e.target[d]! d (.push e.target[d]!) := by
  unfold emit
  simp only [h0, ite_false]
  rw [filter_none hf]
  simp only [hp, ite_true]

theorem emit_blocked (h0 : e.target[d]! ≠ 0) (hf : Far st e.target[d]!)
    (hp : (isFree e.target[d]! || isSpilled e e.target[d]!) = false)
    (hc : shallowestCopy st e.target[d]! = some c) :
    emit e st d = .error (.blocked c (st.len - 1 - c - 15)) := by
  unfold emit
  simp only [h0, ite_false]
  rw [filter_none hf]
  simp only [hp, hc, MAX_DUP_DEPTH]
  rfl

theorem emit_none (h0 : e.target[d]! ≠ 0)
    (hp : (isFree e.target[d]! || isSpilled e e.target[d]!) = false)
    (hc : shallowestCopy st e.target[d]! = none) : emit e st d = .error .assertion := by
  unfold emit
  simp only [h0, ite_false, hc, Option.filter_none, hp]
  rfl

theorem produce_err {e : Env} {st : St} {d : Nat} {x : Err} (h : emit e st d = .error x) :
    produce e st d = .error x := by
  rw [produce_eq, h]; rfl

theorem tail_bad {st : St} (h : positionOf st d ≠ some (st.len - 1)) :
    tail d st = .error .assertion := by
  simp [tail, h]

theorem tail_ok {st : St} (h : positionOf st d = some (st.len - 1)) :
    tail d st = .ok { st with pending := st.pending - 1 } := by
  simp [tail, h]

theorem pending_zero {st : St} (h : st.pending = 0) : { st with pending := st.pending - 1 } = st := by
  cases st; simp_all

end


section
variable {s : MachineData} {ra : Int64}

-- The saved words, the struct and the frame in the memory `m` of `produce`.
structure Fm (s : MachineData) (ra : Int64) (m : Mem 64) : Prop where
  ra : rd m (rsp s - 8#64) = ra.toBitVec
  r13 : rd m (rsp s - 16#64) = s.regs.r13.toBitVec
  r12 : rd m (rsp s - 24#64) = s.regs.r12.toBitVec
  rbp : rd m (rsp s - 32#64) = s.regs.rbp.toBitVec
  rbx : rd m (rsp s - 40#64) = s.regs.rbx.toBitVec
  wf : Wf m (rdi s)
  map : Mem.Mapped [frame 96 s] m
  un : Mem.UnchangedOutside (mod 96 s).mem s.dmem m

-- A change in the blocks of `produce` keeps the environment and the regions.
theorem keeps {m : Mem 64} (hpre : Pre 96 produceA s)
    (hu : Mem.UnchangedOutside (mod 96 s).mem s.dmem m) :
    envOf m (rdi s) = env s ∧ readable m (rdi s) = readable s.dmem (rdi s)
      ∧ writable m (rdi s) = writable s.dmem (rdi s) :=
  Post.env (t := { s with dmem := m }) hpre ⟨fun _ _ => rfl, hu⟩

-- The 8 bytes `k` bytes below `rsp s` lie in the frame.
theorem in_frame (_hle : 96 ≤ (rsp s).toNat) {k : Nat} (hk : 8 ≤ k) (hk' : k ≤ 96) :
    ∀ x, Mem.Blocks.Inside x 1 [(rsp s - BitVec.ofNat 64 k, 8)] →
      Mem.Blocks.Inside x 1 [frame 96 s] := by
  intro x hx
  simp only [Mem.Blocks.Inside, or_false] at hx ⊢
  bv_omega

-- The frame of a callee at `rsp s - 40` lies in the frame.
theorem callee_in_frame {c : MachineData} {G : Nat} (_hle : 96 ≤ (rsp s).toNat) (hG : G ≤ 56)
    (hrsp : rsp c = rsp s - 40#64) :
    ∀ x, Mem.Blocks.Inside x 1 [frame G c] → Mem.Blocks.Inside x 1 [frame 96 s] := by
  intro x hx
  simp only [Mem.Blocks.Inside, or_false, hrsp] at hx ⊢
  bv_omega

-- The saved words do not overlap the frame of a callee at `rsp s - 40`.
theorem saved_not_callee {c : MachineData} {G : Nat} (_hle : 96 ≤ (rsp s).toNat) (hG : G ≤ 56)
    (hrsp : rsp c = rsp s - 40#64) {k : Nat} (hk : 8 ≤ k) (hk' : k ≤ 40) :
    ∀ x, Mem.Blocks.Inside x 1 [(rsp s - BitVec.ofNat 64 k, 8)] →
      ¬ Mem.Blocks.Inside x 1 [frame G c] := by
  intro x hx hc
  simp only [Mem.Blocks.Inside, or_false, hrsp] at hx hc
  bv_omega

-- A callee at `rsp s - 40` keeps the saved words and the blocks of `produce`.
theorem Fm.call {m : Mem 64} {c t : MachineData} {G : Nat} {R : MachineData → MachineData → Prop}
    (hpre : Pre 96 produceA s) (h : Fm s ra m) (hG : G ≤ 56) (hc : c.dmem = m)
    (hrsp : rsp c = rsp s - 40#64) (hrdi : rdi c = rdi s) (hp : Post G R c t)
    (hag : (mod G c).Agree c t) : Fm s ra t.dmem := by
  have hfr := hpre.2.1
  have hle := hfr.le
  have hwr := (keeps hpre h.un).2.2
  have hu : Mem.UnchangedOutside (frame G c :: writable s.dmem (rdi s)) m t.dmem := by
    have := hag.2
    simp only [mod, hc, hrdi, hwr] at this
    exact this
  -- `writable` does not overlap the frame
  have hnw : ∀ x, Mem.Blocks.Inside x 1 [frame 96 s] →
      ¬ Mem.Blocks.Inside x 1 (writable s.dmem (rdi s)) :=
    fun x hx hw => hfr.disj x hx (inside_append.mpr (Or.inl hw))
  have hsv : ∀ {k}, 8 ≤ k → k ≤ 40 →
      rd t.dmem (rsp s - BitVec.ofNat 64 k) = rd m (rsp s - BitVec.ofNat 64 k) := fun hk hk' =>
    rd_congr hu fun x hx hl => by
      rcases hl with hl | hl
      · exact saved_not_callee hle hG hrsp hk hk' x hx (Or.inl hl)
      · exact hnw x (in_frame hle hk (by omega) x hx) hl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hsv (k := 8) (by omega) (by omega)]; exact h.ra
  · rw [hsv (k := 16) (by omega) (by omega)]; exact h.r13
  · rw [hsv (k := 24) (by omega) (by omega)]; exact h.r12
  · rw [hsv (k := 32) (by omega) (by omega)]; exact h.rbp
  · rw [hsv (k := 40) (by omega) (by omega)]; exact h.rbx
  · rw [← hrdi]; exact hp.1
  · intro x hx
    by_cases hx8 : Mem.Blocks.Inside x 1 [frame G c]
    · exact hp.2.1 x hx8
    · rw [hu x fun hl => hl.elim (fun hl => hx8 (Or.inl hl)) (hnw x hx)]
      exact h.map x hx
  · intro x hx
    have hx' : ¬ Mem.Blocks.Inside x 1 (frame G c :: writable s.dmem (rdi s)) := fun hl =>
      hl.elim (fun hl => hx (Or.inl (by
        have := callee_in_frame hle hG hrsp x (Or.inl hl)
        simpa only [Mem.Blocks.Inside, or_false] using this))) (fun hl => hx (Or.inr hl))
    rw [hu x hx']
    exact h.un x hx

-- The precondition of a callee at `rsp s - 40`.
theorem Fm.pre {m : Mem 64} {c : MachineData} {G : Nat} {A : MachineData → Prop}
    (hpre : Pre 96 produceA s) (h : Fm s ra m) (hG : G ≤ 56) (hc : c.dmem = m)
    (hrsp : rsp c = rsp s - 40#64) (hrdi : rdi c = rdi s) (hA : A c) : Pre G A c := by
  obtain ⟨-, hr, hwr⟩ := keeps hpre h.un
  refine ⟨by rw [hc, hrdi]; exact h.wf, ?_, hA⟩
  exact FrameOk.sub (k := 40) hpre.2.1 hpre.1 hrdi hrsp (by omega) (hc ▸ h.map) (hc ▸ hr)
    (hc ▸ hwr)

-- The return address slot of a callee at `rsp s - 40` is mapped.
theorem Fm.call_isSome {m : Mem 64} (hpre : Pre 96 produceA s) (h : Fm s ra m) :
    (m.loadInt (rsp s - 40#64 - 8#64) 8).isSome = true := by
  have hle := hpre.2.1.le
  refine Mem.Mapped.loadInt_isSome h.map (Or.inl ?_)
  bv_omega

-- A store to 8 bytes in `writable` that keeps the words 0 and 2 of the struct
-- keeps the saved words and the blocks of `produce`.
theorem Fm.store {m : Mem 64} {a : Addr} {v : Int} (hpre : Pre 96 produceA s) (h : Fm s ra m)
    (hin : ∀ x, Mem.Blocks.Inside x 1 [(a, 8)] → Mem.Blocks.Inside x 1 (writable s.dmem (rdi s)))
    (h0 : rd (m.storeInt a 8 v) (wordAt (rdi s) 0) = rd m (wordAt (rdi s) 0))
    (h2 : rd (m.storeInt a 8 v) (wordAt (rdi s) 2) = rd m (wordAt (rdi s) 2)) :
    Fm s ra (m.storeInt a 8 v) := by
  have hfr := hpre.2.1
  have hle := hfr.le
  obtain ⟨-, hrd, hwr⟩ := keeps hpre h.un
  have hu : Mem.UnchangedOutside [(a, 8)] m (m.storeInt a 8 v) :=
    .storeInt (fun _ _ => rfl) (Mem.Blocks.Inside.base (Nat.le_refl 8)) _
  have hnf : ∀ x, Mem.Blocks.Inside x 1 [frame 96 s] → ¬ Mem.Blocks.Inside x 1 [(a, 8)] :=
    fun x hx ha => hfr.disj x hx (inside_append.mpr (Or.inl (hin x ha)))
  have hsv : ∀ {k}, 8 ≤ k → k ≤ 96 →
      rd (m.storeInt a 8 v) (rsp s - BitVec.ofNat 64 k) = rd m (rsp s - BitVec.ofNat 64 k) :=
    fun hk hk' => rd_congr hu fun y hy hb => hnf y (in_frame hle hk hk' y hy) hb
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hsv (k := 8) (by omega) (by omega)]; exact h.ra
  · rw [hsv (k := 16) (by omega) (by omega)]; exact h.r13
  · rw [hsv (k := 24) (by omega) (by omega)]; exact h.r12
  · rw [hsv (k := 32) (by omega) (by omega)]; exact h.rbp
  · rw [hsv (k := 40) (by omega) (by omega)]; exact h.rbx
  · refine Wf.congr hu h.wf (fun y hy hb => hpre.disj y (hrd ▸ hy) (Or.inr (hin y hb))) ?_ ?_ ?_
    · exact fun y hy => (h.wf.mapped.storeInt _ _ _) y (inside_append.mpr (Or.inl hy))
    · rw [h0]; exact h.wf.len_le
    · rw [h2]; exact h.wf.nops_le
  · exact h.map.storeInt _ _ _
  · intro y hy
    rw [hu y fun hb => hy (Or.inr (hin y hb))]
    exact h.un y hy

end

/-! ## Normal forms of `kvcgen64` terms -/

section
variable {s : MachineData} {ra : Int64}
@[simp] theorem pushRa_rax : (s.pushRa ra).regs.rax = s.regs.rax := rfl
@[simp] theorem pushRa_rbx : (s.pushRa ra).regs.rbx = s.regs.rbx := rfl
@[simp] theorem pushRa_rcx : (s.pushRa ra).regs.rcx = s.regs.rcx := rfl
@[simp] theorem pushRa_rdx : (s.pushRa ra).regs.rdx = s.regs.rdx := rfl
@[simp] theorem pushRa_rsi : (s.pushRa ra).regs.rsi = s.regs.rsi := rfl
@[simp] theorem pushRa_rdi : (s.pushRa ra).regs.rdi = s.regs.rdi := rfl
@[simp] theorem pushRa_rbp : (s.pushRa ra).regs.rbp = s.regs.rbp := rfl
@[simp] theorem pushRa_r8 : (s.pushRa ra).regs.r8 = s.regs.r8 := rfl
@[simp] theorem pushRa_r12 : (s.pushRa ra).regs.r12 = s.regs.r12 := rfl
@[simp] theorem pushRa_r13 : (s.pushRa ra).regs.r13 = s.regs.r13 := rfl
@[simp] theorem pushRa_r14 : (s.pushRa ra).regs.r14 = s.regs.r14 := rfl
@[simp] theorem pushRa_r15 : (s.pushRa ra).regs.r15 = s.regs.r15 := rfl
theorem pushRa_rsp : (s.pushRa ra).regs.rsp.toBitVec = rsp s - 8#64 := by simp [MachineData.pushRa]

-- The memory after the pushes of the entry block, as `kvcgen64` gives it.
def pushes (s : MachineData) (ra : Int64) : Mem 64 :=
  let t := s.pushRa ra
  let R := t.regs.rsp.toBitVec
  (((t.dmem.storeInt (R - 8#64) 8 t.regs.r13.toBitVec.toInt).storeInt
    (R - 8#64 - 8#64) 8 t.regs.r12.toBitVec.toInt).storeInt
    (R - 8#64 - 8#64 - 8#64) 8 t.regs.rbp.toBitVec.toInt).storeInt
    (R - 8#64 - 8#64 - 8#64 - 8#64) 8 t.regs.rbx.toBitVec.toInt

theorem pushes_eq : (((Mem.storeInt (s.pushRa ra).dmem ((s.pushRa ra).regs.rsp.toBitVec - 8#64) 8
    (s.pushRa ra).regs.r13.toBitVec.toInt).storeInt
    ((s.pushRa ra).regs.rsp.toBitVec - 8#64 - 8#64) 8 (s.pushRa ra).regs.r12.toBitVec.toInt).storeInt
    ((s.pushRa ra).regs.rsp.toBitVec - 8#64 - 8#64 - 8#64) 8
      (s.pushRa ra).regs.rbp.toBitVec.toInt).storeInt
    ((s.pushRa ra).regs.rsp.toBitVec - 8#64 - 8#64 - 8#64 - 8#64) 8
      (s.pushRa ra).regs.rbx.toBitVec.toInt = pushes s ra := rfl
end

-- The displacement `8 * k` of a word in a struct.
theorem disp (a : Addr) (k : Nat) (i : Int64) (h : i.toInt = 8 * k := by decide) :
    a + BitVec.ofInt 64 i.toInt = wordAt a k := by
  rw [h, show (8 * (k : Int)) = ((8 * k : Nat) : Int) by omega, BitVec.ofInt_natCast]
@[simp] theorem disp0 (a : Addr) : a + BitVec.ofInt 64 (Int64.toInt 0) = wordAt a 0 := disp a 0 0
@[simp] theorem disp1 (a : Addr) : a + BitVec.ofInt 64 (Int64.toInt 8) = wordAt a 1 := disp a 1 8
@[simp] theorem disp4 (a : Addr) : a + BitVec.ofInt 64 (Int64.toInt 32) = wordAt a 4 := disp a 4 32
@[simp] theorem disp7 (a : Addr) : a + BitVec.ofInt 64 (Int64.toInt 56) = wordAt a 7 := disp a 7 56

/-! ## The entry block -/

section
variable {s : MachineData} {ra : Int64}

theorem unchanged_pushes : Mem.UnchangedOutside [frame 96 s] s.dmem (pushes s ra) := by
  have hin : ∀ a : Addr, (a - (rsp s - BitVec.ofNat 64 96)).toNat + 8 ≤ 96 →
      Mem.Blocks.Inside a 8 [frame 96 s] := fun a h => Or.inl h
  simp only [pushes, MachineData.dmem_pushRa, pushRa_rsp]
  refine .storeInt (.storeInt (.storeInt (.storeInt (.storeInt
    (fun _ _ => rfl) (hin _ ?_) _) (hin _ ?_) _) (hin _ ?_) _) (hin _ ?_) _) (hin _ ?_) _
  all_goals (simp only [rsp] at *; bv_omega)

theorem fm_pushes (hpre : Pre 96 produceA s) : Fm s ra (pushes s ra) := by
  have hle := hpre.2.1.le
  have hu := unchanged_pushes (s := s) (ra := ra)
  have hd := disjoint_symm hpre.2.1.disj
  refine ⟨?_, ?_, ?_, ?_, ?_, Wf.congr_of_disjoint hu hpre.1 hd, ?_, ?_⟩
  all_goals try simp only [pushes, pushRa_rsp, MachineData.dmem_pushRa]
  · rw [rd_store_other, rd_store_other, rd_store_other, rd_store_other, rd_store_same,
      BitVec.ofInt_toInt]
    all_goals first | rfl | bv_omega
  · rw [rd_store_other, rd_store_other, rd_store_other, rd_store_same, BitVec.ofInt_toInt]
    all_goals first | rfl | bv_omega
  · rw [rd_store_other, rd_store_other, rd_store_same, BitVec.ofInt_toInt]
    all_goals first | rfl | bv_omega
  · rw [rd_store_other, rd_store_same, BitVec.ofInt_toInt]
    all_goals first | rfl | bv_omega
  · rw [rd_store_same, BitVec.ofInt_toInt]
    all_goals first | rfl | bv_omega
  · exact hpre.2.1.mapped.storeInt _ _ _ |>.storeInt _ _ _ |>.storeInt _ _ _ |>.storeInt _ _ _
      |>.storeInt _ _ _
  · intro x hx
    exact hu x fun h => hx (Or.inl (h.elim id False.elim))

theorem st_pushes (hpre : Pre 96 produceA s) : stOf (pushes s ra) (rdi s) = st s :=
  stOf_congr unchanged_pushes hpre.1 (disjoint_symm hpre.2.1.disj)

end

/-! ## The struct in memory -/

section
variable {m : Mem 64} {S : Addr}

theorem env_n : (envOf m S).n = nOf m S := by
  simp [Env.n, envOf]

theorem target_get {d : Nat} (hd : d < nOf m S) :
    (envOf m S).target[d]! = rd m (wordAt (tgtOf m S) d) := by
  simp [envOf, hd]

theorem st_len : (stOf m S).len = (rd m (wordAt S 0)).toNat := by
  simp [St.len, stOf]

theorem st_pending : (stOf m S).pending = (rd m (wordAt S 1)).toNat := rfl

theorem wordAt_mul (a x : Word) : wordAt a x.toNat = a + x * 8#64 := by
  simp only [wordAt]
  bv_omega

-- The load of the target value at the offset `x`.
theorem rd_target {x : Word} (hx : x.toNat < nOf m S) :
    rd m (wordAt (rd m (wordAt S 4) + x * 8#64) 0) = (envOf m S).target[x.toNat]! := by
  have := Nat.lt_of_lt_of_le hx (Nat.le_refl _)
  rw [target_get hx, tgtOf]
  congr 1
  simp only [wordAt, nOf] at *
  bv_omega

theorem hdr_isSome (hw : Wf m S) {k : Nat} (hk : k < 8) :
    (m.loadInt (wordAt S k) 8).isSome = true := by
  have hs := hw.struct_lt
  simp only [WORDS_eq] at hs
  refine Mem.Mapped.loadInt_isSome hw.mapped (inside_append.mpr ?_)
  by_cases hk3 : k < 3
  · exact Or.inl (Or.inl (by simp only [wordAt]; bv_omega))
  · exact Or.inr (Or.inl (by simp only [wordAt]; bv_omega))

theorem tgt_isSome (hw : Wf m S) {d : Nat} (hd : d < nOf m S) :
    (m.loadInt (wordAt (tgtOf m S) d) 8).isSome = true := by
  have := hw.tgt_lt
  refine Mem.Mapped.loadInt_isSome hw.mapped (inside_append.mpr (Or.inr (Or.inr (Or.inl ?_))))
  simp only [wordAt]; bv_omega

-- A store to the word `pending` sets `pending`.
theorem stOf_setPending (hw : Wf m S) (x : Word) :
    stOf (m.storeInt (wordAt S 1) 8 x.toInt) S = { stOf m S with pending := x.toNat } := by
  have hs := hw.struct_lt
  have hn : _ ≤ 1024 := hw.n_le
  simp only [WORDS_eq] at hs
  have hk : ∀ k, k < 2056 → k ≠ 1 →
      rd (m.storeInt (wordAt S 1) 8 x.toInt) (wordAt S k) = rd m (wordAt S k) := fun k hk h1 =>
    rd_store_other _ (by simp only [wordAt]; bv_omega)
  have hop : ∀ j, j < 12 * nOf m S →
      rd (m.storeInt (wordAt S 1) 8 x.toInt) (wordAt (opsOf m S) j) = rd m (wordAt (opsOf m S) j) :=
    fun j hj => rd_storeInt_of_disjoint fun y hy ho => hw.disj_struct y
      (by simp only [Mem.Blocks.Inside, or_false, WORDS_eq] at hy ⊢; bv_omega)
      (Or.inl (by simp only [Mem.Blocks.Inside, or_false] at ho ⊢; bv_omega))
  have hlen : _ ≤ 1024 := hw.len_le
  have hnops := hw.nops_le
  have ho : opsOf (m.storeInt (wordAt S 1) 8 x.toInt) S = opsOf m S := hk 6 (by omega) (by omega)
  simp only [stOf, hk 0 (by omega) (by omega), hk 2 (by omega) (by omega),
    rd_store_same _ rfl, BitVec.ofInt_toInt]
  congr 1
  · refine List.map_congr_left fun i hi => ?_
    have := List.mem_range.mp hi
    simp only [slotOf, STACK, DEST_eq, hk (8 + i) (by omega) (by omega),
      hk (1032 + i) (by omega) (by omega)]
  · refine List.map_congr_left fun i hi => ?_
    have := List.mem_range.mp hi
    simp only [opOf, ho, hop (2 * i) (by omega), hop (2 * i + 1) (by omega)]

end

theorem positionOf_lt {st : St} {d p : Nat} (h : positionOf st d = some p) : p < st.len := by
  simp only [positionOf, List.findIdx?_eq_some_iff_getElem] at h
  exact h.1

theorem shallowestCopy_lt {st : St} {v : Word} {c : Nat} (h : shallowestCopy st v = some c) :
    c < st.len := by
  simpa using List.mem_reverse.mp (List.mem_of_find?_eq_some h)

/-! ## The `blocked` stores -/

section
variable {s : MachineData} {ra : Int64}

theorem blkOf_def {m : Mem 64} {S : Addr} : rd m (wordAt S 7) = blkOf m S := rfl

-- A word of the struct does not overlap `blocked`.
theorem blk_disj {m : Mem 64} {S : Addr} (hw : Wf m S) {k : Nat} (hk : k < WORDS) :
    Mem.Blocks.Disjoint [(wordAt S k, 8)] [(blkOf m S, 16)] := by
  intro x hx hb
  have hs := hw.struct_lt
  simp only [WORDS_eq] at hs hk
  refine hw.disj_struct x ?_ (inside_of_mem (by simp) hb)
  simp only [Mem.Blocks.Inside, or_false, WORDS_eq] at hx ⊢
  bv_omega

-- A store to `blocked` keeps the pointer to it.
theorem blkOf_store {m : Mem 64} {S : Addr} {v : Int} (hw : Wf m S) {k : Nat} (hk : k < 2) :
    blkOf (m.storeInt (wordAt (blkOf m S) k) 8 v) S = blkOf m S := by
  have hb := hw.blk_lt
  refine rd_storeInt_of_disjoint fun x hx hy => blk_disj hw (k := 7) (by decide) x hy ?_
  simp only [Mem.Blocks.Inside, or_false] at hx ⊢
  bv_omega

theorem blk_isSome {m m' : Mem 64} {S : Addr} (hw : Wf m S)
    (hm : Mem.Mapped (writable m S ++ readable m S) m') {k : Nat} (hk : k < 2) :
    (m'.loadInt (wordAt (blkOf m S) k) 8).isSome = true := by
  have hb := hw.blk_lt
  refine Mem.Mapped.loadInt_isSome hm (inside_append.mpr (Or.inl
    (inside_of_mem (p := (blkOf m S, 16)) (by simp [writable]) (Or.inl ?_))))
  simp only [wordAt]; bv_omega

theorem hdr_isSome' {m m' : Mem 64} {S : Addr} (hw : Wf m S)
    (hm : Mem.Mapped (writable m S ++ readable m S) m') {k : Nat} (hk : k < 8) :
    (m'.loadInt (wordAt S k) 8).isSome = true := by
  have hs := hw.struct_lt
  simp only [WORDS_eq] at hs
  refine Mem.Mapped.loadInt_isSome hm (inside_append.mpr ?_)
  by_cases hk3 : k < 3
  · exact Or.inl (Or.inl (by simp only [wordAt]; bv_omega))
  · exact Or.inr (Or.inl (by simp only [wordAt]; bv_omega))

-- The two stores to `blocked` keep the frame and the struct.
theorem Fm.blk {m : Mem 64} (hpre : Pre 96 produceA s) (h : Fm s ra m) (p x : Word) :
    Fm s ra ((m.storeInt (wordAt (blkOf m (rdi s)) 0) 8 p.toInt).storeInt
      (wordAt (blkOf m (rdi s)) 1) 8 x.toInt) := by
  have hfr := hpre.2.1
  have hle := hfr.le
  have hbl := h.wf.blk_lt
  obtain ⟨-, hrd, hwr⟩ := keeps hpre h.un
  generalize hB : blkOf m (rdi s) = B at hbl ⊢
  have hu : Mem.UnchangedOutside [(B, 16)] m
      ((m.storeInt (wordAt B 0) 8 p.toInt).storeInt (wordAt B 1) 8 x.toInt) := by
    have hin : ∀ a : Addr, (a - B).toNat + 8 ≤ 16 → Mem.Blocks.Inside a 8 [(B, 16)] :=
      fun a h => Or.inl h
    refine .storeInt (.storeInt (fun _ _ => rfl) (hin _ ?_) _) (hin _ ?_) _
    all_goals (simp only [wordAt]; bv_omega)
  -- `blocked` lies in `writable`
  have hw : ∀ y, Mem.Blocks.Inside y 1 [(B, 16)] → Mem.Blocks.Inside y 1 (writable s.dmem (rdi s)) :=
    fun y hy => hwr ▸ inside_of_mem (by rw [← hB]; simp [writable]) hy
  have hnw : ∀ y, Mem.Blocks.Inside y 1 [frame 96 s] → ¬ Mem.Blocks.Inside y 1 [(B, 16)] :=
    fun y hy hb => hfr.disj y hy (inside_append.mpr (Or.inl (hw y hb)))
  have hsv : ∀ {k}, 8 ≤ k → k ≤ 96 →
      rd ((m.storeInt (wordAt B 0) 8 p.toInt).storeInt (wordAt B 1) 8 x.toInt)
        (rsp s - BitVec.ofNat 64 k) = rd m (rsp s - BitVec.ofNat 64 k) := fun hk hk' =>
    rd_congr hu fun y hy hb => hnw y (in_frame hle hk hk' y hy) hb
  have hst : ∀ {k}, k < WORDS →
      rd ((m.storeInt (wordAt B 0) 8 p.toInt).storeInt (wordAt B 1) 8 x.toInt)
        (wordAt (rdi s) k) = rd m (wordAt (rdi s) k) := fun hk =>
    rd_congr hu (hB ▸ blk_disj h.wf hk)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hsv (k := 8) (by omega) (by omega)]; exact h.ra
  · rw [hsv (k := 16) (by omega) (by omega)]; exact h.r13
  · rw [hsv (k := 24) (by omega) (by omega)]; exact h.r12
  · rw [hsv (k := 32) (by omega) (by omega)]; exact h.rbp
  · rw [hsv (k := 40) (by omega) (by omega)]; exact h.rbx
  · refine Wf.congr hu h.wf (fun y hy hb => hpre.disj y (hrd ▸ hy) (Or.inr (hw y hb))) ?_ ?_ ?_
    · exact fun y hy =>
        (h.wf.mapped.storeInt _ _ _ |>.storeInt _ _ _) y (inside_append.mpr (Or.inl hy))
    · rw [hst (by decide)]; exact h.wf.len_le
    · rw [hst (by decide)]; exact h.wf.nops_le
  · exact h.map.storeInt _ _ _ |>.storeInt _ _ _
  · intro y hy
    rw [hu y fun hb => hy (Or.inr (hw y hb))]
    exact h.un y hy

end

/-! ## The return -/

section
variable {s : MachineData} {ra : Int64}

-- The pops of `.LB26` read the saved words.
theorem Fm.pops {m : Mem 64} (h : Fm s ra m) {a : Addr} (ha : a = rsp s - 40#64) :
    rd m a = s.regs.rbx.toBitVec ∧ rd m (a + 8#64) = s.regs.rbp.toBitVec
      ∧ rd m (a + 8#64 + 8#64) = s.regs.r12.toBitVec
      ∧ rd m (a + 8#64 + 8#64 + 8#64) = s.regs.r13.toBitVec := by
  subst ha
  refine ⟨h.rbx, ?_, ?_, ?_⟩
  · rw [show rsp s - 40#64 + 8#64 = rsp s - 32#64 by bv_omega]; exact h.rbp
  · rw [show rsp s - 40#64 + 8#64 + 8#64 = rsp s - 24#64 by bv_omega]; exact h.r12
  · rw [show rsp s - 40#64 + 8#64 + 8#64 + 8#64 = rsp s - 16#64 by bv_omega]; exact h.r13

theorem retAddr_of {u : MachineData} (hpre : Pre 96 produceA s) (hm : Fm s ra u.dmem)
    (hsp : u.regs.get64 .rsp = rsp s - 8#64) : u.retAddr = some ra := by
  have hle := hpre.2.1.le
  have hs : (u.dmem.loadInt (rsp s - 8#64) 8).isSome = true :=
    Mem.Mapped.loadInt_isSome hm.map (Or.inl (by bv_omega))
  have hr := hm.ra
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp hs
  rw [rd, hi, Option.get!_some] at hr
  rw [MachineData.retAddr, hsp, hi, Option.map_some, hr, Int64.ofBitVec_toBitVec]

-- `ret` from the state `u` gives the postcondition.
theorem ret [Host] {ls : List Label} {I' : CfgLabel → Nat → Unit → MachineData → Prop}
    {u : MachineData} (hpre : Pre 96 produceA s) (hm : Fm s ra u.dmem)
    (hsp : u.regs.get64 .rsp = rsp s - 8#64)
    (hr : ∀ q, q ∉ [Reg64.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11, .rsp] →
      u.regs.get64 q = s.regs.get64 q)
    (hR : ∀ t', t'.dmem = u.dmem → rax t' = rax u → produceR s t') :
    Program.Intercept ls (s.pushRa ra) I'
      (fun a t => a = ra ∧ Post produceF produceR s t ∧ (mod produceF s).Agree s t) u.retAddr.get!
      { regs := u.regs.set64 Reg64.rsp (u.regs.get64 Reg64.rsp + 8#64), zmms := u.zmms,
        status := u.status, dmem := u.dmem } := by
  have hra := retAddr_of hpre hm hsp
  refine Or.inr ⟨⟨by simp [hra], ⟨hm.wf, hm.map, hR _ rfl (by simp [rax])⟩,
    fun q hq => ?_, hm.un⟩, fun _ _ _ => ?_⟩
  · simp only [Reg64s.get64_set64]
    split
    · subst_vars; rw [hsp, BitVec.sub_add_cancel]
    · exact hr q (by simp_all [mod, produceF])
  · apply MachineData.stackBelow_of_add_eight
    simp [MachineData.pushRa, hsp]
    bv_omega
end


-- `produceR` depends on `rax` and the memory.
theorem produceR_congr {s t t' : MachineData} (hm : t'.dmem = t.dmem) (hax : rax t' = rax t)
    (h : produceR s t) : produceR s t' := by
  unfold produceR Res at *
  generalize produce (env s) (st s) (rsi s).toNat = r at *
  rcases r with (⟨p, x⟩ | _) | a
  · exact ⟨hax.trans h.1, hm ▸ h.2.1, hm ▸ h.2.2⟩
  · exact hax.trans h
  · exact ⟨hax.trans h.1, by simp only [st', hm]; exact h.2⟩

section
variable (s : MachineData) (ra : Int64)

-- The offset `d`, its target value `v` and the copy of `v`.
abbrev dd : Nat := (rsi s).toNat
abbrev vv : Word := (env s).target[(rsi s).toNat]!
abbrev cp : Option Nat := shallowestCopy (st s) (vv s)

-- The frame and the registers that `produce` does not change.
structure Base (t : MachineData) : Prop where
  fm : Fm s ra t.dmem
  rsp : t.regs.rsp.toBitVec = rsp s - 40#64
  r14 : t.regs.r14.toBitVec = s.regs.r14.toBitVec
  r15 : t.regs.r15.toBitVec = s.regs.r15.toBitVec

-- Before `emit`: the struct in `rbx`, `d` in `rbp`, `v` in `r12` and the copy in `r13`.
structure Lp (t : MachineData) : Prop extends Base s ra t where
  st : stOf t.dmem (rdi s) = st s
  rbx : t.regs.rbx.toBitVec = rdi s
  rbp : t.regs.rbp.toBitVec = rsi s
  r12 : t.regs.r12.toBitVec = vv s
  r13 : t.regs.r13.toBitVec = encOpt (cp s)
  v0 : vv s ≠ 0

-- `.LB29`: no copy is in reach.
def At29 (t : MachineData) : Prop := Lp s ra t ∧ Far (st s) (vv s)
-- `.LB37`: `v` is not free.
def At37 (t : MachineData) : Prop := At29 s ra t ∧ isFree (vv s) = false
-- `.LB30`: `emit` pushes `v`.
def At30 (t : MachineData) : Prop :=
  At29 s ra t ∧ (isFree (vv s) || isSpilled (env s) (vv s)) = true
-- `.LB32`: `emit` fails.
def At32 (t : MachineData) : Prop :=
  At29 s ra t ∧ (isFree (vv s) || isSpilled (env s) (vv s)) = false
-- `.LB40`: `emit` dups the copy `c`; `r8` is the depth.
def At40 (t : MachineData) : Prop :=
  Lp s ra t ∧ ∃ c, cp s = some c ∧ (st s).len - 1 - c ≤ 15
    ∧ t.regs.r8.toBitVec = BitVec.ofNat 64 ((st s).len - c)
-- `.LB39`: `v` is 0.
def At39 (t : MachineData) : Prop :=
  Base s ra t ∧ stOf t.dmem (rdi s) = st s ∧ t.regs.rbx.toBitVec = rdi s
    ∧ t.regs.rbp.toBitVec = rsi s ∧ t.regs.rdi.toBitVec = rdi s ∧ t.regs.rsi.toBitVec = rsi s
    ∧ vv s = 0
-- `.LB28`: `emit` is the `add` that returned.
def At28 (t : MachineData) : Prop :=
  Base s ra t ∧ t.regs.rbx.toBitVec = rdi s ∧ t.regs.rbp.toBitVec = rsi s
    ∧ ∃ v op, emit (env s) (st s) (dd s) = add (st s) v (dd s) op
      ∧ Res (rdi s) (add (st s) v (dd s) op) (fun st' => rax t = 0#64 ∧ stOf t.dmem (rdi s) = st') t
-- `.LB34` and `.LB35`: `produce` fails an assertion.
def Asrt (t : MachineData) : Prop :=
  Base s ra t ∧ produce (env s) (st s) (dd s) = .error .assertion
-- `.LB26`: the result.
def At26 (t : MachineData) : Prop := Base s ra t ∧ produceR s t

def V : Label → MachineData → Nat
  | ".LB26", _ => 0
  | ".LB34", _ | ".LB35", _ => 1
  | ".LB28", _ => 2
  | _, _ => 3

theorem V_eq3 (t u : MachineData) : V ".LB29" t = V "produce" u := rfl
theorem V_eq40 (t u : MachineData) : V ".LB40" t = V "produce" u := rfl

end

-- The flags of `testb $1` and `cmpq $1` at `.LB29`.
theorem take_and1 (v : Word) : (v.take 8 &&& 1#8).toNat = v.toNat % 2 := by
  unfold BitVec.take
  rw [BitVec.toNat_and, BitVec.extractLsb'_toNat]
  simp

theorem isFree_even {v : Word} (h0 : v ≠ 0) (h : v.take 8 &&& 1#8 = 0#8) : isFree v = false := by
  have he : v.toNat % 2 = 0 := by rw [← take_and1, h]; rfl
  have h0' : ¬v = 0#64 := h0
  simp [isFree, he, h0']

theorem isFree_odd {v : Word} (h : ¬v.take 8 &&& 1#8 = 0#8) (h1 : ¬v - 1#64 = 0#64) :
    isFree v = true := by
  have ho : v.toNat % 2 = 1 := by
    have : (v.take 8 &&& 1#8).toNat ≠ 0 := fun h' => h (BitVec.eq_of_toNat_eq (by rw [h']; rfl))
    rw [take_and1] at this
    omega
  have h1' : v ≠ 1#64 := by bv_omega
  simp [isFree, ho, h1']

theorem isFree_one {v : Word} (h1 : v - 1#64 = 0#64) : isFree v = false := by
  have : v = 1#64 := by bv_omega
  subst this; decide

/-! ## `.LB32` -/

section
variable {m : Mem 64} {S : Addr}

theorem wordAt_zero (a : Addr) : wordAt a 0 = a := by simp [wordAt]

-- A store to `blocked` keeps the words of the struct.
theorem rd_blk_store {M : Mem 64} (hw : Wf m S) {k j : Nat} (hk : k < WORDS) (hj : j < 2)
    (v : Int) : rd (M.storeInt (wordAt (blkOf m S) j) 8 v) (wordAt S k) = rd M (wordAt S k) := by
  have hb := hw.blk_lt
  refine rd_storeInt_of_disjoint fun x hx hy => blk_disj hw hk x hy ?_
  simp only [Mem.Blocks.Inside, or_false] at hx ⊢
  bv_omega

theorem blk_ptr_store (hw : Wf m S) (v : Int) :
    rd (m.storeInt (rd m (S + 56#64)) 8 v) (S + 56#64) = blkOf m S := by
  have h := rd_blk_store (M := m) hw (k := 7) (j := 0) (by decide) (by decide) v
  rw [wordAt_zero] at h
  exact h

-- The two stores of `.LB32`.
def blkStores (m : Mem 64) (S : Addr) (p x : Word) : Mem 64 :=
  (m.storeInt (wordAt (blkOf m S) 0) 8 p.toInt).storeInt (wordAt (blkOf m S) 1) 8 x.toInt

theorem blkStores_eq (hw : Wf m S) (p x : Word) :
    (m.storeInt (rd m (S + 56#64)) 8 p.toInt).storeInt
      (rd (m.storeInt (rd m (S + 56#64)) 8 p.toInt) (S + 56#64) + 8#64) 8 x.toInt
      = blkStores m S p x := by
  rw [blk_ptr_store hw, blkStores, wordAt_zero]
  rfl

theorem blkStores_rd (hw : Wf m S) (p x : Word) :
    rd (blkStores m S p x) (blkOf (blkStores m S p x) S) = p
      ∧ rd (blkStores m S p x) (wordAt (blkOf (blkStores m S p x) S) 1) = x := by
  have hb := hw.blk_lt
  have hB : blkOf (blkStores m S p x) S = blkOf m S := by
    show rd (blkStores m S p x) (wordAt S 7) = _
    unfold blkStores
    rw [rd_blk_store hw (by decide) (by decide), rd_blk_store hw (by decide) (by decide)]
    rfl
  rw [hB]
  unfold blkStores
  constructor
  · rw [rd_store_other, rd_store_same _ (wordAt_zero _), BitVec.ofInt_toInt]
    simp only [wordAt]; bv_omega
  · rw [rd_store_same _ rfl, BitVec.ofInt_toInt]

theorem blk_isSome0 (hw : Wf m S) : (m.loadInt (rd m (S + 56#64)) 8).isSome = true := by
  have h := blk_isSome hw hw.mapped (k := 0) (by decide)
  rw [wordAt_zero] at h
  exact h

theorem blk_isSome1 (hw : Wf m S) (v : Int) :
    ((m.storeInt (rd m (S + 56#64)) 8 v).loadInt
      (rd (m.storeInt (rd m (S + 56#64)) 8 v) (S + 56#64) + 8#64) 8).isSome = true := by
  rw [blk_ptr_store hw]
  exact blk_isSome hw (hw.mapped.storeInt _ _ _) (k := 1) (by decide)

theorem hdr_isSome0 (hw : Wf m S) : (m.loadInt S 8).isSome = true := by
  have h := hdr_isSome hw (k := 0) (by decide)
  rw [wordAt_zero] at h
  exact h

end

theorem msb_test (v : Word) (r) :
    CondCode.s.interp (StatusFlags.from_result (v &&& v) r) = v.msb := by
  simp [CondCode.interp, StatusFlags.from_result]

theorem encOpt_msb {c : Nat} (h : c < 1024) : (encOpt (some c)).msb = false := by
  rw [encOpt, BitVec.msb_eq_decide]
  simp only [BitVec.toNat_ofNat, decide_eq_false_iff_not, Nat.not_le]
  omega

/-! ## Calls -/

section
variable {s : MachineData} {ra : Int64}

theorem Res.mono {α : Type} {S : Addr} {r : M α} {Q Q' : α → Prop} {t : MachineData}
    (h : ∀ a, Q a → Q' a) (hr : Res S r Q t) : Res S r Q' t := by
  unfold Res at *
  rcases r with (⟨p, x⟩ | _) | a
  · exact hr
  · exact hr
  · exact h a hr

theorem Res.msb {α : Type} {S : Addr} {e : Err} {Q : α → Prop} {t : MachineData}
    (h : Res S (.error e : M α) Q t) : (rax t).msb = true := by
  cases e with
  | blocked p x => rw [show rax t = -1#64 from h.1]; decide
  | assertion => rw [show rax t = -2#64 from h]; decide

theorem Res.err {α β : Type} {S : Addr} {e : Err} {Q : α → Prop} {Q' : β → Prop} {t : MachineData}
    (h : Res S (.error e : M α) Q t) : Res S (.error e : M β) Q' t := by
  cases e <;> exact h

-- A callee keeps a register that it may not change.
theorem keep {G : Nat} {c u : MachineData} (hag : (mod G c).Agree c u) (r : Reg64)
    (hr : r ∉ (mod G c).regs := by simp [mod]) : u.regs.get64 r = c.regs.get64 r :=
  hag.1 r hr

theorem Base.call_isSome {t : MachineData} (hpre : Pre 96 produceA s) (hb : Base s ra t) :
    (t.dmem.loadInt (t.regs.rsp.toBitVec - 8#64) 8).isSome = true := by
  rw [hb.rsp]; exact Fm.call_isSome hpre hb.fm

-- The precondition of a call from `t` to a callee with frame size `G`.
theorem Base.pre {t c : MachineData} {G : Nat} {A : MachineData → Prop} (hpre : Pre 96 produceA s)
    (hb : Base s ra t) (hG : G ≤ 56) (hc : c.dmem = t.dmem) (hrsp : c.regs.rsp = t.regs.rsp)
    (hrdi : rdi c = rdi s) (hA : A c) : Pre G A c :=
  Fm.pre hpre hb.fm hG hc (by simp only [Reg64s.get64_rsp, hrsp]; exact hb.rsp) hrdi hA

-- The state `u` after a call from `t`.
theorem Base.call {t c u : MachineData} {G : Nat} {R : MachineData → MachineData → Prop}
    (hpre : Pre 96 produceA s) (hb : Base s ra t) (hp : Post G R c u)
    (hag : (mod G c).Agree c u) (hG : G ≤ 56) (hc : c.dmem = t.dmem)
    (hrsp : c.regs.rsp = t.regs.rsp) (h14 : c.regs.r14 = t.regs.r14)
    (h15 : c.regs.r15 = t.regs.r15) (hrdi : rdi c = rdi s) : Base s ra u where
  fm := Fm.call hpre hb.fm hG hc (by simp only [Reg64s.get64_rsp, hrsp]; exact hb.rsp) hrdi hp hag
  rsp := by
    have := keep hag .rsp
    simp only [Reg64s.get64_rsp, hrsp] at this
    rw [this]; exact hb.rsp
  r14 := by
    have := keep hag .r14
    simp only [Reg64s.get64_r14, h14] at this
    rw [this]; exact hb.r14
  r15 := by
    have := keep hag .r15
    simp only [Reg64s.get64_r15, h15] at this
    rw [this]; exact hb.r15

theorem Fm.n {m : Mem 64} (hpre : Pre 96 produceA s) (h : Fm s ra m) :
    nOf m (rdi s) = nOf s.dmem (rdi s) := by
  have := congrArg Env.n (keeps hpre h.un).1
  rwa [env_n, env_n] at this

theorem Fm.addA {m : Mem 64} {c : MachineData} (hpre : Pre 96 produceA s) (h : Fm s ra m)
    (hc : c.dmem = m) (hrdi : rdi c = rdi s) (hst : stOf m (rdi s) = st s) : addA c := by
  have hn := h.n hpre
  obtain ⟨-, -, -, hl, ho⟩ := hpre
  show (stOf c.dmem (rdi c)).len < 1024 ∧ (stOf c.dmem (rdi c)).ops.length < 6 * nOf c.dmem (rdi c)
  rw [hc, hrdi, hst, hn]
  exact ⟨hl, ho⟩

-- A call that keeps the model state keeps `Lp`.
theorem Lp.call {t c u : MachineData} {G : Nat} {R : MachineData → MachineData → Prop}
    (hpre : Pre 96 produceA s) (hl : Lp s ra t) (hp : Post G R c u)
    (hag : (mod G c).Agree c u) (hG : G ≤ 56) (hc : c.dmem = t.dmem)
    (hrsp : c.regs.rsp = t.regs.rsp) (h14 : c.regs.r14 = t.regs.r14)
    (h15 : c.regs.r15 = t.regs.r15) (hrbx : c.regs.rbx = t.regs.rbx)
    (hrbp : c.regs.rbp = t.regs.rbp) (h12 : c.regs.r12 = t.regs.r12)
    (h13 : c.regs.r13 = t.regs.r13) (hrdi : rdi c = rdi s)
    (hst : stOf u.dmem (rdi s) = Bbu.st s) : Lp s ra u where
  toBase := hl.toBase.call hpre hp hag hG hc hrsp h14 h15 hrdi
  st := hst
  rbx := by
    have := keep hag .rbx
    simp only [Reg64s.get64_rbx, hrbx] at this
    rw [this]; exact hl.rbx
  rbp := by
    have := keep hag .rbp
    simp only [Reg64s.get64_rbp, hrbp] at this
    rw [this]; exact hl.rbp
  r12 := by
    have := keep hag .r12
    simp only [Reg64s.get64_r12, h12] at this
    rw [this]; exact hl.r12
  r13 := by
    have := keep hag .r13
    simp only [Reg64s.get64_r13, h13] at this
    rw [this]; exact hl.r13
  v0 := hl.v0

-- The environment in `m` is the environment at the call.
theorem Fm.env {m : Mem 64} (hpre : Pre 96 produceA s) (h : Fm s ra m) :
    envOf m (rdi s) = Bbu.env s :=
  (keeps hpre h.un).1

-- `Base` and `Lp` only read the registers and the memory.
theorem Base.congr {t t' : MachineData} (h : Base s ra t) (hm : t'.dmem = t.dmem)
    (hr : t'.regs = t.regs) : Base s ra t' :=
  ⟨hm ▸ h.fm, hr ▸ h.rsp, hr ▸ h.r14, hr ▸ h.r15⟩

theorem Lp.congr {t t' : MachineData} (h : Lp s ra t) (hm : t'.dmem = t.dmem)
    (hr : t'.regs = t.regs) : Lp s ra t' :=
  { toBase := h.toBase.congr hm hr, st := hm ▸ h.st, rbx := hr ▸ h.rbx, rbp := hr ▸ h.rbp,
    r12 := hr ▸ h.r12, r13 := hr ▸ h.r13, v0 := h.v0 }

-- `add` returns to `.LB28`.
theorem at28_of_add {t c u : MachineData} (hpre : Pre 96 produceA s) (hb : Base s ra t)
    (hp : Post addF addR c u) (hag : (mod addF c).Agree c u)
    (hc : c.dmem = t.dmem) (hrsp : c.regs.rsp = t.regs.rsp) (h14 : c.regs.r14 = t.regs.r14)
    (h15 : c.regs.r15 = t.regs.r15) (hrdi : rdi c = rdi s) (hrbx : c.regs.rbx.toBitVec = rdi s)
    (hrbp : c.regs.rbp.toBitVec = rsi s) (hst : stOf t.dmem (rdi s) = st s)
    (hd : (rdx c).toNat = dd s)
    (he : emit (env s) (st s) (dd s) = add (st s) (rsi c) (dd s) ⟨rcx c, r8 c⟩) :
    At28 s ra u := by
  refine ⟨hb.call hpre hp hag (by decide) hc hrsp h14 h15 hrdi, ?_, ?_, _, _, he, ?_⟩
  · have := keep hag .rbx
    simp only [Reg64s.get64_rbx] at this
    rw [this]; exact hrbx
  · have := keep hag .rbp
    simp only [Reg64s.get64_rbp] at this
    rw [this]; exact hrbp
  · have hr := hp.2.2
    unfold addR at hr
    rw [st, hc, hrdi, hst, hd] at hr
    exact Res.mono (fun a ha => ⟨ha.1, hrdi ▸ ha.2⟩) hr
end

-- `position_of` returns from `.LB28`.
theorem Base.pos {s t c u : MachineData} {ra : Int64} {st' : St} (hpre : Pre 96 produceA s) (hb : Base s ra t)
    (hp : Post positionOfF positionOfR c u) (hag : (mod positionOfF c).Agree c u)
    (hc : c.dmem = t.dmem) (hrsp : c.regs.rsp = t.regs.rsp) (h14 : c.regs.r14 = t.regs.r14)
    (h15 : c.regs.r15 = t.regs.r15) (hrbx : c.regs.rbx.toBitVec = rdi s) (hrdi : rdi c = rdi s)
    (hrsi : rsi c = rsi s) (hst : stOf t.dmem (rdi s) = st') :
    Base s ra u ∧ u.regs.rbx.toBitVec = rdi s
      ∧ u.regs.rax.toBitVec = encOpt (positionOf st' (dd s)) ∧ stOf u.dmem (rdi s) = st' := by
  refine ⟨hb.call hpre hp hag (by decide) hc hrsp h14 h15 hrdi, ?_, ?_, ?_⟩
  · have := keep hag .rbx
    simp only [Reg64s.get64_rbx] at this
    rw [this]; exact hrbx
  · have hr : rax u = encOpt (positionOf (stOf c.dmem (rdi c)) (rsi c).toNat) := hp.2.2.1
    rw [hc, hrdi, hst, hrsi] at hr
    exact hr
  · have hr : stOf u.dmem (rdi c) = stOf c.dmem (rdi c) := hp.2.2.2
    rw [hc, hrdi, hst] at hr
    exact hr

-- The test `position_of(s, d) == s->len - 1` at `.LB28`.
theorem pos_test {o : Option Nat} {L : Nat} {r : Word} (hr : r.toNat = L) (hL : 1 ≤ L)
    (hL' : L ≤ 1025) (ho : ∀ p, o = some p → p < L) :
    encOpt o - (r - 1#64) = 0#64 ↔ o = some (L - 1) := by
  cases o with
  | none =>
    simp only [encOpt, reduceCtorEq, iff_false]
    bv_omega
  | some p =>
    have hp := ho p rfl
    simp only [encOpt, Option.some.injEq]
    constructor
    · intro h; bv_omega
    · intro h; subst h; bv_omega

-- The store of `pending - 1` keeps the frame.
theorem Fm.setPending {s : MachineData} {ra : Int64} {m : Mem 64} (hpre : Pre 96 produceA s) (h : Fm s ra m) (x : Word) :
    Fm s ra (m.storeInt (wordAt (rdi s) 1) 8 x.toInt) := by
  have hs := h.wf.struct_lt
  simp only [WORDS_eq] at hs
  refine h.store hpre (fun y hy => ?_) (rd_store_other _ ?_) (rd_store_other _ ?_)
  · refine Or.inl ?_
    simp only [Mem.Blocks.Inside, or_false, wordAt] at hy ⊢
    bv_omega
  all_goals (simp only [wordAt]; bv_omega)

theorem At26.ok {s t : MachineData} {ra : Int64} {st' : St} (hb : Base s ra t)
    (h : produce (env s) (st s) (dd s) = .ok st') (h0 : t.regs.rax.toBitVec = 0#64)
    (hs : stOf t.dmem (rdi s) = st') : At26 s ra t := by
  refine ⟨hb, ?_⟩
  unfold produceR
  rw [h]
  exact ⟨h0, hs⟩

theorem entry_stack (x : Word) :
    (x - 8#64 - (x - 8#64 - 8#64 - 8#64 - 8#64 - 8#64)).toNat < 2 ^ 63 := by
  bv_omega

theorem entry_stack40 (x : Word) : (x - 8#64 - (x - 40#64)).toNat < 2 ^ 63 := by
  bv_omega

theorem encOpt_none {o : Option Nat} (hlt : ∀ c, o = some c → c < 1024)
    (h : (encOpt o).msb = true) : o = none := by
  cases o with
  | none => rfl
  | some c => rw [encOpt_msb (hlt c rfl)] at h; exact absurd h (by decide)

theorem encOpt_some {o : Option Nat} (h : (encOpt o).msb = false) : ∃ c, o = some c := by
  cases o with
  | none => exact absurd h (by decide)
  | some c => exact ⟨c, rfl⟩

-- `shallowest_copy` returns in the entry block.
theorem entry_call {s : MachineData} {ra : Int64} {M : Mem 64} {c u : MachineData}
    (hpre : Pre 96 produceA s) (hfm : Fm s ra M) (hp : Post shallowestCopyF shallowestCopyR c u)
    (hag : (mod shallowestCopyF c).Agree c u) (hc : c.dmem = M) (hrsp : rsp c = rsp s - 40#64)
    (h14 : c.regs.r14 = s.regs.r14) (h15 : c.regs.r15 = s.regs.r15) (hrdi : rdi c = rdi s)
    (hrbx : c.regs.rbx.toBitVec = rdi s) (hrbp : c.regs.rbp.toBitVec = rsi s)
    (h12 : c.regs.r12.toBitVec = vv s) (hrsi : rsi c = vv s) (hst : stOf M (rdi s) = st s) :
    Base s ra u ∧ stOf u.dmem (rdi s) = st s ∧ u.regs.rbx.toBitVec = rdi s
      ∧ u.regs.rbp.toBitVec = rsi s ∧ u.regs.r12.toBitVec = vv s
      ∧ u.regs.rax.toBitVec = encOpt (cp s) := by
  refine ⟨⟨Fm.call hpre hfm (by decide) hc hrsp hrdi hp hag, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · have := keep hag .rsp
    simp only [Reg64s.get64_rsp] at this
    rw [this]; exact hrsp
  · have := keep hag .r14
    simp only [Reg64s.get64_r14] at this
    rw [this, h14]
  · have := keep hag .r15
    simp only [Reg64s.get64_r15] at this
    rw [this, h15]
  · have hr : stOf u.dmem (rdi c) = stOf c.dmem (rdi c) := hp.2.2.2
    rw [hc, hrdi, hst] at hr
    exact hr
  · have := keep hag .rbx
    simp only [Reg64s.get64_rbx] at this
    rw [this]; exact hrbx
  · have := keep hag .rbp
    simp only [Reg64s.get64_rbp] at this
    rw [this]; exact hrbp
  · have := keep hag .r12
    simp only [Reg64s.get64_r12] at this
    rw [this]; exact h12
  · have hr : rax u = encOpt (shallowestCopy (stOf c.dmem (rdi c)) (rsi c)) := hp.2.2.1
    rw [hc, hrdi, hst, hrsi] at hr
    exact hr

-- The `be` flag of `x - 15`.
theorem be_sub15 (x : Word) (af of : Bool) :
    CondCode.be.interp (StatusFlags.from_result (x - 15#64)
      { cf := (((x - 15#64).toNat : Int) != (x.toNat : Int) - 15), af := af, of := of }) =
      decide (x.toNat ≤ 15) := by
  simp only [CondCode.interp_be, StatusFlags.cf_from_result, StatusFlags.zf_from_result]
  rw [Bool.eq_iff_iff, Bool.or_eq_true, bne_iff_ne, beq_iff_eq, decide_eq_true_iff]
  constructor
  · rintro (h | h)
    · rw [ne_eq, BitVec.toNat_sub] at h; have := x.isLt; simp at h; omega
    · have := congrArg BitVec.toNat h; rw [BitVec.toNat_sub] at this; simp at this; omega
  · intro h
    rcases Nat.lt_or_ge x.toNat 15 with h' | h'
    · left; rw [ne_eq, BitVec.toNat_sub]; simp; omega
    · right; apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_sub]; simp; omega

-- The depth `len - c` of the copy `c` and the test value `len - 1 - c`.
theorem depth_bv {r : Word} {L c : Nat} (hr : r.toNat = L) (hc : c < L) (hL : L < 1024) :
    (r - BitVec.ofNat 64 c + -1#64).toNat = L - 1 - c
      ∧ r - BitVec.ofNat 64 c = BitVec.ofNat 64 (L - c) := by
  subst hr
  constructor
  · bv_omega
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega

-- After `shallowest_copy` returns a copy `c`.
theorem entry_depth {s u : MachineData} (hpre : Pre 96 produceA s)
    (hst : stOf u.dmem (rdi s) = st s) (hux : u.regs.rbx.toBitVec = rdi s)
    (hax : u.regs.rax.toBitVec = encOpt (cp s)) (hs : (encOpt (cp s)).msb = false) :
    ∃ c, cp s = some c
      ∧ (rd u.dmem u.regs.rbx.toBitVec - u.regs.rax.toBitVec + -1#64).toNat = (st s).len - 1 - c
      ∧ rd u.dmem u.regs.rbx.toBitVec - u.regs.rax.toBitVec = BitVec.ofNat 64 ((st s).len - c) := by
  obtain ⟨c, hc⟩ := encOpt_some hs
  have hlt := shallowestCopy_lt hc
  have hlen : (st s).len < 1024 := hpre.2.2.2.1
  have hr : (rd u.dmem u.regs.rbx.toBitVec).toNat = (st s).len := by
    rw [hux, ← hst, st_len, wordAt_zero]
  rw [hax, hc]
  exact ⟨c, rfl, depth_bv hr hlt hlen⟩

-- The state after the depth test, as a literal with variable fields. A direct proof
-- in the body makes the kernel compare the state literal with `u`; this uses more
-- than 8 GB. With these lemmas the kernel only checks `rfl` on equal terms.
section
variable {s u : MachineData} {ra : Int64} {z : RegZmms} {f : StatusFlags} {d : Mem 64}
  {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64}

theorem stack40 {t : MachineData} (h : t.regs.rsp.toBitVec = rsp s - 40#64) :
    t.StackAtOrBelow (s.pushRa ra) :=
  MachineData.stackAtOrBelow_of_toNat_lt (by
    simp only [Reg64s.get64_rsp, pushRa_rsp, h]
    exact entry_stack40 _)

theorem stack40_mk (h : a6.toBitVec = rsp s - 40#64) :
    (MachineData.mk ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩
      z f d).StackAtOrBelow (s.pushRa ra) :=
  stack40 h

theorem lp_mk (hB : Base s ra u) (hst : stOf u.dmem (rdi s) = st s)
    (hux : u.regs.rbx.toBitVec = rdi s) (hbp : u.regs.rbp.toBitVec = rsi s)
    (h12 : u.regs.r12.toBitVec = vv s) (hax : u.regs.rax.toBitVec = encOpt (cp s))
    (hz : vv s ≠ 0) (hd : d = u.dmem) (e1 : a1 = u.regs.rbx) (e6 : a6 = u.regs.rsp)
    (e7 : a7 = u.regs.rbp) (e12 : a12 = u.regs.r12) (e13 : a13 = ⟨u.regs.rax.toBitVec⟩)
    (e14 : a14 = u.regs.r14) (e15 : a15 = u.regs.r15) :
    Lp s ra ⟨⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩, z, f, d⟩ := by
  subst hd e1 e6 e7 e12 e13 e14 e15
  exact ⟨⟨hB.fm, hB.rsp, hB.r14, hB.r15⟩, hst, hux, hbp, h12, hax, hz⟩

theorem at40_mk {B : Word} {c : Nat}
    (hL : Lp s ra ⟨⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩, z, f, d⟩)
    (hcp : cp s = some c) (hd : (st s).len - 1 - c ≤ 15) (e8 : a8 = ⟨B⟩)
    (hB : B = BitVec.ofNat 64 ((st s).len - c)) :
    At40 s ra ⟨⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩, z, f, d⟩ := by
  subst e8
  exact ⟨hL, c, hcp, hd, hB⟩

theorem at29_mk {c : Nat}
    (hL : Lp s ra ⟨⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩, z, f, d⟩)
    (hcp : cp s = some c) (hd : ¬(st s).len - 1 - c ≤ 15) :
    At29 s ra ⟨⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩, z, f, d⟩ := by
  refine ⟨hL, fun c' hc' => ?_⟩
  obtain rfl := Option.some.inj (hcp.symm.trans hc')
  exact Nat.lt_of_not_le hd

end

end Produce

-- A jump to a label of the cfg: the stack, the invariant and the variant.
local macro "cfg_goto" : tactic => `(tactic| (
  apply Program.Intercept.intro_label
  · repeat ((fail_if_success (apply List.getElem?_cons_zero)); (apply List.getElem?_cons_succ_of))
    apply List.getElem?_cons_zero
  refine Or.inl ⟨?_, ?_, ?_⟩))

open Produce in
theorem produce_body [Host] [FunDecls]
    (hcopy : Spec "shallowest_copy" shallowestCopyF shallowestCopyA shallowestCopyR)
    (hspill : Spec "is_spilled" isSpilledF isSpilledA isSpilledR)
    (hadd : Spec "add" addF addA addR)
    (hpos : Spec "position_of" positionOfF positionOfA positionOfR) :
    Body produceAsm produceF produceA produceR := by
  intro s ra
  refine ⟨fun s₀ ⟨h₀, hpre⟩ => ?_⟩
  subst h₀
  replace hpre : Pre 96 produceA s := hpre
  have hle : 96 ≤ s.regs.rsp.toBitVec.toNat := hpre.2.1.le
  refine Program.WP.cfg (fun
      | .entry, t | .label "produce", t => t = s.pushRa ra
      | .label ".LB29", t => At29 s ra t
      | .label ".LB37", t => At37 s ra t
      | .label ".LB30", t => At30 s ra t
      | .label ".LB28", t => At28 s ra t
      | .label ".LB26", t => At26 s ra t
      | .label ".LB39", t => At39 s ra t
      | .label ".LB40", t => At40 s ra t
      | .label ".LB32", t => At32 s ra t
      | .label ".LB34", t | .label ".LB35", t => Asrt s ra t
      | _, _ => False)
    V ?_ rfl
  cfg_cases
  case left t ht =>
    subst ht
    kvcgen64
  case right.right.right.right.right.right.right.right.right.right.left t ht
      | right.right.right.right.right.right.right.right.right.right.right t ht =>
    obtain ⟨hb, hpr⟩ := ht
    clear hcopy hspill hadd hpos
    kvcgen64
    cfg_goto
    · apply MachineData.stackAtOrBelow_of_toNat_lt
      simp only [Reg64s.get64_rsp, pushRa_rsp, hb.rsp]
      bv_omega
    · refine ⟨⟨hb.fm, hb.rsp, hb.r14, hb.r15⟩, ?_⟩
      unfold produceR
      rw [hpr]
      rfl
    · simp [V]
  case right.right.right.right.right.right.left t ht =>
    obtain ⟨hb, hR⟩ := ht
    obtain ⟨h1, h2, h3, h4⟩ := hb.fm.pops hb.rsp
    clear hcopy hspill hadd hpos
    kvcgen64
    all_goals simp only [rd_def] at *
    case vc1 | vc2 | vc3 | vc4 =>
      refine Mem.Mapped.loadInt_isSome hb.fm.map (Or.inl ?_)
      simp only [Reg64s.get64_rsp, hb.rsp]
      bv_omega
    case vc5 =>
      simp only [MachineData.retAddr, Option.isSome_map]
      refine Mem.Mapped.loadInt_isSome hb.fm.map (Or.inl ?_)
      simp only [Reg64s.get64_rsp, hb.rsp]
      bv_omega
    case vc6 =>
      refine ret hpre hb.fm (by simp only [Reg64s.get64_rsp, hb.rsp]; bv_omega) ?_ ?_
      · intro q hq
        have := hb.r14
        have := hb.r15
        cases q <;> simp_all
      · intro t' hm hax
        exact produceR_congr hm hax hR
  case right.right.right.right.right.right.right.left t ht =>
    obtain ⟨hb, hst, hrbx, hrbp, hrdi, hrsi, hv⟩ := ht
    clear hcopy hspill hpos
    kvcgen64 [hadd]
    all_goals bbu_norm at *
    case vc1 => exact hb.call_isSome hpre
    case vc2 => exact hb.pre hpre (by decide) rfl rfl hrdi (hb.fm.addA hpre rfl hrdi hst)
    case vc3 =>
      rename_i u hp hag _
      have h28 := at28_of_add hpre hb hp hag rfl rfl rfl rfl hrdi hrbx hrbp hst
        (congrArg BitVec.toNat hrsi) (emit_zero (st := st s) hv)
      cfg_goto
      · apply MachineData.stackAtOrBelow_of_toNat_lt
        simp only [Reg64s.get64_rsp, pushRa_rsp, h28.1.rsp]
        bv_omega
      · exact h28
      · simp [V]
  case right.right.right.right.right.right.right.right.left t ht =>
    obtain ⟨hl, c, hc, hd, hr8⟩ := ht
    clear hcopy hspill hpos
    kvcgen64 [hadd]
    all_goals bbu_norm at *
    case vc1 => exact hl.call_isSome hpre
    case vc2 => exact hl.pre hpre (by decide) rfl rfl hl.rbx (hl.fm.addA hpre rfl hl.rbx hl.st)
    case vc3 =>
      rename_i u hp hag _
      have h28 := at28_of_add hpre hl.toBase hp hag rfl rfl rfl rfl hl.rbx hl.rbx hl.rbp hl.st
        (congrArg BitVec.toNat hl.rbp) (by
          refine (emit_dup hl.v0 hc hd).trans ?_
          show _ = add (st s) t.regs.r12.toBitVec (dd s) ⟨1#64, t.regs.r8.toBitVec⟩
          rw [hl.r12, hr8]; rfl)
      cfg_goto
      · apply MachineData.stackAtOrBelow_of_toNat_lt
        simp only [Reg64s.get64_rsp, pushRa_rsp, h28.1.rsp]
        bv_omega
      · exact h28
      · simp [V]
  case right.right.right.right.left t ht =>
    obtain ⟨⟨hl, hf⟩, hp0⟩ := ht
    clear hcopy hspill hpos
    kvcgen64 [hadd]
    all_goals bbu_norm at *
    case vc1 => exact hl.call_isSome hpre
    case vc2 => exact hl.pre hpre (by decide) rfl rfl hl.rbx (hl.fm.addA hpre rfl hl.rbx hl.st)
    case vc3 =>
      rename_i u hp hag _
      have h28 := at28_of_add hpre hl.toBase hp hag rfl rfl rfl rfl hl.rbx hl.rbx hl.rbp hl.st
        (congrArg BitVec.toNat hl.rbp) (by
          refine (emit_push hl.v0 hf hp0).trans ?_
          show _ = add (st s) t.regs.r12.toBitVec (dd s) ⟨2#64, t.regs.r12.toBitVec⟩
          rw [hl.r12]; rfl)
      exact h28
    case vc4 => simp [V]
  case right.right.right.left t ht =>
    obtain ⟨⟨hl, hf⟩, hfree⟩ := ht
    clear hcopy hadd hpos
    kvcgen64 [hspill]
    all_goals bbu_norm at *
    case vc1 => exact hl.call_isSome hpre
    case vc2 =>
      refine hl.pre hpre (by decide) rfl rfl hl.rbx ⟨dd s, ?_⟩
      show _ < (envOf t.dmem t.regs.rbx.toBitVec).n
        ∧ (envOf t.dmem t.regs.rbx.toBitVec).target[dd s]! = t.regs.r12.toBitVec
      rw [hl.rbx, hl.fm.env hpre, hl.r12]
      exact ⟨hpre.2.2.1, rfl⟩
    all_goals
      rename_i u hp hag _ hz _
      have hst : stOf u.dmem (rdi s) = st s := by
        have h : stOf u.dmem t.regs.rbx.toBitVec = stOf t.dmem t.regs.rbx.toBitVec := hp.2.2.2
        rw [hl.rbx, hl.st] at h; exact h
      have hrax : u.regs.rax.toBitVec = BitVec.ofNat 64 (isSpilled (env s) (vv s)).toNat := by
        have h : u.regs.rax.toBitVec
            = BitVec.ofNat 64 (isSpilled (envOf t.dmem t.regs.rbx.toBitVec) t.regs.r12.toBitVec).toNat :=
          hp.2.2.1
        rw [hl.rbx, hl.fm.env hpre, hl.r12] at h; exact h
      have hL := hl.call hpre hp hag (by decide) rfl rfl rfl rfl rfl rfl rfl rfl hl.rbx hst
      bbu_flags at hz
      rw [hrax] at hz
    case vc3 =>
      have hsp : isSpilled (env s) (vv s) = false := by
        cases hs : isSpilled (env s) (vv s)
        · rfl
        · rw [hs] at hz; revert hz; decide
      cfg_goto
      · apply MachineData.stackAtOrBelow_of_toNat_lt
        simp only [Reg64s.get64_rsp, pushRa_rsp, hL.rsp]
        bv_omega
      · exact ⟨⟨hL.congr rfl rfl, hf⟩, Bool.or_eq_false_iff.mpr ⟨hfree, hsp⟩⟩
      · simp [V]
    case vc4 =>
      have hsp : isSpilled (env s) (vv s) = true := by
        cases hs : isSpilled (env s) (vv s)
        · rw [hs] at hz; revert hz; decide
        · rfl
      exact ⟨⟨hL.congr rfl rfl, hf⟩, by simp only [Bool.or_eq_true]; exact Or.inr hsp⟩
    case vc5 => simp [V]
  case right.right.left t ht =>
    obtain ⟨hl, hf⟩ := ht
    clear hcopy hadd hpos hspill
    kvcgen64
    all_goals bbu_norm at *
    all_goals bbu_flags at *
    case vc1 =>
      rename_i hz
      rw [hl.r12] at hz
      cfg_goto
      · apply MachineData.stackAtOrBelow_of_toNat_lt
        simp only [Reg64s.get64_rsp, pushRa_rsp, hl.rsp]
        bv_omega
      · exact ⟨⟨hl.congr rfl rfl, hf⟩, isFree_even hl.v0 hz⟩
      · simp [V]
    case vc2 =>
      rename_i hz h1
      rw [hl.r12] at hz h1
      cfg_goto
      · apply MachineData.stackAtOrBelow_of_toNat_lt
        simp only [Reg64s.get64_rsp, pushRa_rsp, hl.rsp]
        bv_omega
      · exact ⟨⟨hl.congr rfl rfl, hf⟩, by rw [isFree_odd hz h1]; rfl⟩
      · simp [V]
    case vc3 =>
      rename_i hz h1
      rw [hl.r12] at h1
      exact ⟨⟨hl.congr rfl rfl, hf⟩, isFree_one h1⟩
    case vc4 => simp [V]
  case right.right.right.right.right.right.right.right.right.left t ht =>
    obtain ⟨⟨hl, hf⟩, hp0⟩ := ht
    clear hcopy hadd hpos hspill
    have hw := hl.fm.wf
    kvcgen64
    all_goals bbu_norm at *
    all_goals
      rename_i hz _
      rw [msb_test, hl.r13] at hz
    case vc1 =>
      have hn : cp s = none := by
        cases hc : cp s with
        | none => rfl
        | some c =>
          have hlen : (st s).len < 1024 := hpre.2.2.2.1
          rw [hc, encOpt_msb (by have := shallowestCopy_lt hc; omega)] at hz; cases hz
      cfg_goto
      · apply MachineData.stackAtOrBelow_of_toNat_lt
        simp only [Reg64s.get64_rsp, pushRa_rsp, hl.rsp]
        bv_omega
      · exact ⟨hl.toBase.congr rfl rfl, produce_err (emit_none hl.v0 hp0 hn)⟩
      · simp [V]
    all_goals
      obtain ⟨c, hc⟩ : ∃ c, cp s = some c := by
        cases hc : cp s with
        | none => rw [hc] at hz; exact absurd hz (by decide)
        | some c => exact ⟨c, rfl⟩
      have hb' : t.regs.rbx.toBitVec = s.regs.rdi.toBitVec := hl.rbx
      rw [hb']
    case vc2 => exact hdr_isSome0 hw
    case vc3 => exact hdr_isSome hw (k := 7) (by decide)
    case vc4 => exact blk_isSome0 hw
    case vc5 => exact loadInt_isSome_store _ (hdr_isSome hw (k := 7) (by decide))
    case vc6 => exact blk_isSome1 hw _
    case vc7 =>
      have hP : produce (env s) (st s) (dd s) = .error (.blocked c ((st s).len - 1 - c - 15)) :=
        produce_err (emit_blocked hl.v0 hf hp0 hc)
      have hcl := shallowestCopy_lt hc
      have hfar : 15 < (st s).len - 1 - c := hf c hc
      have hlen : (st s).len < 1024 := hpre.2.2.2.1
      have h0 : (rd t.dmem s.regs.rdi.toBitVec).toNat = (st s).len := by
        rw [← hl.st, st_len, wordAt_zero]; rfl
      rw [blkStores_eq hw]
      cfg_goto
      · apply MachineData.stackAtOrBelow_of_toNat_lt
        simp only [Reg64s.get64_rsp, pushRa_rsp, hl.rsp]
        bv_omega
      · refine ⟨⟨Fm.blk hpre hl.fm _ _, hl.rsp, hl.r14, hl.r15⟩, ?_⟩
        obtain ⟨h1, h2⟩ := blkStores_rd hw t.regs.r13.toBitVec
          (rd t.dmem s.regs.rdi.toBitVec - 16#64 - t.regs.r13.toBitVec)
        unfold produceR
        rw [hP]
        unfold Res
        refine ⟨rfl, h1.trans ?_, h2.trans ?_⟩
        · rw [hl.r13, hc]; rfl
        · rw [hl.r13, hc]
          simp only [encOpt]
          bv_omega
      · simp [V]
  case right.right.right.right.right.left t ht =>
    obtain ⟨hb, hrbx, hrbp, v, op, he, hr⟩ := ht
    have hP : produce (env s) (st s) (dd s) = (add (st s) v (dd s) op).bind (tail (dd s)) := by
      rw [produce_eq, he]
    clear hcopy hadd hspill he
    cases hA : add (st s) v (dd s) op with
    | error e =>
      rw [hA] at hr hP
      have hm : (t.regs.rax.toBitVec).msb = true := Res.msb hr
      kvcgen64 [hpos]
      all_goals simp only [msb_test, hm, Bool.true_eq_false] at *
      cfg_goto
      · apply MachineData.stackAtOrBelow_of_toNat_lt
        simp only [Reg64s.get64_rsp, pushRa_rsp, hb.rsp]
        bv_omega
      · refine ⟨hb.congr rfl rfl, ?_⟩
        unfold produceR
        rw [hP]
        exact Res.err hr
      · simp [V]
    | ok st' =>
      rw [hA] at hr hP
      obtain ⟨hr0, hst'⟩ : rax t = 0#64 ∧ stOf t.dmem (rdi s) = st' := hr
      obtain ⟨hlen', -, hpend, -⟩ := add_shape hA
      have hlen : (st s).len < 1024 := hpre.2.2.2.1
      have hL : 1 ≤ st'.len ∧ st'.len ≤ 1025 := by rw [hlen']; omega
      have hpt : ∀ {u : MachineData}, stOf u.dmem (rdi s) = st' →
          (encOpt (positionOf st' (dd s)) - (rd u.dmem (rdi s) - 1#64) = 0#64
            ↔ positionOf st' (dd s) = some (st'.len - 1)) := fun hsu =>
        pos_test (by rw [← hsu, st_len, wordAt_zero]) hL.1 hL.2 fun _ => positionOf_lt
      have hw : Wf t.dmem (rdi s) := hb.fm.wf
      kvcgen64 [hpos]
      all_goals bbu_norm at *
      case vc1 =>
        rename_i hz _
        rw [msb_test, hr0] at hz
        exact absurd hz (by decide)
      case vc2 => exact hb.call_isSome hpre
      case vc3 => exact hb.pre hpre (by decide) rfl rfl hrbx trivial
      case vc4 =>
        rename_i u hp hag _
        obtain ⟨hB, hux, -, -⟩ := hb.pos hpre hp hag rfl rfl rfl rfl hrbx hrbx hrbp hst'
        rw [hux]; exact hdr_isSome0 hB.fm.wf
      case vc6 =>
        rename_i u hp hag _ _
        obtain ⟨hB, hux, -, -⟩ := hb.pos hpre hp hag rfl rfl rfl rfl hrbx hrbx hrbp hst'
        rw [hux]; exact hdr_isSome hB.fm.wf (k := 1) (by decide)
      case vc8 =>
        rename_i u hp hag _ _ _ _
        obtain ⟨hB, hux, -, -⟩ := hb.pos hpre hp hag rfl rfl rfl rfl hrbx hrbx hrbp hst'
        rw [hux]; exact hdr_isSome hB.fm.wf (k := 1) (by decide)
      case vc5 =>
        rename_i u hp hag _ hnz
        obtain ⟨hB, hux, hax, hsu⟩ := hb.pos hpre hp hag rfl rfl rfl rfl hrbx hrbx hrbp hst'
        bbu_flags at hnz
        rw [hux, hax] at hnz
        replace hnz : positionOf st' (dd s) ≠ some (st'.len - 1) := fun h => hnz ((hpt hsu).mpr h)
        cfg_goto
        · apply MachineData.stackAtOrBelow_of_toNat_lt
          simp only [Reg64s.get64_rsp, pushRa_rsp, hB.rsp]
          bv_omega
        · exact ⟨⟨hB.fm, hB.rsp, hB.r14, hB.r15⟩, hP.trans (tail_bad hnz)⟩
        · simp [V]
      all_goals
        rename_i u hp hag _ hz _ hnz
        obtain ⟨hB, hux, hax, hsu⟩ := hb.pos hpre hp hag rfl rfl rfl rfl hrbx hrbx hrbp hst'
        bbu_flags at hz hnz
        rw [BitVec.and_self] at hz
        rw [hux, hax] at hnz
        have hpo := (hpt hsu).mp hnz
        have hpw : st'.pending = (rd u.dmem (rdi s + 8#64)).toNat := by rw [← hsu]; rfl
        rw [hux] at hz ⊢
      case vc7 =>
        have hp0 : st'.pending = 0 := by rw [hpw, hz]; rfl
        cfg_goto
        · apply MachineData.stackAtOrBelow_of_toNat_lt
          simp only [Reg64s.get64_rsp, pushRa_rsp, hB.rsp]
          bv_omega
        · exact At26.ok ⟨hB.fm, hB.rsp, hB.r14, hB.r15⟩
            (hP.trans ((tail_ok hpo).trans (congrArg _ (pending_zero hp0)))) rfl hsu
        · simp [V]
      case vc9 =>
        have hx : (rd u.dmem (rdi s + 8#64) - 1#64).toNat = st'.pending - 1 := by
          rw [hpw]; bv_omega
        refine At26.ok ⟨hB.fm.setPending hpre (rd u.dmem (rdi s + 8#64) - 1#64), hB.rsp, hB.r14,
          hB.r15⟩ (hP.trans (tail_ok hpo)) rfl ?_
        refine (stOf_setPending hB.fm.wf (rd u.dmem (rdi s + 8#64) - 1#64)).trans ?_
        rw [hsu, hx]
      case vc10 => simp [V]
  case right.left t ht =>
    subst ht
    have hfm := fm_pushes (ra := ra) hpre
    have hsp := st_pushes (ra := ra) hpre
    have hen := hfm.env hpre
    have hn := hfm.n hpre
    have hd : (rsi s).toNat < nOf (pushes s ra) (rdi s) := by
      rw [hn, ← env_n]; exact hpre.2.2.1
    have hv : rd (pushes s ra) (rd (pushes s ra) (rdi s + 32#64) + rsi s * 8#64) = vv s := by
      have := rd_target hd
      rw [wordAt_zero, hen] at this
      exact this
    have htg := tgt_isSome hfm.wf hd
    rw [wordAt_mul] at htg
    have hr40 : s.regs.rsp.toBitVec - 8#64 - 8#64 - 8#64 - 8#64 - 8#64 = rsp s - 40#64 := by
      simp only [Reg64s.get64_rsp]; bv_omega
    have hfr := hpre.2.1.mapped
    clear hspill hadd hpos
    kvcgen64 [hcopy]
    all_goals simp only [pushes_eq, rd_def] at *
    all_goals generalize hM : pushes s ra = M at *
    all_goals bbu_norm at *
    case vc1 | vc2 | vc3 | vc4 =>
      repeat apply loadInt_isSome_store
      refine Mem.Mapped.loadInt_isSome hfr (Or.inl ?_)
      clear hv htg hd hfm hsp hen hn hM hpre hr40 hfr
      rename_i _ _ h
      clear h
      bv_omega
    case vc5 => exact hdr_isSome hfm.wf (k := 4) (by decide)
    case vc6 => exact htg
    case vc8 => exact hr40 ▸ Fm.call_isSome hpre hfm
    case vc9 => exact Fm.pre hpre hfm (by decide) rfl hr40 rfl trivial
    case vc7 =>
      rename_i hz
      bbu_flags at hz
      rw [BitVec.and_self] at hz
      cfg_goto
      · apply MachineData.stackAtOrBelow_of_toNat_lt
        simp only [Reg64s.get64_rsp, pushRa_rsp]
        exact entry_stack _
      · exact ⟨⟨hfm, hr40, rfl, rfl⟩, hsp, rfl, rfl, rfl, rfl, hv.symm.trans hz⟩
      · simp [V]
    case vc10 =>
      rename_i u _ hs _ hz hp hag
      obtain ⟨hB, hst, hux, hbp, h12, hax⟩ :=
        entry_call hpre hfm hp hag rfl hr40 rfl rfl rfl rfl rfl hv hv hsp
      bbu_flags at hz
      rw [BitVec.and_self, hv] at hz
      rw [msb_test, hax] at hs
      have hcp : cp s = none :=
        encOpt_none (fun c hc => by have := shallowestCopy_lt hc; have : _ < 1024 := hpre.2.2.2.1; omega) hs
      cfg_goto
      · apply MachineData.stackAtOrBelow_of_toNat_lt
        simp only [Reg64s.get64_rsp, pushRa_rsp, hB.rsp]
        exact entry_stack40 _
      · exact ⟨⟨⟨hB.fm, hB.rsp, hB.r14, hB.r15⟩, hst, hux, hbp, h12, hax, hz⟩,
          fun c hc => absurd (hc.symm.trans hcp) (Option.some_ne_none c)⟩
      · simp [V]
    case vc11 =>
      rename_i u _ _ _ _ hp hag
      obtain ⟨hB, -, hux, -⟩ := entry_call hpre hfm hp hag rfl hr40 rfl rfl rfl rfl rfl hv hv hsp
      rw [hux]; exact hdr_isSome0 hB.fm.wf
    case vc14 => exact Or.inr ⟨V_eq3 _ _, by decide⟩
    all_goals
      rename_i u _ hs _ hbe hz hp hag
      obtain ⟨hB, hst, hux, hbp, h12, hax⟩ :=
        entry_call hpre hfm hp hag rfl hr40 rfl rfl rfl rfl rfl hv hv hsp
      bbu_flags at hz
      rw [BitVec.and_self, hv] at hz
      rw [msb_test, hax] at hs
      rw [be_sub15] at hbe
      obtain ⟨c, hcp, hy, hr8⟩ := entry_depth hpre hst hux hax hs
      rw [hy] at hbe
    case vc12 =>
      cfg_goto
      · exact stack40_mk hB.rsp
      · exact at40_mk (lp_mk hB hst hux hbp h12 hax hz rfl rfl rfl rfl rfl rfl rfl rfl) hcp
          (of_decide_eq_true hbe) rfl hr8
      · exact Or.inr ⟨V_eq40 _ _, by decide⟩
    case vc13 =>
      exact at29_mk (lp_mk hB hst hux hbp h12 hax hz rfl rfl rfl rfl rfl rfl rfl rfl) hcp
        (of_decide_eq_false hbe)

end Bbu
