import BbuKraken.Contracts

/-!
The body triple of `urgent` (`c/bbu/urgent.S`). The loop keeps the offset `d`
in `rbx` and the result `u` so far in `r14`; the model is `urgentFrom`.
-/

open Std.WP Lean.Order
open scoped Program.WP

set_option experimental.vcgen true

namespace Bbu

namespace Urgent

/-! ## Model lemmas -/

theorem env_n {m : Mem 64} {S : Addr} : (envOf m S).n = nOf m S := by
  simp [Env.n, envOf]

theorem target_get {m : Mem 64} {S : Addr} {d : Nat} (hd : d < nOf m S) :
    (envOf m S).target[d]! = rd m (wordAt (tgtOf m S) d) := by
  simp [envOf, hd]

theorem st_len {m : Mem 64} {S : Addr} : (stOf m S).len = (rd m (wordAt S 0)).toNat := by
  simp [St.len, stOf]

theorem positionOf_lt {st : St} {d p : Nat} (h : positionOf st d = some p) : p < st.len := by
  simp only [positionOf, List.findIdx?_eq_some_iff_getElem] at h
  exact h.1

theorem shallowestCopy_lt {st : St} {v : Word} {c : Nat} (h : shallowestCopy st v = some c) :
    c < st.len := by
  simpa using List.mem_reverse.mp (List.mem_of_find?_eq_some h)

section
variable {e : Env} {st : St} {t d u : Nat}

theorem urgentFrom_done (h : e.n ≤ d) : urgentFrom e st t d u = .ok u := by
  rw [urgentFrom]; simp only [show ¬ d < e.n by omega, ite_false]

theorem urgentFrom_pos (hd : d < e.n) (h : (positionOf st d).isSome) :
    urgentFrom e st t d u = urgentFrom e st t (d + 1) u := by
  rw [urgentFrom]; simp only [hd, h, ite_true]

theorem urgentFrom_skip (hd : d < e.n) (hp : positionOf st d = none)
    (h : (isFree e.target[d]! || isSpilled e e.target[d]!) = true) :
    urgentFrom e st t d u = urgentFrom e st t (d + 1) u := by
  rw [urgentFrom]; simp only [hd, ite_true, hp]
  simp only [Option.isSome_none, Bool.false_eq_true, ite_false, h, ite_true]

theorem urgentFrom_none (hd : d < e.n) (hp : positionOf st d = none)
    (h : (isFree e.target[d]! || isSpilled e e.target[d]!) = false)
    (hc : shallowestCopy st e.target[d]! = none) :
    urgentFrom e st t d u = urgentFrom e st t (d + 1) u := by
  rw [urgentFrom]; simp only [hd, ite_true, hp]
  simp only [Option.isSome_none, Bool.false_eq_true, ite_false, h, hc]

theorem urgentFrom_blocked {c : Nat} (hd : d < e.n) (hp : positionOf st d = none)
    (h : (isFree e.target[d]! || isSpilled e e.target[d]!) = false)
    (hc : shallowestCopy st e.target[d]! = some c) (hb : 15 < st.len - 1 - c) :
    urgentFrom e st t d u = .error (.blocked c (st.len - 1 - c - 15)) := by
  rw [urgentFrom]; simp only [hd, ite_true, hp]
  simp only [Option.isSome_none, Bool.false_eq_true, ite_false, h, hc, MAX_DUP_DEPTH, hb, ite_true]

theorem urgentFrom_some {c : Nat} (hd : d < e.n) (hp : positionOf st d = none)
    (h : (isFree e.target[d]! || isSpilled e e.target[d]!) = false)
    (hc : shallowestCopy st e.target[d]! = some c) (hb : st.len - 1 - c ≤ 15) :
    urgentFrom e st t d u =
      urgentFrom e st t (d + 1) (if st.len - 1 - c = 15 ∧ c ≠ t ∧ u = e.n then d else u) := by
  rw [urgentFrom]; simp only [hd, ite_true, hp]
  simp only [Option.isSome_none, Bool.false_eq_true, ite_false, h, hc, MAX_DUP_DEPTH,
    show ¬ 15 < st.len - 1 - c by omega, ite_false]
  rfl
end



/-! ## Normal forms of `kvcgen64` terms -/

theorem rd_def {m : Mem 64} {a : Addr} : BitVec.ofInt 64 (m.loadInt a 8).get! = rd m a := rfl

section
variable {s : MachineData} {ra : Int64}
@[simp] theorem pushRa_rax : (s.pushRa ra).regs.rax = s.regs.rax := rfl
@[simp] theorem pushRa_rbx : (s.pushRa ra).regs.rbx = s.regs.rbx := rfl
@[simp] theorem pushRa_rcx : (s.pushRa ra).regs.rcx = s.regs.rcx := rfl
@[simp] theorem pushRa_rdx : (s.pushRa ra).regs.rdx = s.regs.rdx := rfl
@[simp] theorem pushRa_rsi : (s.pushRa ra).regs.rsi = s.regs.rsi := rfl
@[simp] theorem pushRa_rdi : (s.pushRa ra).regs.rdi = s.regs.rdi := rfl
@[simp] theorem pushRa_rbp : (s.pushRa ra).regs.rbp = s.regs.rbp := rfl
@[simp] theorem pushRa_r12 : (s.pushRa ra).regs.r12 = s.regs.r12 := rfl
@[simp] theorem pushRa_r13 : (s.pushRa ra).regs.r13 = s.regs.r13 := rfl
@[simp] theorem pushRa_r14 : (s.pushRa ra).regs.r14 = s.regs.r14 := rfl
@[simp] theorem pushRa_r15 : (s.pushRa ra).regs.r15 = s.regs.r15 := rfl
theorem pushRa_rsp : (s.pushRa ra).regs.rsp.toBitVec = rsp s - 8#64 := by simp [MachineData.pushRa]
end

-- The displacement `8 * k` of a word in a struct.
theorem disp (a : Addr) (k : Nat) (i : Int64) (h : i.toInt = 8 * k := by decide) :
    a + BitVec.ofInt 64 i.toInt = wordAt a k := by
  rw [h, show (8 * (k : Int)) = ((8 * k : Nat) : Int) by omega, BitVec.ofInt_natCast]
@[simp] theorem disp0 (a : Addr) : a + BitVec.ofInt 64 (Int64.toInt 0) = wordAt a 0 := disp a 0 0
@[simp] theorem disp1 (a : Addr) : a + BitVec.ofInt 64 (Int64.toInt 8) = wordAt a 1 := disp a 1 8
@[simp] theorem disp3 (a : Addr) : a + BitVec.ofInt 64 (Int64.toInt 24) = wordAt a 3 := disp a 3 24
@[simp] theorem disp4 (a : Addr) : a + BitVec.ofInt 64 (Int64.toInt 32) = wordAt a 4 := disp a 4 32
@[simp] theorem disp7 (a : Addr) : a + BitVec.ofInt 64 (Int64.toInt 56) = wordAt a 7 := disp a 7 56
/-! ## Memory lemmas -/

section
variable {s : MachineData} {ra : Int64}

-- The saved words, the struct and the frame in the memory `m` of `urgent`.
structure Fm (s : MachineData) (ra : Int64) (m : Mem 64) : Prop where
  ra : rd m (rsp s - 8#64) = ra.toBitVec
  r15 : rd m (rsp s - 16#64) = s.regs.r15.toBitVec
  r14 : rd m (rsp s - 24#64) = s.regs.r14.toBitVec
  r13 : rd m (rsp s - 32#64) = s.regs.r13.toBitVec
  r12 : rd m (rsp s - 40#64) = s.regs.r12.toBitVec
  rbp : rd m (rsp s - 48#64) = s.regs.rbp.toBitVec
  rbx : rd m (rsp s - 56#64) = s.regs.rbx.toBitVec
  wf : Wf m (rdi s)
  map : Mem.Mapped [frame 64 s] m
  un : Mem.UnchangedOutside (mod 64 s).mem s.dmem m

-- A change in the blocks of `urgent` keeps the environment and the regions.
theorem keeps {m : Mem 64} (hpre : Pre 64 urgentA s) (hu : Mem.UnchangedOutside (mod 64 s).mem s.dmem m) :
    envOf m (rdi s) = env s ∧ readable m (rdi s) = readable s.dmem (rdi s)
      ∧ writable m (rdi s) = writable s.dmem (rdi s) :=
  Post.env (t := { s with dmem := m }) hpre ⟨fun _ _ => rfl, hu⟩

-- The 8 bytes `k` bytes below `rsp s` lie in the frame.
theorem in_frame (_hle : 64 ≤ (rsp s).toNat) {k : Nat} (hk : 8 ≤ k) (hk' : k ≤ 64) :
    ∀ x, Mem.Blocks.Inside x 1 [(rsp s - BitVec.ofNat 64 k, 8)] → Mem.Blocks.Inside x 1 [frame 64 s] := by
  intro x hx
  simp only [Mem.Blocks.Inside, or_false] at hx ⊢
  bv_omega

-- The frame of a callee at `rsp s - 56` lies in the frame.
theorem callee_in_frame {c : MachineData} (_hle : 64 ≤ (rsp s).toNat) (hrsp : rsp c = rsp s - 56#64) :
    ∀ x, Mem.Blocks.Inside x 1 [frame 8 c] → Mem.Blocks.Inside x 1 [frame 64 s] := by
  intro x hx
  simp only [Mem.Blocks.Inside, or_false, hrsp] at hx ⊢
  bv_omega

-- The saved words do not overlap the frame of a callee at `rsp s - 56`.
theorem saved_not_callee {c : MachineData} (_hle : 64 ≤ (rsp s).toNat) (hrsp : rsp c = rsp s - 56#64)
    {k : Nat} (hk : 8 ≤ k) (hk' : k ≤ 56) :
    ∀ x, Mem.Blocks.Inside x 1 [(rsp s - BitVec.ofNat 64 k, 8)] → ¬ Mem.Blocks.Inside x 1 [frame 8 c] := by
  intro x hx hc
  simp only [Mem.Blocks.Inside, or_false, hrsp] at hx hc
  bv_omega

-- A callee at `rsp s - 56` keeps the saved words and the blocks of `urgent`.
theorem Fm.call {m : Mem 64} {c t : MachineData} {R : MachineData → MachineData → Prop}
    (hpre : Pre 64 urgentA s) (h : Fm s ra m) (hc : c.dmem = m) (hrsp : rsp c = rsp s - 56#64)
    (hrdi : rdi c = rdi s) (hp : Post 8 R c t) (hag : (mod 8 c).Agree c t) : Fm s ra t.dmem := by
  have hfr := hpre.2.1
  have hle := hfr.le
  have hwr := (keeps hpre h.un).2.2
  have hu : Mem.UnchangedOutside (frame 8 c :: writable s.dmem (rdi s)) m t.dmem := by
    have := hag.2
    simp only [mod, hc, hrdi, hwr] at this
    exact this
  -- `writable` does not overlap the frame
  have hnw : ∀ x, Mem.Blocks.Inside x 1 [frame 64 s] → ¬ Mem.Blocks.Inside x 1 (writable s.dmem (rdi s)) :=
    fun x hx hw => hfr.disj x hx (inside_append.mpr (Or.inl hw))
  have hsv : ∀ {k}, 8 ≤ k → k ≤ 56 →
      rd t.dmem (rsp s - BitVec.ofNat 64 k) = rd m (rsp s - BitVec.ofNat 64 k) := fun hk hk' =>
    rd_congr hu fun x hx hl => by
      rcases hl with hl | hl
      · exact saved_not_callee hle hrsp hk hk' x hx (Or.inl hl)
      · exact hnw x (in_frame hle hk (by omega) x hx) hl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hsv (k := 8) (by omega) (by omega)]; exact h.ra
  · rw [hsv (k := 16) (by omega) (by omega)]; exact h.r15
  · rw [hsv (k := 24) (by omega) (by omega)]; exact h.r14
  · rw [hsv (k := 32) (by omega) (by omega)]; exact h.r13
  · rw [hsv (k := 40) (by omega) (by omega)]; exact h.r12
  · rw [hsv (k := 48) (by omega) (by omega)]; exact h.rbp
  · rw [hsv (k := 56) (by omega) (by omega)]; exact h.rbx
  · rw [← hrdi]; exact hp.1
  · intro x hx
    by_cases hx8 : Mem.Blocks.Inside x 1 [frame 8 c]
    · exact hp.2.1 x hx8
    · rw [hu x fun hl => hl.elim (fun hl => hx8 (Or.inl hl)) (hnw x hx)]
      exact h.map x hx
  · intro x hx
    have hx' : ¬ Mem.Blocks.Inside x 1 (frame 8 c :: writable s.dmem (rdi s)) := fun hl =>
      hl.elim (fun hl => hx (Or.inl (by
        have := callee_in_frame hle hrsp x (Or.inl hl)
        simpa only [Mem.Blocks.Inside, or_false] using this))) (fun hl => hx (Or.inr hl))
    rw [hu x hx']
    exact h.un x hx

-- The precondition of a callee at `rsp s - 56`.
theorem Fm.pre {m : Mem 64} {c : MachineData} {A : MachineData → Prop}
    (hpre : Pre 64 urgentA s) (h : Fm s ra m) (hc : c.dmem = m) (hrsp : rsp c = rsp s - 56#64)
    (hrdi : rdi c = rdi s) (hA : A c) : Pre 8 A c := by
  obtain ⟨-, hr, hwr⟩ := keeps hpre h.un
  refine ⟨by rw [hc, hrdi]; exact h.wf, ?_, hA⟩
  exact FrameOk.sub (k := 56) hpre.2.1 hpre.1 hrdi hrsp (by omega) (hc ▸ h.map) (hc ▸ hr) (hc ▸ hwr)

-- The return address slot of a callee at `rsp s - 56` is mapped.
theorem Fm.call_isSome {m : Mem 64} (hpre : Pre 64 urgentA s) (h : Fm s ra m) :
    (m.loadInt (rsp s - 56#64 - 8#64) 8).isSome = true := by
  have hle := hpre.2.1.le
  refine Mem.Mapped.loadInt_isSome h.map (Or.inl ?_)
  bv_omega

end

/-! ## The entry block -/

section
variable {s : MachineData} {ra : Int64}

theorem rd_storeInt_ne {m : Mem 64} {a b : Addr} {v : Int}
    (h : 8 ≤ (b - a).toNat ∧ 8 ≤ (a - b).toNat) : rd (m.storeInt a 8 v) b = rd m b :=
  rd_storeInt_of_disjoint fun x hx hy => by
    simp only [Mem.Blocks.Inside, or_false] at hx hy
    bv_omega

theorem rd_storeInt_eq {m : Mem 64} {a b : Addr} {x : Word} (h : a = b) :
    rd (m.storeInt a 8 x.toInt) b = x := by
  subst h
  rw [rd, Mem.loadInt_storeInt _ _ _ _ (by decide), Option.get!_some]
  exact BitVec.ofInt_ofBytes_toBytes 64 8 rfl x

-- The memory after the pushes of the entry block, as `kvcgen64` gives it.
def pushes (s : MachineData) (ra : Int64) : Mem 64 :=
  let t := s.pushRa ra
  let R := t.regs.rsp.toBitVec
  (((((t.dmem.storeInt (R - 8#64) 8 t.regs.r15.toBitVec.toInt).storeInt
    (R - 8#64 - 8#64) 8 t.regs.r14.toBitVec.toInt).storeInt
    (R - 8#64 - 8#64 - 8#64) 8 t.regs.r13.toBitVec.toInt).storeInt
    (R - 8#64 - 8#64 - 8#64 - 8#64) 8 t.regs.r12.toBitVec.toInt).storeInt
    (R - 8#64 - 8#64 - 8#64 - 8#64 - 8#64) 8 t.regs.rbp.toBitVec.toInt).storeInt
    (R - 8#64 - 8#64 - 8#64 - 8#64 - 8#64 - 8#64) 8 t.regs.rbx.toBitVec.toInt

-- Fold the memory after the pushes, as `kvcgen64` gives it.
theorem pushes_eq : (((((Mem.storeInt (s.pushRa ra).dmem ((s.pushRa ra).regs.rsp.toBitVec - 8#64) 8
    (s.pushRa ra).regs.r15.toBitVec.toInt).storeInt
    ((s.pushRa ra).regs.rsp.toBitVec - 8#64 - 8#64) 8 (s.pushRa ra).regs.r14.toBitVec.toInt).storeInt
    ((s.pushRa ra).regs.rsp.toBitVec - 8#64 - 8#64 - 8#64) 8
      (s.pushRa ra).regs.r13.toBitVec.toInt).storeInt
    ((s.pushRa ra).regs.rsp.toBitVec - 8#64 - 8#64 - 8#64 - 8#64) 8
      (s.pushRa ra).regs.r12.toBitVec.toInt).storeInt
    ((s.pushRa ra).regs.rsp.toBitVec - 8#64 - 8#64 - 8#64 - 8#64 - 8#64) 8
      (s.pushRa ra).regs.rbp.toBitVec.toInt).storeInt
    ((s.pushRa ra).regs.rsp.toBitVec - 8#64 - 8#64 - 8#64 - 8#64 - 8#64 - 8#64) 8
      (s.pushRa ra).regs.rbx.toBitVec.toInt = pushes s ra := rfl

theorem unchanged_pushes :
    Mem.UnchangedOutside [frame 64 s] s.dmem (pushes s ra) := by
  have hin : ∀ a : Addr, (a - (rsp s - BitVec.ofNat 64 64)).toNat + 8 ≤ 64 →
      Mem.Blocks.Inside a 8 [frame 64 s] := fun a h => Or.inl h
  have hrsp : (s.pushRa ra).regs.rsp.toBitVec = rsp s - 8#64 := by simp [MachineData.pushRa]
  simp only [pushes, MachineData.dmem_pushRa, hrsp]
  refine .storeInt (.storeInt (.storeInt (.storeInt (.storeInt (.storeInt (.storeInt
    (fun _ _ => rfl) (hin _ ?_) _) (hin _ ?_) _) (hin _ ?_) _) (hin _ ?_) _) (hin _ ?_) _)
    (hin _ ?_) _) (hin _ ?_) _
  all_goals (simp only [rsp] at *; bv_omega)

theorem fm_pushes (hpre : Pre 64 urgentA s) : Fm s ra (pushes s ra) := by
  have hle := hpre.2.1.le
  have hrsp : (s.pushRa ra).regs.rsp.toBitVec = rsp s - 8#64 := by simp [MachineData.pushRa]
  have hu := unchanged_pushes (s := s) (ra := ra)
  have hd := disjoint_symm hpre.2.1.disj
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, Wf.congr_of_disjoint hu hpre.1 hd, ?_, ?_⟩
  all_goals try simp only [pushes, hrsp]
  · rw [rd_storeInt_ne, rd_storeInt_ne, rd_storeInt_ne, rd_storeInt_ne, rd_storeInt_ne,
      rd_storeInt_ne, MachineData.dmem_pushRa, rd_storeInt_eq rfl]
    all_goals first | rfl | bv_omega
  · rw [rd_storeInt_ne, rd_storeInt_ne, rd_storeInt_ne, rd_storeInt_ne, rd_storeInt_ne,
      rd_storeInt_eq]
    all_goals first | rfl | bv_omega
  · rw [rd_storeInt_ne, rd_storeInt_ne, rd_storeInt_ne, rd_storeInt_ne, rd_storeInt_eq]
    all_goals first | rfl | bv_omega
  · rw [rd_storeInt_ne, rd_storeInt_ne, rd_storeInt_ne, rd_storeInt_eq]
    all_goals first | rfl | bv_omega
  · rw [rd_storeInt_ne, rd_storeInt_ne, rd_storeInt_eq]
    all_goals first | rfl | bv_omega
  · rw [rd_storeInt_ne, rd_storeInt_eq]
    all_goals first | rfl | bv_omega
  · rw [rd_storeInt_eq]
    all_goals first | rfl | bv_omega
  · simp only [MachineData.dmem_pushRa]
    exact hpre.2.1.mapped.storeInt _ _ _ |>.storeInt _ _ _ |>.storeInt _ _ _ |>.storeInt _ _ _
      |>.storeInt _ _ _ |>.storeInt _ _ _ |>.storeInt _ _ _
  · intro x hx
    exact hu x fun h => hx (Or.inl (h.elim id False.elim))


theorem hdr_isSome {m : Mem 64} {S a : Addr} (hw : Wf m S) {k : Nat} (hk : k < 8)
    (ha : a = wordAt S k) : (m.loadInt a 8).isSome = true := by
  have hs := hw.struct_lt
  simp only [WORDS] at hs
  subst ha
  refine Mem.Mapped.loadInt_isSome hw.mapped (inside_append.mpr ?_)
  by_cases hk3 : k < 3
  · exact Or.inl (Or.inl (by simp only [wordAt]; bv_omega))
  · exact Or.inr (Or.inl (by simp only [wordAt]; bv_omega))

theorem rd_pushes_n (hpre : Pre 64 urgentA s) :
    rd (pushes s ra) (wordAt (rdi s) 3) = rd s.dmem (wordAt (rdi s) 3) :=
  hdr_congr unchanged_pushes (disjoint_mono (fun x hx => inside_append.mpr (Or.inr hx))
    (disjoint_symm hpre.2.1.disj)) (by omega) (by omega)

theorem st_pushes (hpre : Pre 64 urgentA s) : stOf (pushes s ra) (rdi s) = st s :=
  stOf_congr unchanged_pushes hpre.1 (disjoint_symm hpre.2.1.disj)
end

/-! ## The `blocked` block -/

section
variable {s : MachineData} {ra : Int64}

theorem blkOf_def {m : Mem 64} {S : Addr} : rd m (wordAt S 7) = blkOf m S := rfl

-- A word of the struct does not overlap `blocked`.
theorem blk_disj {m : Mem 64} {S : Addr} (hw : Wf m S) {k : Nat} (hk : k < WORDS) :
    Mem.Blocks.Disjoint [(wordAt S k, 8)] [(blkOf m S, 16)] := by
  intro x hx hb
  have hs := hw.struct_lt
  simp only [WORDS] at hs hk
  refine hw.disj_struct x ?_ (inside_of_mem (by simp) hb)
  simp only [Mem.Blocks.Inside, or_false, WORDS] at hx ⊢
  bv_omega

-- A store to `blocked` keeps the pointer to it.
theorem blkOf_store {m : Mem 64} {S : Addr} {v : Int} (hw : Wf m S) {k : Nat} (hk : k < 2) :
    blkOf (m.storeInt (wordAt (blkOf m S) k) 8 v) S = blkOf m S := by
  have hb := hw.blk_lt
  refine rd_storeInt_of_disjoint fun x hx hy => blk_disj hw (k := 7) (by decide) x hy ?_
  simp only [Mem.Blocks.Inside, or_false] at hx ⊢
  bv_omega

theorem blkOf_store2 {m : Mem 64} {S : Addr} {v w : Int} (hw : Wf m S) :
    blkOf ((m.storeInt (wordAt (blkOf m S) 0) 8 v).storeInt (wordAt (blkOf m S) 1) 8 w) S =
      blkOf m S := by
  have hb := hw.blk_lt
  unfold blkOf
  rw [rd_storeInt_of_disjoint, rd_storeInt_of_disjoint]
  all_goals
    intro x hx hy
    refine blk_disj hw (k := 7) (by decide) x hy ?_
    simp only [Mem.Blocks.Inside, or_false, blkOf] at hx ⊢
    bv_omega

theorem hdr_isSome' {m m' : Mem 64} {S : Addr} (hw : Wf m S)
    (hm : Mem.Mapped (writable m S ++ readable m S) m') {k : Nat} (hk : k < 8) :
    (m'.loadInt (wordAt S k) 8).isSome = true := by
  have hs := hw.struct_lt
  simp only [WORDS] at hs
  refine Mem.Mapped.loadInt_isSome hm (inside_append.mpr ?_)
  by_cases hk3 : k < 3
  · exact Or.inl (Or.inl (by simp only [wordAt]; bv_omega))
  · exact Or.inr (Or.inl (by simp only [wordAt]; bv_omega))

theorem blk_isSome {m m' : Mem 64} {S : Addr} (hw : Wf m S)
    (hm : Mem.Mapped (writable m S ++ readable m S) m') {k : Nat} (hk : k < 2) :
    (m'.loadInt (wordAt (blkOf m S) k) 8).isSome = true := by
  have hb := hw.blk_lt
  refine Mem.Mapped.loadInt_isSome hm (inside_append.mpr (Or.inl
    (inside_of_mem (p := (blkOf m S, 16)) (by simp [writable]) (Or.inl ?_))))
  simp only [wordAt]; bv_omega

-- The two stores to `blocked` keep the frame and the struct.
theorem Fm.blk {m : Mem 64} (hpre : Pre 64 urgentA s) (h : Fm s ra m) (p x : Word) :
    Fm s ra ((m.storeInt (wordAt (blkOf m (rdi s)) 0) 8 p.toInt).storeInt
      (wordAt (blkOf m (rdi s)) 1) 8 x.toInt) := by
  have hfr := hpre.2.1
  have hle := hfr.le
  have hbl := h.wf.blk_lt
  obtain ⟨-, hrd, hwr⟩ := keeps hpre h.un
  generalize hB : blkOf m (rdi s) = B at hbl ⊢
  have hu : Mem.UnchangedOutside [(B, 16)] m
      ((m.storeInt (wordAt B 0) 8 p.toInt).storeInt (wordAt B 1) 8 x.toInt) := by
    have hin : ∀ a : Addr, (a - B).toNat + 8 ≤ 16 → Mem.Blocks.Inside a 8 [(B, 16)] := fun a h => Or.inl h
    refine .storeInt (.storeInt (fun _ _ => rfl) (hin _ ?_) _) (hin _ ?_) _
    all_goals (simp only [wordAt]; bv_omega)
  -- `blocked` lies in `writable`
  have hw : ∀ y, Mem.Blocks.Inside y 1 [(B, 16)] → Mem.Blocks.Inside y 1 (writable s.dmem (rdi s)) :=
    fun y hy => hwr ▸ inside_of_mem (by rw [← hB]; simp [writable]) hy
  have hnw : ∀ y, Mem.Blocks.Inside y 1 [frame 64 s] → ¬ Mem.Blocks.Inside y 1 [(B, 16)] :=
    fun y hy hb => hfr.disj y hy (inside_append.mpr (Or.inl (hw y hb)))
  have hsv : ∀ {k}, 8 ≤ k → k ≤ 64 →
      rd ((m.storeInt (wordAt B 0) 8 p.toInt).storeInt (wordAt B 1) 8 x.toInt)
        (rsp s - BitVec.ofNat 64 k) = rd m (rsp s - BitVec.ofNat 64 k) := fun hk hk' =>
    rd_congr hu fun y hy hb => hnw y (in_frame hle hk hk' y hy) hb
  have hst : ∀ {k}, k < WORDS →
      rd ((m.storeInt (wordAt B 0) 8 p.toInt).storeInt (wordAt B 1) 8 x.toInt)
        (wordAt (rdi s) k) = rd m (wordAt (rdi s) k) := fun hk =>
    rd_congr hu (hB ▸ blk_disj h.wf hk)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hsv (k := 8) (by omega) (by omega)]; exact h.ra
  · rw [hsv (k := 16) (by omega) (by omega)]; exact h.r15
  · rw [hsv (k := 24) (by omega) (by omega)]; exact h.r14
  · rw [hsv (k := 32) (by omega) (by omega)]; exact h.r13
  · rw [hsv (k := 40) (by omega) (by omega)]; exact h.r12
  · rw [hsv (k := 48) (by omega) (by omega)]; exact h.rbp
  · rw [hsv (k := 56) (by omega) (by omega)]; exact h.rbx
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

-- The pops of `.LB79` read the saved words.
theorem Fm.pops {m : Mem 64} (h : Fm s ra m) {a : Addr} (ha : a = rsp s - 56#64) :
    rd m a = s.regs.rbx.toBitVec ∧ rd m (a + 8#64) = s.regs.rbp.toBitVec
      ∧ rd m (a + 8#64 + 8#64) = s.regs.r12.toBitVec
      ∧ rd m (a + 8#64 + 8#64 + 8#64) = s.regs.r13.toBitVec
      ∧ rd m (a + 8#64 + 8#64 + 8#64 + 8#64) = s.regs.r14.toBitVec
      ∧ rd m (a + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) = s.regs.r15.toBitVec := by
  subst ha
  refine ⟨h.rbx, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show rsp s - 56#64 + 8#64 = rsp s - 48#64 by bv_omega]; exact h.rbp
  · rw [show rsp s - 56#64 + 8#64 + 8#64 = rsp s - 40#64 by bv_omega]; exact h.r12
  · rw [show rsp s - 56#64 + 8#64 + 8#64 + 8#64 = rsp s - 32#64 by bv_omega]; exact h.r13
  · rw [show rsp s - 56#64 + 8#64 + 8#64 + 8#64 + 8#64 = rsp s - 24#64 by bv_omega]; exact h.r14
  · rw [show rsp s - 56#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 = rsp s - 16#64 by bv_omega]
    exact h.r15

theorem rsp_pop {X Y : Addr} (h : X = Y - 56#64) :
    X + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 = Y - 8#64 := by
  subst h; bv_omega

theorem retAddr_of {u : MachineData} (hpre : Pre 64 urgentA s) (hm : Fm s ra u.dmem)
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
    {u : MachineData} (hpre : Pre 64 urgentA s) (hm : Fm s ra u.dmem)
    (hsp : u.regs.get64 .rsp = rsp s - 8#64)
    (hr : ∀ q, q ∉ [Reg64.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11, .rsp] →
      u.regs.get64 q = s.regs.get64 q)
    (hR : ∀ t', t'.dmem = u.dmem → rax t' = rax u → urgentR s t') :
    Program.Intercept ls (s.pushRa ra) I'
      (fun a t => a = ra ∧ Post urgentF urgentR s t ∧ (mod urgentF s).Agree s t) u.retAddr.get!
      { regs := u.regs.set64 Reg64.rsp (u.regs.get64 Reg64.rsp + 8#64), zmms := u.zmms,
        status := u.status, dmem := u.dmem } := by
  have hra := retAddr_of hpre hm hsp
  refine Or.inr ⟨⟨by simp [hra], ⟨hm.wf, hm.map, hR _ rfl (by simp [rax])⟩,
    fun q hq => ?_, hm.un⟩, fun _ _ _ => ?_⟩
  · simp only [Reg64s.get64_set64]
    split
    · subst_vars; rw [hsp]; simp only [rsp]; bv_omega
    · exact hr q (by simp_all [mod, urgentF])
  · apply MachineData.stackBelow_of_add_eight
    simp [MachineData.pushRa, hsp]
    bv_omega
end

/-! ## Flags -/

-- The carry flag of `a - b`.
theorem cf_sub (a b : Word) :
    ((((a - b).toNat : Int) != (a.toNat : Int) - (b.toNat : Int)) = true) ↔ a.toNat < b.toNat := by
  rw [bne_iff_ne, ne_eq, BitVec.toNat_sub]
  have := a.isLt; have := b.isLt
  constructor <;> intro h <;> omega

theorem cf_sub' (a b : Word) :
    ((((a - b).toNat : Int) != (a.toNat : Int) - (b.toNat : Int)) = false) ↔ b.toNat ≤ a.toNat := by
  rw [← Bool.not_eq_true, cf_sub]; omega

-- The zero flag of `a - b`.
theorem zf_sub (a b : Word) : ((a - b == BitVec.zero 64) = true) ↔ a = b := by
  rw [beq_iff_eq, show BitVec.zero 64 = 0#64 from rfl]
  constructor <;> intro h <;> bv_omega

theorem zf_sub' (a b : Word) : ((a - b == BitVec.zero 64) = false) ↔ a ≠ b := by
  rw [← Bool.not_eq_true, zf_sub]

-- `rbx + 1` for `rbx < 256`.
theorem toNat_one_add {x : Word} (h : x.toNat < 256) : (1#64 + x).toNat = x.toNat + 1 := by
  rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega

-- The stack at the loop labels.
theorem stack_ok {s t : MachineData} {ra : Int64} (h : t.regs.rsp.toBitVec = rsp s - 56#64) :
    t.StackAtOrBelow (s.pushRa ra) :=
  MachineData.stackAtOrBelow_of_toNat_lt (by
    simp only [Reg64s.get64_rsp, pushRa_rsp, h]
    bv_omega)

/- `stack_ok` for a state literal. The kernel checks `stack_ok h` for a literal
by structure eta against the state the literal was built from, and a field that
differs makes it unfold the bit-vector terms. Here each field is a variable. -/
theorem stack_mk {s : MachineData} {ra : Int64}
    {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64} {z f d}
    (h : a6.toBitVec = rsp s - 56#64) :
    (MachineData.mk ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩
      z f d).StackAtOrBelow (s.pushRa ra) :=
  stack_ok h

theorem get64_rbx_mk {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64} :
    Reg64s.get64 ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩ .rbx
      = a1.toBitVec :=
  rfl

theorem get64_r14_mk {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64} :
    Reg64s.get64 ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩ .r14
      = a14.toBitVec :=
  rfl

/-! ## Invariants -/

section
variable (s : MachineData) (ra : Int64)

abbrev N : Nat := nOf s.dmem (rdi s)

-- The memory and the fixed registers at the loop labels.
structure Lp (t : MachineData) : Prop where
  fm : Fm s ra t.dmem
  st : stOf t.dmem (rdi s) = st s
  rsp : t.regs.rsp.toBitVec = rsp s - 56#64
  rbp : t.regs.rbp.toBitVec = rdi s
  r15 : t.regs.r15.toBitVec = rsi s
  r13 : t.regs.r13.toBitVec = rd s.dmem (wordAt (rdi s) 3)

-- `.LB84`: the scan at the offset `d` in `rbx`, with the result `u` so far in `r14`.
def At84 (t : MachineData) : Prop :=
  Lp s ra t ∧ t.regs.rbx.toNat < N s ∧ urgent (env s) (st s) (rsi s).toNat =
    urgentFrom (env s) (st s) (rsi s).toNat t.regs.rbx.toNat t.regs.r14.toNat

-- `.LB81`: the scan is done at the offset `d` in `rbx`.
def At81 (t : MachineData) : Prop :=
  Lp s ra t ∧ t.regs.rbx.toNat < N s ∧ urgent (env s) (st s) (rsi s).toNat =
    urgentFrom (env s) (st s) (rsi s).toNat (t.regs.rbx.toNat + 1) t.regs.r14.toNat

-- `.LB85`: no slot is bound for `d`, and the target value `v` of `d` in `r12` is not free.
def At85 (t : MachineData) : Prop :=
  At84 s ra t ∧ positionOf (st s) t.regs.rbx.toNat = none
    ∧ t.regs.r12.toBitVec = (env s).target[t.regs.rbx.toNat]!
    ∧ isFree t.regs.r12.toBitVec = false

-- `.LB88`: the copy `c` in `rax` is out of reach.
def At88 (t : MachineData) : Prop :=
  Fm s ra t.dmem ∧ t.regs.rsp.toBitVec = rsp s - 56#64 ∧ t.regs.rbp.toBitVec = rdi s
    ∧ ∃ c, t.regs.rax.toBitVec = BitVec.ofNat 64 c
      ∧ t.regs.rdx.toBitVec = BitVec.ofNat 64 ((st s).len - c) ∧ c + 16 < (st s).len
      ∧ urgent (env s) (st s) (rsi s).toNat = .error (.blocked c ((st s).len - c - 16))

-- The result in `r14` and memory.
def Out (t : MachineData) : Prop :=
  match urgent (env s) (st s) (rsi s).toNat with
  | .ok u => t.regs.r14.toBitVec = BitVec.ofNat 64 u ∧ stOf t.dmem (rdi s) = st s
  | .error (.blocked p x) => t.regs.r14.toBitVec = -1#64
    ∧ rd t.dmem (blkOf t.dmem (rdi s)) = BitVec.ofNat 64 p
    ∧ rd t.dmem (wordAt (blkOf t.dmem (rdi s)) 1) = BitVec.ofNat 64 x
  | .error .assertion => False

-- `.LB79`: the result is in `r14`.
def At79 (t : MachineData) : Prop :=
  Fm s ra t.dmem ∧ t.regs.rsp.toBitVec = rsp s - 56#64 ∧ Out s t

-- The loop variant: `n - d` falls at each back edge.
def V : Label → MachineData → Nat
  | "urgent", _ => 2 * N s + 2
  | ".LB84", t | ".LB85", t => 2 * (N s - t.regs.rbx.toNat) + 1
  | ".LB81", t => 2 * (N s - t.regs.rbx.toNat)
  | _, _ => 0

end

/-! ## The calls in the loop -/

-- The index `x` into the words at `a`.
theorem idx (a x : Addr) : a + x * 8#64 + BitVec.ofInt 64 (Int64.toInt 0) = wordAt a x.toNat := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, wordAt]
  have : BitVec.ofInt 64 (Int64.toInt 0) = 0#64 := by decide
  rw [this, BitVec.toNat_ofNat]
  omega

-- The sign flag of `test x, x`.
theorem ns_test (x : Word) (f : StatusFlags.from_result.Remaining) :
    CondCode.ns.interp (StatusFlags.from_result (x &&& x) f) = !x.msb := by
  simp [CondCode.interp, StatusFlags.from_result]

theorem s_test (x : Word) (f : StatusFlags.from_result.Remaining) :
    CondCode.s.interp (StatusFlags.from_result (x &&& x) f) = x.msb := by
  simp [CondCode.interp, StatusFlags.from_result]

-- The zero flag of `test x, x`.
theorem z_test (x : Word) (f : StatusFlags.from_result.Remaining) :
    CondCode.z.interp (StatusFlags.from_result (x &&& x) f) = (x == 0#64) := by
  simp [CondCode.interp, StatusFlags.from_result]

-- The zero flag of `testb $1, x`.
theorem z_odd (x : Word) (f : StatusFlags.from_result.Remaining) :
    CondCode.z.interp (StatusFlags.from_result (x.take 8 &&& 1#8) f) = (x.toNat % 2 == 0) := by
  simp only [CondCode.interp, StatusFlags.from_result]
  have h : (x.take 8 &&& 1#8).toNat = x.toNat % 2 := by
    simp only [BitVec.take, BitVec.toNat_and, BitVec.extractLsb'_toNat, Nat.shiftRight_zero,
      BitVec.toNat_ofNat]
    rw [show 1 % 2 ^ 8 = 1 from rfl, Nat.and_one_is_mod]
    omega
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, ← h]
  constructor
  · intro h3; rw [h3]; rfl
  · intro h3; exact BitVec.eq_of_toNat_eq (by rw [h3]; rfl)

-- The zero flag of `cmp $1, x`.
theorem nz_one (x : Word) (f : StatusFlags.from_result.Remaining) :
    CondCode.nz.interp (StatusFlags.from_result (x - 1#64) f) = (x != 1#64) := by
  simp only [CondCode.interp, StatusFlags.from_result]
  rw [show BitVec.zero 64 = 0#64 from rfl, bne, Bool.eq_iff_iff]
  simp only [Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq]
  constructor <;> intro h h' <;> apply h <;> bv_omega

-- The zero flag of `test eax, eax` for a `bool` result.
theorem nz_bool (b : Bool) (f : StatusFlags.from_result.Remaining) :
    CondCode.nz.interp (StatusFlags.from_result
      ((BitVec.ofNat 64 b.toNat).take 32 &&& (BitVec.ofNat 64 b.toNat).take 32) f) = b := by
  cases b <;> simp [CondCode.interp, StatusFlags.from_result] <;> decide

-- The zero flag of `cmp y, x`.
theorem z_sub (x y : Word) (f : StatusFlags.from_result.Remaining) :
    CondCode.z.interp (StatusFlags.from_result (x - y) f) = (x == y) := by
  simp only [CondCode.interp, StatusFlags.from_result]
  rw [show BitVec.zero 64 = 0#64 from rfl, Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  constructor <;> intro h <;> bv_omega

theorem nz_sub (x y : Word) (f : StatusFlags.from_result.Remaining) :
    CondCode.nz.interp (StatusFlags.from_result (x - y) f) = (x != y) := by
  simp only [CondCode.interp, StatusFlags.from_result]
  rw [show BitVec.zero 64 = 0#64 from rfl, bne, Bool.eq_iff_iff]
  simp only [Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq]
  constructor <;> intro h h' <;> apply h <;> bv_omega

-- The zero flag of `testb` on two `set` bytes.
theorem z_setb (a b : Bool) (f : StatusFlags.from_result.Remaining) :
    CondCode.z.interp (StatusFlags.from_result
      (BitVec.ofNat 8 a.toNat &&& BitVec.ofNat 8 b.toNat) f) = !(a && b) := by
  cases a <;> cases b <;> simp [CondCode.interp, StatusFlags.from_result] <;> decide

-- The flag `a` of `cmp $15, x`.
theorem a_sub15 (x : Word) (af o : Bool) :
    CondCode.a.interp (StatusFlags.from_result (x - 15#64)
      { cf := (((x - 15#64).toNat : Int) != (x.toNat : Int) - 15), af := af, of := o })
      = decide (15 < x.toNat) := by
  simp only [CondCode.interp, StatusFlags.from_result]
  rw [show BitVec.zero 64 = 0#64 from rfl, Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, Bool.not_eq_true', bne_eq_false_iff_eq, beq_eq_false_iff_ne, ne_eq,
    decide_eq_true_eq, BitVec.toNat_sub]
  have := x.isLt
  constructor
  · intro ⟨h1, h2⟩
    rcases Nat.lt_or_ge 15 x.toNat with h3 | h3; exact h3; exfalso
    apply h2; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat] at h1 ⊢
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]
    omega
  · intro h
    refine ⟨?_, fun h' => ?_⟩
    · simp only [BitVec.toNat_ofNat]; omega
    · have := congrArg BitVec.toNat h'; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at this; omega

-- The depth `len - 1 - c` in `rcx`.
theorem depth {L : Word} {c : Nat} (hc : c < L.toNat) :
    (L - BitVec.ofNat 64 c + BitVec.ofInt 64 (-1 : Int64).toInt).toNat = L.toNat - 1 - c := by
  have := L.isLt
  rw [show BitVec.ofInt 64 (-1 : Int64).toInt = -1#64 by decide]
  rw [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_neg, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : c < 2^64)]
  omega

theorem sub_ofNat {L : Word} {c : Nat} (hc : c ≤ L.toNat) :
    L - BitVec.ofNat 64 c = BitVec.ofNat 64 (L.toNat - c) := by
  have := L.isLt
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : c < 2^64)]
  omega

-- `isFree v` by the tests of `.LB84`.
theorem isFree_zero : isFree 0#64 = true := by decide

theorem isFree_one : isFree 1#64 = false := by decide

theorem isFree_odd {v : Word} (ho : v.toNat % 2 = 1) (h1 : v ≠ 1#64) : isFree v = true := by
  simp [isFree, ho, h1]

theorem isFree_even {v : Word} (h0 : v ≠ 0#64) (he : v.toNat % 2 = 0) : isFree v = false := by
  simp [isFree, h0, he]

-- The sign of an optional position below 256.
theorem msb_encOpt {o : Option Nat} (h : ∀ p, o = some p → p < 256) : (encOpt o).msb = o.isNone := by
  cases o with
  | none => decide
  | some p =>
    have := h p rfl
    simp only [encOpt, Option.isNone_some]
    rw [BitVec.msb_eq_false_iff_two_mul_lt, BitVec.toNat_ofNat]
    omega

section
variable {s : MachineData} {ra : Int64}

-- The registers that a callee keeps.
abbrev Kept (t u : MachineData) : Prop :=
  ∀ q ∉ [Reg64.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11], u.regs.get64 q = t.regs.get64 q

-- A call in the loop with `rdi = rbp` keeps the loop state and the registers.
theorem call_lp {t c u : MachineData} {R : MachineData → MachineData → Prop}
    (hpre : Pre 64 urgentA s) (hl : Lp s ra t) (hp : Post 8 R c u) (hag : (mod 8 c).Agree c u)
    (hc : c.dmem = t.dmem) (hk : Kept t c) (hrdi : rdi c = t.regs.rbp.toBitVec)
    (hst : st' c u = st c) :
    Lp s ra u ∧ u.regs.rbx = t.regs.rbx ∧ u.regs.r12 = t.regs.r12 ∧ u.regs.r14 = t.regs.r14
      ∧ st c = st s := by
  have hk' : Kept t u := fun q hq => (hag.1 q hq).trans (hk q hq)
  have hrdi' : rdi c = rdi s := hrdi.trans hl.rbp
  have hsc : st c = st s := by
    show stOf c.dmem (rdi c) = _
    rw [hc, hrdi']; exact hl.st
  have hrsp : rsp c = rsp s - 56#64 := (hk .rsp (by simp)).trans hl.rsp
  refine ⟨⟨Fm.call hpre hl.fm hc hrsp hrdi' hp hag, ?_, (hk' .rsp (by simp)).trans hl.rsp,
    (hk' .rbp (by simp)).trans hl.rbp, (hk' .r15 (by simp)).trans hl.r15,
    (hk' .r13 (by simp)).trans hl.r13⟩, ?_, ?_, ?_, hsc⟩
  · have : st' c u = stOf u.dmem (rdi s) := by show stOf u.dmem (rdi c) = _; rw [hrdi']
    rw [← this, hst, hsc]
  · exact UInt64.toBitVec_inj.mp (hk' .rbx (by simp))
  · exact UInt64.toBitVec_inj.mp (hk' .r12 (by simp))
  · exact UInt64.toBitVec_inj.mp (hk' .r14 (by simp))

-- `Lp` reads only the memory and the registers `rsp`, `rbp`, `r15` and `r13`.
theorem lp_eq {t t' : MachineData} (h : Lp s ra t) (hm : t'.dmem = t.dmem)
    (h1 : t'.regs.rsp = t.regs.rsp) (h2 : t'.regs.rbp = t.regs.rbp) (h3 : t'.regs.r15 = t.regs.r15)
    (h4 : t'.regs.r13 = t.regs.r13) : Lp s ra t' :=
  ⟨by rw [hm]; exact h.fm, by rw [hm]; exact h.st, by rw [h1]; exact h.rsp, by rw [h2]; exact h.rbp,
    by rw [h3]; exact h.r15, by rw [h4]; exact h.r13⟩

-- `lp_eq` for a state literal. See `stack_mk`.
theorem lp_mk {t : MachineData} {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64}
    {z f d} (h : Lp s ra t) (hm : d = t.dmem) (h1 : a6 = t.regs.rsp) (h2 : a7 = t.regs.rbp)
    (h3 : a15 = t.regs.r15) (h4 : a13 = t.regs.r13) :
    Lp s ra ⟨⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩, z, f, d⟩ :=
  lp_eq h hm h1 h2 h3 h4

-- `At81` and `V` for a state literal. See `stack_mk`.
theorem at81_mk {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64} {z f d} :
    At81 s ra ⟨⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩, z, f, d⟩ ↔
      Lp s ra ⟨⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩, z, f, d⟩
      ∧ a1.toNat < N s ∧ urgent (env s) (st s) (rsi s).toNat =
        urgentFrom (env s) (st s) (rsi s).toNat (a1.toNat + 1) a14.toNat :=
  Iff.rfl

theorem v81_mk {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64} {z f d} :
    V s ".LB81" ⟨⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩, z, f, d⟩
      = 2 * (N s - a1.toNat) :=
  rfl

-- The result of `position_of` for `rbx`.
theorem pos_rax {t c u : MachineData} (hsc : st c = st s) (hrsi : rsi c = t.regs.rbx.toBitVec)
    (hR : positionOfR c u) : u.regs.rax.toBitVec = encOpt (positionOf (st s) t.regs.rbx.toNat) := by
  have h := hR.1
  rw [hsc, hrsi] at h
  exact h

-- The sign of the result of `position_of`.
theorem pos_msb {st : St} {d : Nat} (hlen : st.len ≤ 256) :
    (encOpt (positionOf st d)).msb = (positionOf st d).isNone :=
  msb_encOpt fun _ h => by have := positionOf_lt h; omega

-- The target value at the offset `d`, through `rbp`.
theorem tgt_val {u : MachineData} (hpre : Pre 64 urgentA s) (hl : Lp s ra u) {d : Nat}
    (hd : d < N s) :
    rd u.dmem (wordAt (rd u.dmem (wordAt u.regs.rbp.toBitVec 4)) d) = (env s).target[d]! := by
  have he := (keeps hpre hl.fm.un).1
  have hn : nOf u.dmem (rdi s) = N s := by rw [← env_n, he, env_n]
  rw [hl.rbp, ← he, target_get (by omega)]
  rfl

-- The target value at `rbx` after a call that keeps `rbx`.
theorem tgt_val' {t u : MachineData} (hpre : Pre 64 urgentA s) (hl : Lp s ra u)
    (hbx : u.regs.rbx = t.regs.rbx) (hd : t.regs.rbx.toNat < N s) :
    rd u.dmem (wordAt (rd u.dmem (wordAt u.regs.rbp.toBitVec 4)) u.regs.rbx.toBitVec.toNat)
      = (env s).target[t.regs.rbx.toNat]! := by
  rw [hbx]; exact tgt_val hpre hl hd

theorem none_of_ns {o : Option Nat} (h : (!o.isNone) = false) : o = none := by
  cases o <;> simp_all

theorem tgt_isSome {u : MachineData} (hpre : Pre 64 urgentA s) (hl : Lp s ra u) {d : Nat}
    (hd : d < N s) :
    (u.dmem.loadInt (wordAt (rd u.dmem (wordAt u.regs.rbp.toBitVec 4)) d) 8).isSome = true := by
  have he := (keeps hpre hl.fm.un).1
  have hn : nOf u.dmem (rdi s) = N s := by rw [← env_n, he, env_n]
  have hw := hl.fm.wf
  have ht := hw.tgt_lt
  rw [hl.rbp, show rd u.dmem (wordAt (rdi s) 4) = tgtOf u.dmem (rdi s) from rfl]
  refine Mem.Mapped.loadInt_isSome hw.mapped (inside_append.mpr (Or.inr (Or.inr (Or.inl ?_))))
  rw [hn]
  generalize tgtOf u.dmem (rdi s) = T at ht ⊢
  rw [hn] at ht
  simp only [wordAt]
  bv_omega

-- The result of `is_spilled` for the target value in `r12`.
theorem spill_rax {t c u : MachineData} (hR : isSpilledR c u) (he : env c = env s)
    (hrsi : rsi c = t.regs.r12.toBitVec) (hv : t.regs.r12.toBitVec = (env s).target[t.regs.rbx.toNat]!) :
    u.regs.rax.toBitVec
      = BitVec.ofNat 64 (isSpilled (env s) (env s).target[t.regs.rbx.toNat]!).toNat := by
  have h := hR.1
  rw [he, hrsi, hv] at h
  exact h

-- The result of `shallowest_copy` for the target value in `r12`.
theorem copy_rax {t t1 c u : MachineData} (hR : shallowestCopyR c u) (hsc : st c = st s)
    (h12 : t1.regs.r12 = t.regs.r12) (hrsi : rsi c = t1.regs.r12.toBitVec)
    (hv : t.regs.r12.toBitVec = (env s).target[t.regs.rbx.toNat]!) :
    u.regs.rax.toBitVec = encOpt (shallowestCopy (st s) (env s).target[t.regs.rbx.toNat]!) := by
  have h := hR.1
  rw [hsc, hrsi, h12, hv] at h
  exact h

-- The word `len` at `[rbp]`.
theorem len_rd {u : MachineData} (hl : Lp s ra u) :
    (rd u.dmem (wordAt u.regs.rbp.toBitVec 0)).toNat = (st s).len := by
  rw [hl.rbp, ← st_len, hl.st]

-- The depth `len - 1 - c` of the copy `c` in `rcx`.
theorem depth_rd {u : MachineData} (hl : Lp s ra u) {c : Nat} (hc : c < (st s).len) :
    (rd u.dmem (wordAt u.regs.rbp.toBitVec 0) - BitVec.ofNat 64 c
      + BitVec.ofInt 64 (-1 : Int64).toInt).toNat = (st s).len - 1 - c := by
  rw [depth (by rw [len_rd hl]; exact hc), len_rd hl]

theorem depth_eq {u : MachineData} (hl : Lp s ra u) {c : Nat} (hc : c < (st s).len) :
    (rd u.dmem (wordAt u.regs.rbp.toBitVec 0) - BitVec.ofNat 64 c
      + BitVec.ofInt 64 (-1 : Int64).toInt == 15#64) = decide ((st s).len - 1 - c = 15) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_eq, ← depth_rd hl hc]
  constructor
  · intro h; rw [h]; rfl
  · intro h; exact BitVec.eq_of_toNat_eq h

-- The flag of the `cmp` with 15 before the `cmove` of `.LB85`.
theorem z_depth {u : MachineData} (hl : Lp s ra u) {c : Nat} (hc : c < (st s).len) (f) :
    CondCode.z.interp (StatusFlags.from_result (rd u.dmem (wordAt u.regs.rbp.toBitVec 0)
      - BitVec.ofNat 64 c + BitVec.ofInt 64 (-1 : Int64).toInt - 15#64) f)
      = decide ((st s).len - 1 - c = 15) := by
  rw [z_sub, depth_eq hl hc]

-- The test `c != t && u == n` before the `cmove` of `.LB85`.
theorem dup_cond {u : MachineData} (hl : Lp s ra u) {c : Nat} (hc : c < 256) :
    ((u.regs.r15.toBitVec != BitVec.ofNat 64 c) && (u.regs.r14.toBitVec == u.regs.r13.toBitVec))
      = decide (c ≠ (rsi s).toNat ∧ u.regs.r14.toNat = (env s).n) := by
  rw [hl.r15, hl.r13, env_n]
  show _ = decide (c ≠ (rsi s).toNat
    ∧ u.regs.r14.toBitVec.toNat = (rd s.dmem (wordAt (rdi s) 3)).toNat)
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, bne_iff_ne, beq_iff_eq, decide_eq_true_eq, ne_eq]
  constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨fun h => h1 ?_, ?_⟩ <;> bv_omega

end

-- The sign of the result of `shallowest_copy`.
theorem copy_msb {st : St} {v : Word} (hlen : st.len ≤ 256) :
    (encOpt (shallowestCopy st v)).msb = (shallowestCopy st v).isNone :=
  msb_encOpt fun _ h => by have := shallowestCopy_lt h; omega

end Urgent

end Bbu

-- A jump to a label of the cfg: the stack, the invariant and the variant.
local macro "cfg_goto" : tactic => `(tactic| (
  apply Program.Intercept.intro_label
  · repeat ((fail_if_success (apply List.getElem?_cons_zero)); (apply List.getElem?_cons_succ_of))
    apply List.getElem?_cons_zero
  refine Or.inl ⟨?_, ?_, ?_⟩))

namespace Bbu
open Urgent

theorem urgent_body [Host] [FunDecls]
    (hpos : Spec "position_of" positionOfF positionOfA positionOfR)
    (hcopy : Spec "shallowest_copy" shallowestCopyF shallowestCopyA shallowestCopyR)
    (hspill : Spec "is_spilled" isSpilledF isSpilledA isSpilledR) :
    Body urgentAsm urgentF urgentA urgentR := by
  intro s ra
  refine ⟨fun s₀ ⟨h₀, hpre⟩ => ?_⟩
  subst h₀
  replace hpre : Pre 64 urgentA s := hpre
  refine Program.WP.cfg (fun
      | .entry, t | .label "urgent", t => t = s.pushRa ra
      | .label ".LB84", t => At84 s ra t
      | .label ".LB85", t => At85 s ra t
      | .label ".LB81", t => At81 s ra t
      | .label ".LB88", t => At88 s ra t
      | .label ".LB79", t => At79 s ra t
      | _, _ => False)
    (V s) ?_ rfl
  cfg_cases
  case left t ht =>
    subst ht
    kvcgen64
  case right.left t ht =>
    subst ht
    have hmap0 : Mem.Mapped [frame 64 s] (s.pushRa ra).dmem := hpre.2.1.mapped.storeInt _ _ _
    have hle := hpre.2.1.le
    have hn : rd (pushes s ra) (wordAt s.regs.rdi.toBitVec 3) = rd s.dmem (wordAt s.regs.rdi.toBitVec 3) :=
      rd_pushes_n hpre
    kvcgen64
    case vc1 | vc2 | vc3 | vc4 | vc5 | vc6 =>
      refine Mem.Mapped.loadInt_isSome (bs := [frame 64 s]) ?_ (Or.inl ?_)
      · repeat (first | (with_reducible exact hmap0) | apply Mem.Mapped.storeInt)
      · simp only [Reg64s.get64_rsp, pushRa_rsp, rsp] at *
        bv_omega
    all_goals simp only [pushes_eq, rd_def] at *
    all_goals simp only [disp3, pushRa_rdi, pushRa_rsi, pushRa_rbx, pushRa_rbp, pushRa_r12,
      pushRa_r13, pushRa_r14, pushRa_r15] at *
    case vc7 => exact hdr_isSome (fm_pushes hpre).wf (k := 3) (by omega) rfl
    case vc8 =>
      rename_i hc
      simp only [CondCode.interp_nc, StatusFlags.cf_from_result, Bool.not_eq_true', cf_sub', hn] at hc
      cfg_goto
      · apply MachineData.stackAtOrBelow_of_toNat_lt
        simp only [Reg64s.get64_rsp, pushRa_rsp]
        bv_omega
      · refine ⟨fm_pushes hpre, by simp only [pushRa_rsp]; bv_omega, ?_⟩
        unfold Out
        rw [urgent, urgentFrom_done (by rw [env_n]; exact hc)]
        refine ⟨?_, st_pushes hpre⟩
        rw [env_n]
        simp only [hn, nOf, BitVec.ofNat_toNat, BitVec.setWidth_eq]
        rfl
      · simp [V]
    case vc9 =>
      rename_i hc
      simp only [CondCode.interp_nc, StatusFlags.cf_from_result, Bool.not_eq_false', cf_sub, hn] at hc
      cfg_goto
      · apply MachineData.stackAtOrBelow_of_toNat_lt
        simp only [Reg64s.get64_rsp, pushRa_rsp]
        bv_omega
      · refine ⟨⟨fm_pushes hpre, st_pushes hpre, by simp only [pushRa_rsp]; bv_omega, rfl, rfl, hn⟩,
          hc, ?_⟩
        rw [urgent, env_n]
        simp only [hn, nOf]
        rfl
      · simp [V]
        omega
  case right.right.left t ht =>
    obtain ⟨hfm, hrsp, hrbp, c, hrax, hrdx, hc16, hurg⟩ := ht
    have hlen : (st s).len ≤ 256 := by rw [st_len]; exact hpre.1.len_le
    have hbl := hfm.wf.blk_lt
    kvcgen64
    all_goals simp only [rd_def] at *
    all_goals simp only [disp0, disp1, disp7] at *
    all_goals simp only [Reg64s.get64_rbp, Reg64s.get64_rcx, Reg64s.get64_rax,
      hrbp, hrax, hrdx, blkOf_def]
    case vc1 => exact hdr_isSome hfm.wf (k := 7) (by omega) rfl
    case vc2 => exact blk_isSome hfm.wf hfm.wf.mapped (by decide)
    case vc3 => exact hdr_isSome' hfm.wf (hfm.wf.mapped.storeInt _ _ _) (by decide)
    case vc4 =>
      rw [blkOf_store hfm.wf (by decide)]
      exact blk_isSome hfm.wf (hfm.wf.mapped.storeInt _ _ _) (by decide)
    case vc5 =>
      rw [blkOf_store hfm.wf (by decide)]
      refine ⟨Fm.blk hpre hfm _ _, hrsp, ?_⟩
      simp only [Out, hurg]
      refine ⟨rfl, ?_, ?_⟩
      all_goals rw [blkOf_store2 hfm.wf]
      · rw [rd_storeInt_ne, rd_storeInt_eq]
        · simp [wordAt]
        · simp only [wordAt]; bv_omega
      · rw [rd_storeInt_eq rfl]
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
        omega
    case vc6 => simp [V]
  case right.right.right.left t ht =>
    obtain ⟨hfm, hrsp, hout⟩ := ht
    have hle := hpre.2.1.le
    kvcgen64
    all_goals simp only [rd_def] at *
    case vc1 | vc2 | vc3 | vc4 | vc5 | vc6 =>
      refine Mem.Mapped.loadInt_isSome hfm.map (Or.inl ?_)
      simp only [Reg64s.get64_rsp, hrsp]
      have := s.regs.rsp.toBitVec.isLt
      simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    case vc7 =>
      refine Option.isSome_iff_exists.mpr ⟨ra, retAddr_of hpre hfm ?_⟩
      simp only [Reg64s.get64_rsp]; exact rsp_pop hrsp
    case vc8 =>
      refine ret hpre hfm (by simp only [Reg64s.get64_rsp]; exact rsp_pop hrsp) ?_ ?_
      · intro q hq
        obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hfm.pops hrsp
        cases q <;> simp [h1, h2, h3, h4, h5, h6] at hq ⊢
      · intro t' hm hax
        unfold urgentR Res
        unfold Out at hout
        cases h : urgent (env s) (st s) (rsi s).toNat with
        | ok v =>
          rw [h] at hout
          exact ⟨hax.trans hout.1, by rw [st', hm]; exact hout.2⟩
        | error e =>
          cases e with
          | blocked p x =>
            rw [h] at hout
            exact ⟨hax.trans hout.1, by rw [hm]; exact hout.2.1, by rw [hm]; exact hout.2.2⟩
          | assertion => rw [h] at hout; exact hout.elim
  case right.right.right.right.left t ht =>
    obtain ⟨hlp, hlt, hurg⟩ := ht
    have hn := hpre.1.n_le
    have h1 : (1#64 + t.regs.rbx.toBitVec).toNat = t.regs.rbx.toNat + 1 :=
      toNat_one_add (x := t.regs.rbx.toBitVec) (by simp only [N, UInt64.toNat_toBitVec] at *; omega)
    have h1' : ({ toBitVec := 1#64 + t.regs.rbx.toBitVec } : UInt64).toNat = t.regs.rbx.toNat + 1 := h1
    have hN : t.regs.r13.toNat = nOf s.dmem (rdi s) := by
      rw [← UInt64.toNat_toBitVec, hlp.r13]; rfl
    kvcgen64
    all_goals simp only [UInt64.toNat_toBitVec] at *
    case vc1 =>
      rename_i hc
      simp only [CondCode.interp_z, StatusFlags.zf_from_result, zf_sub] at hc
      have hN1 : t.regs.rbx.toNat + 1 = nOf s.dmem (rdi s) := by rw [← h1, ← hc]; exact hN
      cfg_goto
      · exact stack_ok hlp.rsp
      · refine ⟨hlp.fm, hlp.rsp, ?_⟩
        simp only [Out, hurg, urgentFrom_done (show (env s).n ≤ t.regs.rbx.toNat + 1 by
          rw [env_n]; exact Nat.le_of_eq hN1.symm)]
        exact ⟨by simp, hlp.st⟩
      · simp [V, N, Reg64s.get64_rdi] at hlt ⊢; omega
    case vc2 | vc3 =>
      rename_i hc
      simp only [CondCode.interp_z, StatusFlags.zf_from_result, zf_sub'] at hc
      have hne : t.regs.rbx.toNat + 1 ≠ nOf s.dmem (s.regs.get64 .rdi) := fun h => hc (BitVec.eq_of_toNat_eq (by
        rw [h1]; simp only [UInt64.toNat_toBitVec]; omega))
      first
      | refine ⟨⟨hlp.fm, hlp.st, hlp.rsp, hlp.rbp, hlp.r15, hlp.r13⟩, ?_, ?_⟩
        · simp only [h1', N, rdi]; omega
        · simp only [h1']; exact hurg
      | simp only [V, N, rdi, h1']
        omega
  case right.right.right.right.right.left t ht =>
    obtain ⟨hlp, hlt, hurg⟩ := ht
    have hlen : (st s).len ≤ 256 := by rw [st_len]; exact hpre.1.len_le
    have hn := hpre.1.n_le
    kvcgen64
    all_goals simp only [rd_def] at *
    all_goals try simp only [disp4, idx, ns_test, z_test, z_odd, nz_one] at *
    case vc1 => simp only [Reg64s.get64_rsp, hlp.rsp]; exact Fm.call_isSome hpre hlp.fm
    case vc2 => exact Fm.pre hpre hlp.fm rfl hlp.rsp hlp.rbp trivial
    all_goals
      have hp := ‹Post positionOfF positionOfR _ _›
      have hag := ‹(mod positionOfF _).Agree _ _›
      obtain ⟨hl, hbx, h12, h14, hsc⟩ := call_lp hpre hlp hp hag rfl
        (fun q hq => by cases q <;> first | rfl | simp at hq) rfl hp.2.2.2
      have hrax := pos_rax hsc rfl hp.2.2
    case vc3 =>
      rename_i hns
      rw [hrax, pos_msb hlen] at hns
      have hsome : (positionOf (st s) t.regs.rbx.toNat).isSome = true := by
        revert hns; cases positionOf (st s) t.regs.rbx.toNat <;> simp
      cfg_goto
      · exact stack_ok hl.rsp
      · refine ⟨lp_eq hl rfl rfl rfl rfl rfl, ?_, ?_⟩
        · simp only [hbx]; exact hlt
        · simp only [hbx, h14]
          rw [hurg]
          exact urgentFrom_pos (by rw [env_n]; exact hlt) hsome
      · simp only [V, hbx]; first | omega | simp
    case vc4 =>
      exact hdr_isSome hl.fm.wf (k := 4) (by omega) (by simp only [Reg64s.get64_rbp, hl.rbp])
    case vc5 =>
      rw [hbx]
      exact tgt_isSome hpre hl (d := t.regs.rbx.toBitVec.toNat) hlt
    all_goals
      have hv := tgt_val' hpre hl hbx hlt
      simp only [hv, hrax, pos_msb hlen] at *
      have hnone := none_of_ns ‹_›
      have hd : t.regs.rbx.toNat < (env s).n := by rw [env_n]; exact hlt
      simp only [beq_iff_eq, beq_eq_false_iff_ne, bne_iff_ne, bne_eq_false_iff_eq, ne_eq] at *
    case vc6 =>
      have hv0 : (env s).target[t.regs.rbx.toNat]! = 0#64 := ‹_›
      cfg_goto
      · exact stack_ok hl.rsp
      · refine ⟨lp_eq hl rfl rfl rfl rfl rfl, ?_, ?_⟩
        · simp only [hbx]; exact hlt
        · simp only [hbx, h14]
          rw [hurg]
          exact urgentFrom_skip hd hnone (by rw [hv0, isFree_zero, Bool.true_or])
      · simp only [V, hbx]; first | omega | simp
    case vc7 =>
      rename_i h0 he
      cfg_goto
      · exact stack_ok hl.rsp
      · refine ⟨⟨lp_eq hl rfl rfl rfl rfl rfl, ?_, ?_⟩, ?_, ?_, ?_⟩
        · simp only [hbx]; exact hlt
        · simp only [hbx, h14]; exact hurg
        · simp only [hbx]; exact hnone
        · simp only [hbx]
        · simp only; exact isFree_even h0 he
      · simp only [V, hbx]; first | omega | simp
    case vc8 =>
      rename_i h0 ho h1
      cfg_goto
      · exact stack_ok hl.rsp
      · refine ⟨lp_eq hl rfl rfl rfl rfl rfl, ?_, ?_⟩
        · simp only [hbx]; exact hlt
        · simp only [hbx, h14]
          rw [hurg]
          exact urgentFrom_skip hd hnone (by rw [isFree_odd (by omega) h1, Bool.true_or])
      · simp only [V, hbx]; first | omega | simp
    case vc9 =>
      rename_i h0 ho h1
      refine ⟨⟨lp_eq hl rfl rfl rfl rfl rfl, ?_, ?_⟩, ?_, ?_, ?_⟩
      · simp only [hbx]; exact hlt
      · simp only [hbx, h14]; exact hurg
      · simp only [hbx]; exact hnone
      · simp only [hbx]
      · simp only [h1]; exact isFree_one
    case vc10 =>
      simp only [V, hbx]; simp
  case right.right.right.right.right.right t ht =>
    obtain ⟨⟨hlp, hlt, hurg⟩, hnone, hv, hfree⟩ := ht
    have hlen : (st s).len ≤ 256 := by rw [st_len]; exact hpre.1.len_le
    have hn := hpre.1.n_le
    have he : envOf t.dmem t.regs.rbp.toBitVec = env s := by
      rw [hlp.rbp]; exact (keeps hpre hlp.fm.un).1
    have hd : t.regs.rbx.toNat < (env s).n := by rw [env_n]; exact hlt
    replace hfree : isFree (env s).target[t.regs.rbx.toNat]! ≠ true := by
      rw [← hv, hfree]; decide
    kvcgen64
    all_goals simp only [rd_def] at *
    case vc1 => simp only [Reg64s.get64_rsp, hlp.rsp]; exact Fm.call_isSome hpre hlp.fm
    case vc2 =>
      refine Fm.pre hpre hlp.fm rfl hlp.rsp hlp.rbp ⟨t.regs.rbx.toNat, ?_, ?_⟩
      · show t.regs.rbx.toNat < (envOf t.dmem t.regs.rbp.toBitVec).n
        rw [he]; exact hd
      · show (envOf t.dmem t.regs.rbp.toBitVec).target[t.regs.rbx.toNat]! = t.regs.r12.toBitVec
        rw [he, hv]
    all_goals
      have hp1 := ‹Post isSpilledF isSpilledR _ _›
      obtain ⟨hl1, hbx1, h121, h141, -⟩ := call_lp hpre hlp hp1 ‹(mod isSpilledF _).Agree _ _› rfl
        (fun q hq => by cases q <;> first | rfl | simp at hq) rfl hp1.2.2.2
      have hsp := spill_rax hp1.2.2 he rfl hv
    case vc3 =>
      have hs := ‹CondCode.nz.interp _ = true›
      rw [hsp, nz_bool] at hs
      cfg_goto
      · apply stack_ok; exact hl1.rsp
      · refine ⟨lp_eq hl1 rfl rfl rfl rfl rfl, ?_, ?_⟩
        · simp only [hbx1]; exact hlt
        · simp only [hbx1, h141]
          rw [hurg]
          exact urgentFrom_skip hd hnone (by rw [Bool.eq_false_iff.mpr hfree, hs]; rfl)
      · simp only [V, hbx1]; omega
    case vc4 => simp only [Reg64s.get64_rsp, hl1.rsp]; exact Fm.call_isSome hpre hl1.fm
    case vc5 => exact Fm.pre hpre hl1.fm rfl hl1.rsp hl1.rbp trivial
    all_goals
      have hp2 := ‹Post shallowestCopyF shallowestCopyR _ _›
      obtain ⟨hl2, hbx2, h122, h142, hsc2⟩ := call_lp hpre hl1 hp2
        ‹(mod shallowestCopyF _).Agree _ _› rfl
        (fun q hq => by cases q <;> first | rfl | simp at hq) rfl hp2.2.2.2
      have hcp := copy_rax hp2.2.2 hsc2 h121 rfl hv
      have hs := (by with_reducible assumption : CondCode.nz.interp _ = false)
      rw [hsp, nz_bool] at hs
    case vc6 =>
      have hm := (by with_reducible assumption : CondCode.s.interp _ = true)
      rw [s_test, hcp, copy_msb hlen, Option.isNone_iff_eq_none] at hm
      cfg_goto
      · apply stack_ok; exact hl2.rsp
      · refine ⟨lp_eq hl2 rfl rfl rfl rfl rfl, ?_, ?_⟩
        · simp only [hbx2, hbx1]; exact hlt
        · simp only [hbx2, hbx1, h142, h141]
          rw [hurg]
          exact urgentFrom_none hd hnone (by rw [Bool.eq_false_iff.mpr hfree, hs]; rfl) hm
      · simp only [V, hbx2, hbx1]; omega
    case vc7 =>
      exact hdr_isSome hl2.fm.wf (k := 0) (by omega) (by simp only [Reg64s.get64_rbp, hl2.rbp, disp0])
    all_goals
      have hm := (by with_reducible assumption : CondCode.s.interp _ = false)
      rw [s_test, hcp, copy_msb hlen] at hm
      obtain ⟨c, hc⟩ : ∃ c, shallowestCopy (st s) (env s).target[t.regs.rbx.toNat]! = some c := by
        revert hm; cases shallowestCopy (st s) (env s).target[t.regs.rbx.toNat]! <;> simp
      have hcl := shallowestCopy_lt hc
      have hrax := hcp.trans (show encOpt _ = BitVec.ofNat 64 c by rw [hc]; rfl)
      have ha := (by with_reducible assumption : CondCode.a.interp _ = _)
      rw [a_sub15] at ha
      simp only [disp0, hrax, depth_rd hl2 hcl, decide_eq_true_eq, decide_eq_false_iff_not,
        Nat.not_lt] at ha
      have hsk : (isFree (env s).target[t.regs.rbx.toNat]!
          || isSpilled (env s) (env s).target[t.regs.rbx.toNat]!) = false := by
        rw [Bool.eq_false_iff.mpr hfree, hs]; rfl
    case vc8 =>
      cfg_goto
      · exact stack_mk hl2.rsp
      · show At88 s ra _
        rw [At88, MachineData.dmem_mk, MachineData.regs_mk, Reg64s.rsp_mk, Reg64s.rbp_mk,
          Reg64s.rax_mk, Reg64s.rdx_mk, UInt64.toBitVec_ofBitVec]
        refine ⟨hl2.fm, hl2.rsp, hl2.rbp, c, hrax, ?_, by omega, ?_⟩
        · rw [disp0, hrax, sub_ofNat (by rw [len_rd hl2]; omega), len_rd hl2]
        · rw [hurg, urgentFrom_blocked hd hnone hsk hc (by omega),
            show (st s).len - 1 - c - 15 = (st s).len - c - 16 by omega]
      · left; rw [show ∀ x, V s ".LB88" x = 0 from fun _ => rfl]; simp only [V]; omega
    all_goals
      have hz := (by with_reducible assumption : CondCode.z.interp _ = _)
      rw [z_setb, nz_sub, z_sub, hrax, dup_cond hl2 (Nat.lt_of_lt_of_le hcl hlen), h142, h141] at hz
      simp only [Bool.not_eq_true', Bool.not_eq_false', decide_eq_true_eq, decide_eq_false_iff_not] at hz
    case vc9 =>
      cfg_goto
      · exact stack_mk hl2.rsp
      · refine at81_mk.2 ⟨lp_mk hl2 rfl rfl rfl rfl rfl, ?_, ?_⟩
        · rw [hbx2, hbx1]; exact hlt
        · rw [hbx2, hbx1, h142, h141, hurg, urgentFrom_some hd hnone hsk hc (by omega),
            ite_eq_right (fun h : _ ∧ _ => hz h.2)]
      · left; rw [v81_mk, hbx2, hbx1]; simp only [V]; omega
    case vc10 =>
      cfg_goto
      · exact stack_mk hl2.rsp
      · refine at81_mk.2 ⟨lp_mk hl2 rfl rfl rfl rfl rfl, ?_, ?_⟩
        · rw [hbx2, hbx1]; exact hlt
        · rw [get64_rbx_mk, get64_r14_mk, disp0, hrax, hbx2, hbx1, h142, h141, hurg,
            urgentFrom_some hd hnone hsk hc (by omega)]
          simp only [z_depth hl2 hcl]
          by_cases h15 : (st s).len - 1 - c = 15
          · rw [ite_eq_left (c := decide ((st s).len - 1 - c = 15) = true) (decide_eq_true h15),
              ite_eq_left (c := _ ∧ _) (And.intro h15 hz)]
          · rw [ite_eq_right (c := decide ((st s).len - 1 - c = 15) = true) (by simpa using h15),
              ite_eq_right (c := _ ∧ _) (fun h => h15 h.1)]
      · left; rw [v81_mk, hbx2, hbx1]; simp only [V]; omega

end Bbu
