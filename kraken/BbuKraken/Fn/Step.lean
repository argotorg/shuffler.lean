import BbuKraken.Contracts
import BbuKraken.ModelLemmas

/-!
The body triple of `step` (`c/bbu/step.S`). `step` pushes `r14`, `rbp` and
`rbx`, keeps the struct in `rbp` and the offset `t` in `rbx`, and calls
`urgent`, `position_of`, `take_bound`, `swap_with` and `generate` at
`rsp s - 32`.
-/

open Std.WP Lean.Order
open scoped Program.WP

set_option experimental.vcgen true

namespace Bbu

namespace Step

/-! ## Model lemmas -/

theorem env_n {m : Mem 64} {S : Addr} : (envOf m S).n = nOf m S := by
  simp [Env.n, envOf]

theorem st_len {m : Mem 64} {S : Addr} : (stOf m S).len = (rd m (wordAt S 0)).toNat := by
  simp [St.len, stOf]

theorem st_pending {m : Mem 64} {S : Addr} : (stOf m S).pending = (rd m (wordAt S 1)).toNat := rfl

theorem st_dest {m : Mem 64} {S : Addr} {i : Nat} (hi : i < (rd m (wordAt S 0)).toNat) :
    (stOf m S).dest i = (rd m (wordAt S (DEST + i))).toNat := by
  simp [St.dest, stOf, hi, slotOf]

theorem urgentFrom_le {e : Env} {st : St} {t : Nat} :
    ∀ k d u r, e.n - d = k → u ≤ e.n → urgentFrom e st t d u = .ok r → r ≤ e.n := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro d u r hk hu h
    rw [urgentFrom] at h
    split at h
    · have ih' := fun u' (hu' : u' ≤ e.n) (h' : urgentFrom e st t (d + 1) u' = .ok r) =>
        ih (e.n - (d + 1)) (by omega) (d + 1) u' r rfl hu' h'
      split at h
      · exact ih' u hu h
      · dsimp only at h
        split at h
        · exact ih' u hu h
        · split at h
          · exact ih' u hu h
          · split at h
            · cases h
            · exact ih' _ (by split <;> omega) h
    · cases h; exact hu

theorem urgent_le {e : Env} {st : St} {t u : Nat} (h : urgent e st t = .ok u) : u ≤ e.n :=
  urgentFrom_le _ t e.n u rfl (Nat.le_refl _) h

theorem positionOf_lt {st : St} {d p : Nat} (h : positionOf st d = some p) : p < st.len := by
  simp only [positionOf, List.findIdx?_eq_some_iff_getElem] at h
  exact h.1

-- The branch of `step` on the slot bound for `t`.
def afterTake (t : Nat) (r : St × Bool) : M (St × Next) :=
  if r.2 then .ok (r.1, .next (t + 1)) else placeTop r.1 t

def afterGen (t : Nat) (st : St) : M (St × Next) :=
  if t < st.len ∧ st.dest t = t then .ok (st, .next (t + 1)) else placeTop st t

def bound (e : Env) (st : St) (t : Nat) : M (St × Next) :=
  match positionOf st t with
  | some b => (takeBound st t b).bind (afterTake t)
  | none => (generate e st t).bind (afterGen t)

-- The branch of `step` on the result `u` of `urgent`.
def afterUrgent (e : Env) (st : St) (t u : Nat) : M (St × Next) :=
  if u ≠ e.n ∧ u ≠ t ∧ st.len < t + MAX_SWAP_DEPTH then (generate e st u).map (·, .next t)
  else if u = e.n ∧ t < st.len ∧ st.len < e.n ∧ positionOf st st.len = none ∧
      st.len < t + MAX_SWAP_DEPTH then (generate e st st.len).map (·, .next t)
  else bound e st t

theorem step_eq {e : Env} {st : St} {t : Nat} (h : ¬ (t < st.len ∧ st.dest t = t))
    (hp : st.pending ≠ 0) : step e st t = (urgent e st t).bind (afterUrgent e st t) := by
  simp only [step, h, hp, ite_false]
  rfl

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
@[simp] theorem pushRa_r14 : (s.pushRa ra).regs.r14 = s.regs.r14 := rfl
theorem pushRa_rsp : (s.pushRa ra).regs.rsp.toBitVec = rsp s - 8#64 := by simp [MachineData.pushRa]
end

/-! ## Memory lemmas -/

section
variable {s : MachineData} {ra : Int64}

-- The saved words, the struct and the frame in the memory `m` of `step`.
structure Fm (s : MachineData) (ra : Int64) (m : Mem 64) : Prop where
  ra : rd m (rsp s - 8#64) = ra.toBitVec
  r14 : rd m (rsp s - 16#64) = s.regs.r14.toBitVec
  rbp : rd m (rsp s - 24#64) = s.regs.rbp.toBitVec
  rbx : rd m (rsp s - 32#64) = s.regs.rbx.toBitVec
  wf : Wf m (rdi s)
  map : Mem.Mapped [frame 152 s] m
  un : Mem.UnchangedOutside (mod 152 s).mem s.dmem m

-- A change in the blocks of `step` keeps the environment and the regions.
theorem keeps {m : Mem 64} (hpre : Pre 152 stepA s)
    (hu : Mem.UnchangedOutside (mod 152 s).mem s.dmem m) :
    envOf m (rdi s) = env s ∧ readable m (rdi s) = readable s.dmem (rdi s)
      ∧ writable m (rdi s) = writable s.dmem (rdi s) :=
  Post.env (t := { s with dmem := m }) hpre ⟨fun _ _ => rfl, hu⟩

theorem Fm.n {m : Mem 64} (hpre : Pre 152 stepA s) (h : Fm s ra m) :
    nOf m (rdi s) = nOf s.dmem (rdi s) := by
  have := congrArg Env.n (keeps hpre h.un).1
  rwa [env_n, env_n] at this

-- The 8 bytes `k` bytes below `rsp s` lie in the frame.
theorem in_frame (_hle : 152 ≤ (rsp s).toNat) {k : Nat} (hk : 8 ≤ k) (hk' : k ≤ 152) :
    ∀ x, Mem.Blocks.Inside x 1 [(rsp s - BitVec.ofNat 64 k, 8)] →
      Mem.Blocks.Inside x 1 [frame 152 s] := by
  intro x hx
  simp only [Mem.Blocks.Inside, or_false] at hx ⊢
  bv_omega

-- The frame of a callee at `rsp s - 32` lies in the frame.
theorem callee_in_frame {c : MachineData} {G : Nat} (hG : 32 + G ≤ 152)
    (_hle : 152 ≤ (rsp s).toNat) (hrsp : rsp c = rsp s - 32#64) :
    ∀ x, Mem.Blocks.Inside x 1 [frame G c] → Mem.Blocks.Inside x 1 [frame 152 s] := by
  intro x hx
  simp only [Mem.Blocks.Inside, or_false, hrsp] at hx ⊢
  bv_omega

-- The saved words do not overlap the frame of a callee at `rsp s - 32`.
theorem saved_not_callee {c : MachineData} {G : Nat} (hG : 32 + G ≤ 152)
    (_hle : 152 ≤ (rsp s).toNat) (hrsp : rsp c = rsp s - 32#64) {k : Nat} (hk : 8 ≤ k)
    (hk' : k ≤ 32) :
    ∀ x, Mem.Blocks.Inside x 1 [(rsp s - BitVec.ofNat 64 k, 8)] →
      ¬ Mem.Blocks.Inside x 1 [frame G c] := by
  intro x hx hc
  simp only [Mem.Blocks.Inside, or_false, hrsp] at hx hc
  bv_omega

-- A callee at `rsp s - 32` keeps the saved words and the blocks of `step`.
theorem Fm.call {m : Mem 64} {c t : MachineData} {G : Nat} {R : MachineData → MachineData → Prop}
    (hG : 32 + G ≤ 152) (hpre : Pre 152 stepA s) (h : Fm s ra m) (hc : c.dmem = m)
    (hrsp : rsp c = rsp s - 32#64) (hrdi : rdi c = rdi s) (hp : Post G R c t)
    (hag : (mod G c).Agree c t) : Fm s ra t.dmem := by
  have hfr := hpre.2.1
  have hle := hfr.le
  have hwr := (keeps hpre h.un).2.2
  have hu : Mem.UnchangedOutside (frame G c :: writable s.dmem (rdi s)) m t.dmem := by
    have := hag.2
    simp only [mod, hc, hrdi, hwr] at this
    exact this
  -- `writable` does not overlap the frame
  have hnw : ∀ x, Mem.Blocks.Inside x 1 [frame 152 s] →
      ¬ Mem.Blocks.Inside x 1 (writable s.dmem (rdi s)) :=
    fun x hx hw => hfr.disj x hx (inside_append.mpr (Or.inl hw))
  have hsv : ∀ {k}, 8 ≤ k → k ≤ 32 →
      rd t.dmem (rsp s - BitVec.ofNat 64 k) = rd m (rsp s - BitVec.ofNat 64 k) := fun hk hk' =>
    rd_congr hu fun x hx hl => by
      rcases hl with hl | hl
      · exact saved_not_callee hG hle hrsp hk hk' x hx (Or.inl hl)
      · exact hnw x (in_frame hle hk (by omega) x hx) hl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hsv (k := 8) (by omega) (by omega)]; exact h.ra
  · rw [hsv (k := 16) (by omega) (by omega)]; exact h.r14
  · rw [hsv (k := 24) (by omega) (by omega)]; exact h.rbp
  · rw [hsv (k := 32) (by omega) (by omega)]; exact h.rbx
  · rw [← hrdi]; exact hp.1
  · intro x hx
    by_cases hxG : Mem.Blocks.Inside x 1 [frame G c]
    · exact hp.2.1 x hxG
    · rw [hu x fun hl => hl.elim (fun hl => hxG (Or.inl hl)) (hnw x hx)]
      exact h.map x hx
  · intro x hx
    have hx' : ¬ Mem.Blocks.Inside x 1 (frame G c :: writable s.dmem (rdi s)) := fun hl =>
      hl.elim (fun hl => hx (Or.inl (by
        have := callee_in_frame hG hle hrsp x (Or.inl hl)
        simpa only [Mem.Blocks.Inside, or_false] using this))) (fun hl => hx (Or.inr hl))
    rw [hu x hx']
    exact h.un x hx

-- The precondition of a callee at `rsp s - 32`.
theorem Fm.pre {m : Mem 64} {c : MachineData} {G : Nat} {A : MachineData → Prop}
    (hG : 32 + G ≤ 152) (hpre : Pre 152 stepA s) (h : Fm s ra m) (hc : c.dmem = m)
    (hrsp : rsp c = rsp s - 32#64) (hrdi : rdi c = rdi s) (hA : A c) : Pre G A c := by
  obtain ⟨-, hr, hwr⟩ := keeps hpre h.un
  refine ⟨by rw [hc, hrdi]; exact h.wf, ?_, hA⟩
  exact FrameOk.sub (k := 32) hpre.2.1 hpre.1 hrdi hrsp hG (hc ▸ h.map) (hc ▸ hr) (hc ▸ hwr)

-- The return address slot of a callee at `rsp s - 32` is mapped.
theorem Fm.call_isSome {m : Mem 64} (hpre : Pre 152 stepA s) (h : Fm s ra m) :
    (m.loadInt (rsp s - 32#64 - 8#64) 8).isSome = true := by
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
  ((t.dmem.storeInt (R - 8#64) 8 s.regs.r14.toBitVec.toInt).storeInt
    (R - 8#64 - 8#64) 8 s.regs.rbp.toBitVec.toInt).storeInt
    (R - 8#64 - 8#64 - 8#64) 8 s.regs.rbx.toBitVec.toInt

-- Fold the memory after the pushes, as `kvcgen64` gives it.
theorem pushes_eq : ((Mem.storeInt (s.pushRa ra).dmem ((s.pushRa ra).regs.rsp.toBitVec - 8#64) 8
    s.regs.r14.toBitVec.toInt).storeInt
    ((s.pushRa ra).regs.rsp.toBitVec - 8#64 - 8#64) 8 s.regs.rbp.toBitVec.toInt).storeInt
    ((s.pushRa ra).regs.rsp.toBitVec - 8#64 - 8#64 - 8#64) 8
      s.regs.rbx.toBitVec.toInt = pushes s ra := rfl

theorem unchanged_pushes :
    Mem.UnchangedOutside [frame 152 s] s.dmem (pushes s ra) := by
  have hin : ∀ a : Addr, (a - (rsp s - BitVec.ofNat 64 152)).toNat + 8 ≤ 152 →
      Mem.Blocks.Inside a 8 [frame 152 s] := fun a h => Or.inl h
  have hrsp : (s.pushRa ra).regs.rsp.toBitVec = rsp s - 8#64 := by simp [MachineData.pushRa]
  simp only [pushes, MachineData.dmem_pushRa, hrsp]
  refine .storeInt (.storeInt (.storeInt (.storeInt
    (fun _ _ => rfl) (hin _ ?_) _) (hin _ ?_) _) (hin _ ?_) _) (hin _ ?_) _
  all_goals (simp only [rsp] at *; bv_omega)

theorem fm_pushes (hpre : Pre 152 stepA s) : Fm s ra (pushes s ra) := by
  have hle := hpre.2.1.le
  have hrsp : (s.pushRa ra).regs.rsp.toBitVec = rsp s - 8#64 := by simp [MachineData.pushRa]
  have hu := unchanged_pushes (s := s) (ra := ra)
  have hd := disjoint_symm hpre.2.1.disj
  refine ⟨?_, ?_, ?_, ?_, Wf.congr_of_disjoint hu hpre.1 hd, ?_, ?_⟩
  all_goals try simp only [pushes, hrsp]
  · rw [rd_storeInt_ne, rd_storeInt_ne, rd_storeInt_ne, MachineData.dmem_pushRa, rd_storeInt_eq rfl]
    all_goals first | rfl | bv_omega
  · rw [rd_storeInt_ne, rd_storeInt_ne, rd_storeInt_eq]
    all_goals first | rfl | bv_omega
  · rw [rd_storeInt_ne, rd_storeInt_eq]
    all_goals first | rfl | bv_omega
  · rw [rd_storeInt_eq]
    all_goals first | rfl | bv_omega
  · simp only [MachineData.dmem_pushRa]
    exact hpre.2.1.mapped.storeInt _ _ _ |>.storeInt _ _ _ |>.storeInt _ _ _ |>.storeInt _ _ _
  · intro x hx
    exact hu x fun h => hx (Or.inl (h.elim id False.elim))

theorem st_pushes (hpre : Pre 152 stepA s) : stOf (pushes s ra) (rdi s) = st s :=
  stOf_congr unchanged_pushes hpre.1 (disjoint_symm hpre.2.1.disj)

-- A word of the header or of the stack arrays is mapped.
theorem hdr_isSome {m : Mem 64} {S : Addr} (hw : Wf m S) {k : Nat} (hk : k < 8) :
    (m.loadInt (wordAt S k) 8).isSome = true := by
  have hs := hw.struct_lt
  simp only [WORDS_eq] at hs
  refine Mem.Mapped.loadInt_isSome hw.mapped (inside_append.mpr ?_)
  by_cases hk3 : k < 3
  · exact Or.inl (Or.inl (by simp only [wordAt]; bv_omega))
  · exact Or.inr (Or.inl (by simp only [wordAt]; bv_omega))

theorem arr_isSome {m : Mem 64} {S : Addr} (hw : Wf m S) {k : Nat} (hk1 : STACK ≤ k)
    (hk : k < WORDS) : (m.loadInt (wordAt S k) 8).isSome = true := by
  have hs := hw.struct_lt
  simp only [WORDS_eq, STACK] at hs hk hk1
  refine Mem.Mapped.loadInt_isSome hw.mapped (inside_append.mpr ?_)
  exact Or.inl (Or.inr (Or.inl (by simp only [wordAt, STACK, MAX_N]; bv_omega)))
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
theorem Fm.blk {m : Mem 64} (hpre : Pre 152 stepA s) (h : Fm s ra m) (p x : Word) :
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
  have hw : ∀ y, Mem.Blocks.Inside y 1 [(B, 16)] →
      Mem.Blocks.Inside y 1 (writable s.dmem (rdi s)) :=
    fun y hy => hwr ▸ inside_of_mem (by rw [← hB]; simp [writable]) hy
  have hnw : ∀ y, Mem.Blocks.Inside y 1 [frame 152 s] → ¬ Mem.Blocks.Inside y 1 [(B, 16)] :=
    fun y hy hb => hfr.disj y hy (inside_append.mpr (Or.inl (hw y hb)))
  have hsv : ∀ {k}, 8 ≤ k → k ≤ 152 →
      rd ((m.storeInt (wordAt B 0) 8 p.toInt).storeInt (wordAt B 1) 8 x.toInt)
        (rsp s - BitVec.ofNat 64 k) = rd m (rsp s - BitVec.ofNat 64 k) := fun hk hk' =>
    rd_congr hu fun y hy hb => hnw y (in_frame hle hk hk' y hy) hb
  have hst : ∀ {k}, k < WORDS →
      rd ((m.storeInt (wordAt B 0) 8 p.toInt).storeInt (wordAt B 1) 8 x.toInt)
        (wordAt (rdi s) k) = rd m (wordAt (rdi s) k) := fun hk =>
    rd_congr hu (hB ▸ blk_disj h.wf hk)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hsv (k := 8) (by omega) (by omega)]; exact h.ra
  · rw [hsv (k := 16) (by omega) (by omega)]; exact h.r14
  · rw [hsv (k := 24) (by omega) (by omega)]; exact h.rbp
  · rw [hsv (k := 32) (by omega) (by omega)]; exact h.rbx
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

-- The pops of `.LB89` read the saved words.
theorem Fm.pops {m : Mem 64} (h : Fm s ra m) {a : Addr} (ha : a = rsp s - 32#64) :
    rd m a = s.regs.rbx.toBitVec ∧ rd m (a + 8#64) = s.regs.rbp.toBitVec
      ∧ rd m (a + 8#64 + 8#64) = s.regs.r14.toBitVec := by
  subst ha
  refine ⟨h.rbx, ?_, ?_⟩
  · rw [show rsp s - 32#64 + 8#64 = rsp s - 24#64 by bv_omega]; exact h.rbp
  · rw [show rsp s - 32#64 + 8#64 + 8#64 = rsp s - 16#64 by bv_omega]; exact h.r14

theorem retAddr_of {u : MachineData} (hpre : Pre 152 stepA s) (hm : Fm s ra u.dmem)
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
    {u : MachineData} (hpre : Pre 152 stepA s) (hm : Fm s ra u.dmem)
    (hsp : u.regs.get64 .rsp = rsp s - 8#64)
    (hr : ∀ q, q ∉ [Reg64.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11, .rsp] →
      u.regs.get64 q = s.regs.get64 q)
    (hR : ∀ t', t'.dmem = u.dmem → rax t' = rax u → stepR s t') :
    Program.Intercept ls (s.pushRa ra) I'
      (fun a t => a = ra ∧ Post stepF stepR s t ∧ (mod stepF s).Agree s t) u.retAddr.get!
      { regs := u.regs.set64 Reg64.rsp (u.regs.get64 Reg64.rsp + 8#64), zmms := u.zmms,
        status := u.status, dmem := u.dmem } := by
  have hra := retAddr_of hpre hm hsp
  refine Or.inr ⟨⟨by simp [hra], ⟨hm.wf, hm.map, hR _ rfl (by simp [rax])⟩,
    fun q hq => ?_, hm.un⟩, fun _ _ _ => ?_⟩
  · simp only [Reg64s.get64_set64]
    split
    · subst_vars; rw [hsp]; exact BitVec.sub_add_cancel _ _
    · exact hr q (by simp_all [mod, stepF])
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

theorem sf_test (v : Word) (r) : CondCode.s.interp (StatusFlags.from_result (v &&& v) r) = v.msb := by
  simp [CondCode.interp, StatusFlags.from_result]

theorem ns_test (v : Word) (r) :
    CondCode.ns.interp (StatusFlags.from_result (v &&& v) r) = !v.msb := by
  simp [CondCode.interp, StatusFlags.from_result]

theorem z_test (v : Word) (r) : CondCode.z.interp (StatusFlags.from_result (v &&& v) r) = (v == 0) := by
  simp [CondCode.interp, StatusFlags.from_result]

theorem z_sub (a b : Word) (r) : CondCode.z.interp (StatusFlags.from_result (a - b) r) = (a == b) := by
  rw [CondCode.interp_z, StatusFlags.zf_from_result, Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq,
    BitVec.zero_eq]
  constructor <;> intro h <;> bv_omega

theorem nz_sub (a b : Word) (r) : CondCode.nz.interp (StatusFlags.from_result (a - b) r) = !(a == b) := by
  rw [CondCode.interp_nz, ← CondCode.interp_z, z_sub]

theorem a_sub16 (x : Word) (af of : Bool) :
    CondCode.a.interp (StatusFlags.from_result (x - 16#64)
      { cf := (((x - 16#64).toNat : Int) != (x.toNat : Int) - 16), af := af, of := of }) =
      decide (16 < x.toNat) := by
  rw [CondCode.interp_a, StatusFlags.cf_from_result, StatusFlags.zf_from_result, Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, Bool.not_eq_true', bne_eq_false_iff_eq, beq_eq_false_iff_ne,
    decide_eq_true_eq, ne_eq, BitVec.zero_eq]
  rw [BitVec.toNat_sub]
  have := x.isLt
  constructor
  · intro ⟨h1, h2⟩; bv_omega
  · intro h; constructor <;> bv_omega

-- The displacement `8 * k` of a word in a struct.
theorem disp (a : Addr) (k : Nat) (i : Int64) (h : i.toInt = 8 * k := by decide) :
    a + BitVec.ofInt 64 i.toInt = wordAt a k := by
  rw [h, show (8 * (k : Int)) = ((8 * k : Nat) : Int) by omega, BitVec.ofInt_natCast]
theorem disp0 (a : Addr) : a + BitVec.ofInt 64 (Int64.toInt 0) = wordAt a 0 := disp a 0 0
theorem disp1 (a : Addr) : a + BitVec.ofInt 64 (Int64.toInt 8) = wordAt a 1 := disp a 1 8
theorem disp3 (a : Addr) : a + BitVec.ofInt 64 (Int64.toInt 24) = wordAt a 3 := disp a 3 24
theorem disp7 (a : Addr) : a + BitVec.ofInt 64 (Int64.toInt 56) = wordAt a 7 := disp a 7 56

-- The word of `dest[i]`.
theorem disp_dest (a i : Word) :
    a + i * 8#64 + BitVec.ofInt 64 (Int64.toInt 8256) = wordAt a (DEST + i.toNat) := by
  simp only [wordAt, DEST_eq]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofInt]
  have : Int64.toInt 8256 = 8256 := by decide
  rw [this]
  omega

theorem ofInt_one : BitVec.ofInt 64 (Int64.toInt 1) = 1#64 := by decide
theorem ofInt_m1 : BitVec.ofInt 64 (Int64.toInt (-1)) = -1#64 := by decide
theorem ofInt_16 : BitVec.ofInt 64 (Int64.toInt 16) = 16#64 := by decide

end Step

end Bbu

namespace Bbu
namespace Step

/-! ## Invariants -/

section
variable (s : MachineData) (ra : Int64)

abbrev T : Nat := (rsi s).toNat

-- The memory and the fixed registers after the entry block.
structure Base (t : MachineData) : Prop where
  fm : Fm s ra t.dmem
  rsp : t.regs.rsp.toBitVec = rsp s - 32#64
  rbp : t.regs.rbp.toBitVec = rdi s
  rbx : t.regs.rbx.toBitVec = rsi s
  r12 : t.regs.r12 = s.regs.r12
  r13 : t.regs.r13 = s.regs.r13
  r15 : t.regs.r15 = s.regs.r15

-- `.LB90`: `t` is not done.
def At90 (t : MachineData) : Prop :=
  Base s ra t ∧ st' s t = st s ∧ ¬ (T s < (st s).len ∧ (st s).dest (T s) = T s)

-- `.LB92`: `urgent` gives `u`, which is `t` or `n`.
def At92 (t : MachineData) : Prop :=
  Base s ra t ∧ st' s t = st s ∧ (st s).pending ≠ 0 ∧ ∃ u, rcx t = BitVec.ofNat 64 u
    ∧ rdx t = BitVec.ofNat 64 (env s).n ∧ (u = T s ∨ u = (env s).n)
    ∧ step (env s) (st s) (T s) = afterUrgent (env s) (st s) (T s) u

-- `.LB106`: generate the slot for `u`.
def At106 (t : MachineData) : Prop :=
  Base s ra t ∧ st' s t = st s ∧ (st s).pending ≠ 0
    ∧ step (env s) (st s) (T s) = (generate (env s) (st s) (rax t).toNat).map (·, .next (T s))

-- `.LB93`: the slot bound for `t`.
def At93 (t : MachineData) : Prop :=
  Base s ra t ∧ st' s t = st s ∧ (st s).pending ≠ 0
    ∧ step (env s) (st s) (T s) = bound (env s) (st s) (T s)

-- `.LB94`: no slot is bound for `t`.
def At94 (t : MachineData) : Prop :=
  Base s ra t ∧ st' s t = st s ∧ (st s).pending ≠ 0
    ∧ step (env s) (st s) (T s) = (generate (env s) (st s) (T s)).bind (afterGen (T s))

-- `.LB96`: swap the top into `t`.
def At96 (t : MachineData) : Prop :=
  Base s ra t ∧ T s < (st' s t).len ∧ (st' s t).dest (T s) ≠ T s
    ∧ rdx t = BitVec.ofNat 64 (st' s t).len ∧ (st' s t).ops.length < cap s
    ∧ step (env s) (st s) (T s) = placeTop (st' s t) (T s)

-- `.LB97`: `t` is done.
def At97 (t : MachineData) : Prop :=
  Base s ra t ∧ step (env s) (st s) (T s) = .ok (st' s t, .next (T s + 1))

-- `.LB107`: the top is out of reach.
def At107 (t : MachineData) : Prop :=
  Base s ra t ∧ rdx t = BitVec.ofNat 64 ((st' s t).len - T s) ∧ T s + 17 < (st' s t).len
    ∧ step (env s) (st s) (T s) = .error (.blocked (T s) ((st' s t).len - 1 - T s - 16))

-- `.LB99`: no slot is pending.
def At99 (t : MachineData) : Prop :=
  Base s ra t ∧ step (env s) (st s) (T s) = .ok (st' s t, .finish)

-- `.LB103`, `.LB104`: an assertion fails.
def AtErr (t : MachineData) : Prop :=
  Base s ra t ∧ step (env s) (st s) (T s) = .error .assertion

-- `.LB89`: the result is in `rax` and memory.
def At89 (t : MachineData) : Prop :=
  Fm s ra t.dmem ∧ t.regs.rsp.toBitVec = rsp s - 32#64 ∧ t.regs.rbx.toBitVec = rsi s
    ∧ t.regs.r12 = s.regs.r12 ∧ t.regs.r13 = s.regs.r13 ∧ t.regs.r15 = s.regs.r15
    ∧ stepR s t

end

-- The variant: each jump goes to a label with a smaller value.
def V : Label → Nat
  | "step" => 20
  | ".LB90" => 19
  | ".LB92" => 18
  | ".LB93" => 17
  | ".LB94" => 16
  | ".LB96" => 15
  | ".LB97" => 14
  | ".LB106" | ".LB107" | ".LB99" | ".LB103" | ".LB104" => 5
  | _ => 0

/-! ## Helpers of the cases -/

section
variable {s : MachineData} {ra : Int64}

theorem stack_of {t : MachineData} (h : t.regs.rsp.toBitVec = rsp s - 32#64) :
    t.StackAtOrBelow (s.pushRa ra) := by
  apply MachineData.stackAtOrBelow_of_toNat_lt
  simp only [Reg64s.get64_rsp, pushRa_rsp, h]
  bv_omega

theorem base_pushes (hpre : Pre 152 stepA s) {t : MachineData} (hm : t.dmem = pushes s ra)
    (hsp : t.regs.rsp.toBitVec = (s.pushRa ra).regs.rsp.toBitVec - 8#64 - 8#64 - 8#64)
    (hbp : t.regs.rbp.toBitVec = rdi s) (hbx : t.regs.rbx.toBitVec = rsi s)
    (h12 : t.regs.r12 = s.regs.r12) (h13 : t.regs.r13 = s.regs.r13)
    (h15 : t.regs.r15 = s.regs.r15) : Base s ra t :=
  ⟨hm ▸ fm_pushes hpre, by rw [hsp, pushRa_rsp]; bv_omega, hbp, hbx, h12, h13, h15⟩

-- `stepR` reads only `rax` and the memory.
theorem stepR_congr {t t' : MachineData} (h : stepR s t) (hm : t'.dmem = t.dmem)
    (hr : rax t' = rax t) : stepR s t' := by
  revert h
  unfold stepR Res
  split <;> simp only [Ok, st', hm, hr, imp_self]

-- An error of a callee is the error of `step`.
theorem res_err {α β : Type} {S : Addr} {r : M α} {r' : M β} {e : Err} {Q : α → Prop}
    {Q' : β → Prop} {t : MachineData} (h : Res S r Q t) (hr : r = .error e)
    (hr' : r' = .error e) : Res S r' Q' t := by
  subst hr hr'
  cases e <;> exact h


theorem step_done {e : Env} {st : St} {t : Nat} (h : t < st.len ∧ st.dest t = t) :
    step e st t = .ok (st, .next (t + 1)) := by
  simp [step, h]

theorem dest_iff {m : Mem 64} {S : Addr} {t : Word} (hi : t.toNat < (rd m (wordAt S 0)).toNat) :
    (stOf m S).dest t.toNat = t.toNat ↔ rd m (wordAt S (DEST + t.toNat)) = t := by
  rw [st_dest hi]
  exact ⟨BitVec.eq_of_toNat_eq, fun h => by rw [h]⟩

theorem step_fin {e : Env} {st : St} {t : Nat} (h : ¬ (t < st.len ∧ st.dest t = t))
    (hp : st.pending = 0) : step e st t = .ok (st, .finish) := by
  simp [step, h, hp]

theorem msb_small {u : Nat} (h : u ≤ 1024) : (BitVec.ofNat 64 u).msb = false := by
  rw [BitVec.msb_eq_decide]
  simp only [BitVec.toNat_ofNat, decide_eq_false_iff_not, Nat.not_le]
  omega

theorem toNat_small {u : Nat} (h : u ≤ 1024) : (BitVec.ofNat 64 u).toNat = u := by
  simp only [BitVec.toNat_ofNat]; omega

theorem eq_toNat_of_ofNat {u : Nat} {w : Word} (hu : u ≤ 1024) (h : BitVec.ofNat 64 u = w) :
    u = w.toNat := by
  rw [← h, toNat_small hu]

theorem n_le (hpre : Pre 152 stepA s) : (env s).n ≤ 1024 := by
  rw [env_n]; exact hpre.1.n_le

theorem T_lt (hpre : Pre 152 stepA s) : T s < (env s).n := hpre.2.2.1

theorem rsi_small (hpre : Pre 152 stepA s) : (rsi s).toNat + 16 < 2 ^ 64 := by
  have h1 := n_le hpre
  have h2 := T_lt hpre
  simp only [T] at h2
  omega

theorem rd_n {m : Mem 64} (hpre : Pre 152 stepA s) (h : Fm s ra m) :
    rd m (wordAt (rdi s) 3) = BitVec.ofNat 64 (env s).n := by
  rw [env_n, ← h.n hpre]
  simp only [nOf, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem rd_len {m : Mem 64} : (rd m (wordAt (rdi s) 0)).toNat = (stOf m (rdi s)).len := st_len.symm

theorem rd_pending {m : Mem 64} : (rd m (wordAt (rdi s) 1)).toNat = (stOf m (rdi s)).pending := rfl

theorem ofNat_T : BitVec.ofNat 64 (T s) = rsi s := by simp [T]

theorem toNat_add {w : Word} {k : Nat} (h : w.toNat + k < 2 ^ 64) :
    (w + BitVec.ofNat 64 k).toNat = w.toNat + k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega


theorem ofNat_inj64 {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (h : BitVec.ofNat 64 a = BitVec.ofNat 64 b) : a = b := by
  have := congrArg BitVec.toNat h
  rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this

theorem ofNat_pred {k : Nat} (h : 0 < k) :
    BitVec.ofNat 64 k + -1#64 = BitVec.ofNat 64 (k - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel, BitVec.ofNat_add, BitVec.add_assoc,
    show BitVec.ofNat 64 1 + -1#64 = 0#64 by decide, BitVec.add_zero]

theorem sub_of {L T : Nat} (hlt : T ≤ L) :
    BitVec.ofNat 64 L - BitVec.ofNat 64 T = BitVec.ofNat 64 (L - T) := by
  obtain ⟨j, rfl⟩ : ∃ j, L = j + T := ⟨L - T, by omega⟩
  rw [Nat.add_sub_cancel, BitVec.ofNat_add, BitVec.add_sub_cancel]

theorem last_of {L T : Nat} (hL : L ≤ 1024) (hlt : T < L)
    (h : BitVec.ofNat 64 L + -1#64 = BitVec.ofNat 64 T) : T = L - 1 := by
  rw [ofNat_pred (by omega)] at h
  exact (ofNat_inj64 (by omega) (by omega) h).symm

theorem gap_of {L T : Nat} (hL : L ≤ 1024) (hlt : T < L) :
    (BitVec.ofNat 64 L - BitVec.ofNat 64 T + -1#64).toNat = L - 1 - T := by
  rw [sub_of (by omega), ofNat_pred (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega
theorem len_of {m : Mem 64} (h : stOf m (rdi s) = st s) :
    (rd m (wordAt (rdi s) 0)).toNat = (st s).len := by
  rw [rd_len]; exact congrArg St.len h
theorem res_err_msb {α : Type} {S : Addr} {e : Err} {Q : α → Prop} {t : MachineData}
    (h : Res S (.error e : M α) Q t) : (rax t).msb = true := by
  cases e <;> simp only [Res] at h
  · rw [h.1]; decide
  · rw [h]; decide

end


/-! ## Calls -/

section
variable {s : MachineData} {ra : Int64} {t c t' : MachineData}

theorem res_mono {α : Type} {S : Addr} {r : M α} {Q Q' : α → Prop} {u : MachineData}
    (h : Res S r Q u) (hq : ∀ a, Q a → Q' a) : Res S r Q' u := by
  cases r with
  | ok a => exact hq a h
  | error e => cases e <;> exact h


theorem res_ok_of_msb {α : Type} {S : Addr} {r : M α} {Q : α → Prop} {u : MachineData}
    (h : Res S r Q u) (hm : (rax u).msb = false) : ∃ a, r = .ok a ∧ Q a := by
  cases r with
  | ok a => exact ⟨a, rfl, h⟩
  | error e => rw [res_err_msb h] at hm; cases hm

-- `js` to `.LB89` after a call: the error of the callee is the error of `step`.
theorem at89_err {α : Type} {t' : MachineData} {r : M α} {Q : α → Prop} (hb : Base s ra t')
    (h : Res (rdi s) r Q t') (hm : (rax t').msb = true)
    (hq : ∀ a, r = .ok a → Q a → (rax t').msb = false)
    (hstep : ∀ e, r = .error e → step (env s) (st s) (T s) = .error e) : At89 s ra t' := by
  refine ⟨hb.fm, hb.rsp, hb.rbx, hb.r12, hb.r13, hb.r15, ?_⟩
  cases hr : r with
  | ok a => rw [hr] at h; rw [hq a hr h] at hm; cases hm
  | error e =>
    rw [hr] at h
    exact res_err h rfl (hstep e hr)
-- A callee at `rsp s - 32` keeps `Base`.
theorem Base.call {G : Nat} {R : MachineData → MachineData → Prop} (hG : 32 + G ≤ 152)
    (hpre : Pre 152 stepA s) (hb : Base s ra t) (hp : Post G R c t')
    (hag : (mod G c).Agree c t') (hc : c.dmem = t.dmem)
    (hsp : c.regs.rsp = t.regs.rsp) (hdi : rdi c = rdi s) (hbp : c.regs.rbp = t.regs.rbp)
    (hbx : c.regs.rbx = t.regs.rbx) (h12 : c.regs.r12 = t.regs.r12)
    (h13 : c.regs.r13 = t.regs.r13) (h15 : c.regs.r15 = t.regs.r15) : Base s ra t' := by
  have hrsp : Bbu.rsp c = Bbu.rsp s - 32#64 := by
    simp only [Bbu.rsp, Reg64s.get64_rsp, hsp]; exact hb.rsp
  have hr := fun (q : Reg64) (hq : q ∉ (mod G c).regs) => hag.reg q hq
  simp only [mod, List.mem_cons, List.not_mem_nil, or_false] at hr
  have h1 := hr .rsp (by decide)
  have h2 := hr .rbp (by decide)
  have h3 := hr .rbx (by decide)
  have h4 := hr .r12 (by decide)
  have h5 := hr .r13 (by decide)
  have h6 := hr .r15 (by decide)
  simp only [Reg64s.get64_rsp, Reg64s.get64_rbp, Reg64s.get64_rbx, Reg64s.get64_r12,
    Reg64s.get64_r13, Reg64s.get64_r15] at h1 h2 h3 h4 h5 h6
  refine ⟨Fm.call hG hpre hb.fm hc hrsp hdi hp hag, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h1, hsp]; exact hb.rsp
  · rw [h2, hbp]; exact hb.rbp
  · rw [h3, hbx]; exact hb.rbx
  · rw [UInt64.toBitVec_inj.mp h4, h12]; exact hb.r12
  · rw [UInt64.toBitVec_inj.mp h5, h13]; exact hb.r13
  · rw [UInt64.toBitVec_inj.mp h6, h15]; exact hb.r15

-- `Base.call` for a call state that keeps the callee-saved registers of `t`.
theorem Base.callR {G : Nat} {R : MachineData → MachineData → Prop} {a d si : UInt64}
    {f : StatusFlags} (hG : 32 + G ≤ 152) (hpre : Pre 152 stepA s) (hb : Base s ra t)
    (hp : Post G R ⟨⟨a, t.regs.rbx, t.regs.rcx, d, si, ⟨t.regs.rbp.toBitVec⟩, t.regs.rsp,
      t.regs.rbp, t.regs.r8, t.regs.r9, t.regs.r10, t.regs.r11, t.regs.r12, t.regs.r13,
      t.regs.r14, t.regs.r15⟩, t.zmms, f, t.dmem⟩ t')
    (hag : (mod G ⟨⟨a, t.regs.rbx, t.regs.rcx, d, si, ⟨t.regs.rbp.toBitVec⟩, t.regs.rsp,
      t.regs.rbp, t.regs.r8, t.regs.r9, t.regs.r10, t.regs.r11, t.regs.r12, t.regs.r13,
      t.regs.r14, t.regs.r15⟩, t.zmms, f, t.dmem⟩).Agree ⟨⟨a, t.regs.rbx, t.regs.rcx, d, si,
      ⟨t.regs.rbp.toBitVec⟩, t.regs.rsp, t.regs.rbp, t.regs.r8, t.regs.r9, t.regs.r10,
      t.regs.r11, t.regs.r12, t.regs.r13, t.regs.r14, t.regs.r15⟩, t.zmms, f, t.dmem⟩ t') :
    Base s ra t' :=
  Base.call hG hpre hb hp hag rfl rfl hb.rbp rfl rfl rfl rfl rfl

theorem env_call (hpre : Pre 152 stepA s) (hb : Base s ra t) (hc : c.dmem = t.dmem)
    (hdi : rdi c = rdi s) : env c = env s := by
  show envOf c.dmem (rdi c) = _
  rw [hc, hdi]; exact (keeps hpre hb.fm.un).1

theorem st_call (hc : c.dmem = t.dmem) (hdi : rdi c = rdi s) : st c = st' s t := by
  show stOf c.dmem (rdi c) = _
  rw [hc, hdi]

theorem cap_call (hpre : Pre 152 stepA s) (hb : Base s ra t) (hc : c.dmem = t.dmem)
    (hdi : rdi c = rdi s) : cap c = cap s := by
  show 6 * nOf c.dmem (rdi c) = _
  rw [hc, hdi, Fm.n hpre hb.fm]

theorem urgent_post (hpre : Pre 152 stepA s) (hb : Base s ra t) (hp : Post urgentF urgentR c t')
    (hc : c.dmem = t.dmem) (hdi : rdi c = rdi s) (hsi : rsi c = rsi s) :
    Res (rdi s) (urgent (env s) (st' s t) (T s))
      (fun u => rax t' = BitVec.ofNat 64 u ∧ st' s t' = st' s t) t' := by
  have h := hp.2.2
  unfold urgentR at h
  rw [hdi, env_call hpre hb hc hdi, st_call hc hdi, hsi] at h
  exact res_mono h fun _ ⟨h1, h2⟩ => ⟨h1, by simpa only [st', hdi, id] using h2⟩

theorem positionOf_post (hp : Post positionOfF positionOfR c t') (hc : c.dmem = t.dmem)
    (hdi : rdi c = rdi s) :
    rax t' = encOpt (positionOf (st' s t) (rsi c).toNat) ∧ st' s t' = st' s t := by
  have h := hp.2.2
  unfold positionOfR at h
  rw [st_call hc hdi] at h
  exact ⟨h.1, by simpa only [st', hdi] using h.2⟩

theorem takeBound_post (hp : Post takeBoundF takeBoundR c t') (hc : c.dmem = t.dmem)
    (hdi : rdi c = rdi s) :
    Res (rdi s) (takeBound (st' s t) (rsi c).toNat (rdx c).toNat)
      (fun r => rax t' = (if r.2 then 0#64 else 1#64) ∧ st' s t' = r.1) t' := by
  have h := hp.2.2
  unfold takeBoundR at h
  rw [hdi, st_call hc hdi] at h
  exact res_mono h fun _ ⟨h1, h2⟩ => ⟨h1, by simpa only [st', hdi, id] using h2⟩

theorem generate_post (hpre : Pre 152 stepA s) (hb : Base s ra t)
    (hp : Post generateF generateR c t')
    (hc : c.dmem = t.dmem) (hdi : rdi c = rdi s) :
    Res (rdi s) (generate (env s) (st' s t) (rsi c).toNat)
      (fun r => rax t' = 0#64 ∧ st' s t' = r) t' := by
  have h := hp.2.2
  unfold generateR at h
  rw [hdi, env_call hpre hb hc hdi, st_call hc hdi] at h
  exact res_mono h fun _ ⟨h1, h2⟩ => ⟨h1, by simpa only [st', hdi, id] using h2⟩

theorem swapWith_post (hp : Post swapWithF swapWithR c t') (hc : c.dmem = t.dmem)
    (hdi : rdi c = rdi s) :
    Res (rdi s) (swapWith (st' s t) (rsi c).toNat) (fun r => rax t' = 0#64 ∧ st' s t' = r) t' := by
  have h := hp.2.2
  unfold swapWithR at h
  rw [hdi, st_call hc hdi] at h
  exact res_mono h fun _ ⟨h1, h2⟩ => ⟨h1, by simpa only [st', hdi, id] using h2⟩


theorem generate_post_T (hpre : Pre 152 stepA s) (hb : Base s ra t)
    (hp : Post generateF generateR c t') (hc : c.dmem = t.dmem) (hdi : rdi c = rdi s)
    (hsi : rsi c = rsi s) (hst : st' s t = st s) :
    Res (rdi s) (generate (env s) (st s) (T s)) (fun r => rax t' = 0#64 ∧ st' s t' = r) t' := by
  have h := generate_post hpre hb hp hc hdi
  rw [hst, hsi] at h
  exact h

theorem at89_of {u : MachineData} (hb : Base s ra u)
    (h : Res (rdi s) (step (env s) (st s) (T s)) (Ok s u (fun r => encNext r.2) Prod.fst) u) :
    At89 s ra u :=
  ⟨hb.fm, hb.rsp, hb.rbx, hb.r12, hb.r13, hb.r15, h⟩

theorem placeTop_len {st : St} {t : Nat} (h : st.len ≤ t) : placeTop st t = .error .assertion := by
  simp [placeTop, h]

theorem placeTop_dest {st : St} {t : Nat} (h : st.dest t = t) :
    placeTop st t = .error .assertion := by
  simp [placeTop, h]

theorem rd_len' {m : Mem 64} {S : Addr} : rd m (wordAt S 0) = BitVec.ofNat 64 (stOf m S).len := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat]; simp [St.len, stOf]; exact (Nat.mod_eq_of_lt (BitVec.isLt _)).symm

theorem dest_isSome {m : Mem 64} {S : Addr} (hw : Wf m S) {i : Word}
    (hi : i.toNat < (rd m (wordAt S 0)).toNat) :
    (m.loadInt (wordAt S (DEST + i.toNat)) 8).isSome = true := by
  have : _ ≤ 1024 := hw.len_le
  refine arr_isSome hw (by simp only [STACK, DEST_eq]; omega) ?_
  simp only [WORDS_eq, DEST_eq]
  omega

-- `.LB107`: write `blocked` and return `-1`.
theorem at107_out (hpre : Pre 152 stepA s) (hb : Base s ra t)
    (hdx : rdx t = BitVec.ofNat 64 ((st' s t).len - T s)) (hlt : T s + 17 < (st' s t).len)
    (hs : step (env s) (st s) (T s) = .error (.blocked (T s) ((st' s t).len - 1 - T s - 16)))
    {u : MachineData}
    (hm : u.dmem = (t.dmem.storeInt (wordAt (rd t.dmem (wordAt t.regs.rbp.toBitVec 7)) 0) 8
      t.regs.rbx.toBitVec.toInt).storeInt (wordAt (rd (t.dmem.storeInt
        (wordAt (rd t.dmem (wordAt t.regs.rbp.toBitVec 7)) 0) 8 t.regs.rbx.toBitVec.toInt)
        (wordAt t.regs.rbp.toBitVec 7)) 1) 8 (t.regs.rdx.toBitVec - 17#64).toInt)
    (hsp : u.regs.rsp = t.regs.rsp) (hbx : u.regs.rbx = t.regs.rbx) (h12 : u.regs.r12 = t.regs.r12)
    (h13 : u.regs.r13 = t.regs.r13) (h15 : u.regs.r15 = t.regs.r15) (hax : rax u = -1#64) :
    At89 s ra u := by
  have hw := hb.fm.wf
  have hL : _ ≤ 1024 := hw.len_le
  rw [rd_len] at hL
  rw [hb.rbp, blkOf_def, blkOf_def, blkOf_store hw (by decide), hb.rbx] at hm
  have hu : u.dmem = ((t.dmem.storeInt (wordAt (blkOf t.dmem (rdi s)) 0) 8 (rsi s).toInt).storeInt
      (wordAt (blkOf t.dmem (rdi s)) 1) 8 (rdx t - 17#64).toInt) := hm
  refine ⟨hu ▸ hb.fm.blk hpre _ _, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hsp]; exact hb.rsp
  · rw [hbx]; exact hb.rbx
  · rw [h12]; exact hb.r12
  · rw [h13]; exact hb.r13
  · rw [h15]; exact hb.r15
  · show Res _ (step _ _ _) _ _
    rw [hs]
    refine ⟨hax, ?_, ?_⟩
    · rw [hu, blkOf_store2 hw, rd_storeInt_ne (by simp only [wordAt]; bv_omega),
        rd_storeInt_eq (by simp only [wordAt]; bv_omega)]
      exact ofNat_T.symm
    · rw [hu, blkOf_store2 hw, rd_storeInt_eq rfl, hdx]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
      omega

theorem swapWith_post_T (hp : Post swapWithF swapWithR c t') (hc : c.dmem = t.dmem)
    (hdi : rdi c = rdi s) (hsi : rsi c = rsi s) :
    Res (rdi s) (swapWith (st' s t) (T s)) (fun r => rax t' = 0#64 ∧ st' s t' = r) t' := by
  have h := swapWith_post hp hc hdi
  rw [hsi] at h
  exact h

theorem placeTop_last {st : St} {t : Nat} (hlt : t < st.len) (hd : st.dest t ≠ t)
    (h : t = st.len - 1) : placeTop st t = .ok (st, .next (t + 1)) := by
  unfold placeTop
  rw [if_neg (by omega), if_neg (by omega)]

theorem placeTop_far {st : St} {t : Nat} (hlt : t < st.len) (hd : st.dest t ≠ t)
    (h : 16 < st.len - 1 - t) :
    placeTop st t = .error (.blocked t (st.len - 1 - t - 16)) := by
  unfold placeTop
  rw [if_neg (by omega), if_pos (by omega), if_pos (by simp only [MAX_SWAP_DEPTH]; omega)]
  rfl

theorem placeTop_swap {st : St} {t : Nat} (hlt : t < st.len) (hd : st.dest t ≠ t)
    (hne : t ≠ st.len - 1) (h : st.len - 1 - t ≤ 16) :
    placeTop st t = (swapWith st t).map (·, .next (t + 1)) := by
  unfold placeTop
  rw [if_neg (by omega), if_pos (by omega), if_neg (by simp only [MAX_SWAP_DEPTH]; omega)]

theorem gen_pre (hpre : Pre 152 stepA s) (hb : Base s ra t) (hst : st' s t = st s)
    (hpd : (st s).pending ≠ 0) (hc : c.dmem = t.dmem) (hdi : rdi c = rdi s) : generateA c := by
  have h1 := n_le hpre
  have h2 := hpre.2.2.2.1
  have h3 := hpre.2.2.2.2
  unfold generateA MAX_N
  rw [st_call hc hdi, hst, cap_call hpre hb hc hdi]
  omega


theorem swap_pre (hpre : Pre 152 stepA s) (hb : Base s ra t) (hops : (st' s t).ops.length < cap s)
    (hc : c.dmem = t.dmem) (hdi : rdi c = rdi s) : swapWithA c := by
  unfold swapWithA
  rw [st_call hc hdi, cap_call hpre hb hc hdi]
  exact hops

theorem at97_of {r : St} {u : MachineData} (hb : Base s ra u) (hm : u.dmem = t'.dmem)
    (hst : st' s t' = r) (h : step (env s) (st s) (T s) = .ok (r, .next (T s + 1))) : At97 s ra u := by
  refine ⟨hb, ?_⟩
  rw [h, ← hst]
  show _ = Except.ok (stOf u.dmem _, _)
  rw [hm]
theorem res_err_congr {α β : Type} {S : Addr} {e : Err} {Q : α → Prop} {Q' : β → Prop}
    {u : MachineData} (h : Res S (.error e : M α) Q t') (hm : u.dmem = t'.dmem)
    (hr : rax u = rax t') : Res S (.error e : M β) Q' u := by
  cases e <;> simp only [Res, hm, hr] at h ⊢ <;> exact h

-- `testq rax; cmovns rbx, rax` after a call that gives `0` on `ok`.
theorem at89_cmov {g : M St} {u : MachineData} (hb : Base s ra t') (hbu : Base s ra u)
    (h : Res (rdi s) g (fun r => rax t' = 0#64 ∧ st' s t' = r) t')
    (hstep : step (env s) (st s) (T s) = g.map (·, .next (T s))) (hm : u.dmem = t'.dmem)
    (hax : rax u = if (rax t').msb = false then t'.regs.rbx.toBitVec else rax t') :
    At89 s ra u := by
  refine ⟨hbu.fm, hbu.rsp, hbu.rbx, hbu.r12, hbu.r13, hbu.r15, ?_⟩
  show Res _ (step _ _ _) _ _
  rw [hstep]
  cases g with
  | ok r =>
    obtain ⟨h1, h2⟩ := h
    refine ⟨?_, ?_⟩
    · rw [hax, h1]
      exact hb.rbx.trans ofNat_T.symm
    · show stOf u.dmem _ = r
      rw [hm]; exact h2
  | error e =>
    refine res_err_congr h hm ?_
    rw [hax, res_err_msb h]; rfl
end

/-! ## State literals

The kernel is slow when it checks that a `kvcgen64` state literal and the state it came from
agree on a field: it tries structure eta and unfolds the flag terms. These lemmas state the
literal with variable fields, so that a use is an instance. -/

section
variable {s : MachineData} {ra : Int64} {u t' : MachineData}
  {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : UInt64} {z : RegZmms} {f : StatusFlags}
  {d : Mem 64} {a si : UInt64} {r : Reg64s}

-- The state at a call from `u`: `rdi` is `rbp`, and the saved registers are those of `u`.
abbrev callSt (u : MachineData) (a d si : UInt64) (f : StatusFlags) : MachineData :=
  ⟨⟨a, u.regs.rbx, u.regs.rcx, d, si, ⟨u.regs.rbp.toBitVec⟩, u.regs.rsp, u.regs.rbp, u.regs.r8,
    u.regs.r9, u.regs.r10, u.regs.r11, u.regs.r12, u.regs.r13, u.regs.r14, u.regs.r15⟩,
    u.zmms, f, u.dmem⟩

theorem Fm.preR {G : Nat} {A : MachineData → Prop} {dx : UInt64} (hG : 32 + G ≤ 152)
    (hpre : Pre 152 stepA s) (hb : Base s ra u) (hA : A (callSt u a dx si f)) :
    Pre G A (callSt u a dx si f) :=
  Fm.pre hG hpre hb.fm rfl hb.rsp hb.rbp hA

theorem st_callR {dx : UInt64} (hb : Base s ra u) : st (callSt u a dx si f) = st' s u :=
  st_call rfl hb.rbp

theorem cap_callR {dx : UInt64} (hpre : Pre 152 stepA s) (hb : Base s ra u) :
    cap (callSt u a dx si f) = cap s :=
  cap_call hpre hb rfl hb.rbp

theorem swap_preR {dx : UInt64} (hpre : Pre 152 stepA s) (hb : Base s ra u)
    (hops : (st' s u).ops.length < cap s) : swapWithA (callSt u a dx si f) :=
  swap_pre hpre hb hops rfl hb.rbp

theorem swapWith_postR {dx : UInt64} (hb : Base s ra u)
    (hp : Post swapWithF swapWithR (callSt u a dx si f) t') (hsi : si.toBitVec = rsi s) :
    Res (rdi s) (swapWith (st' s u) (T s)) (fun r => rax t' = 0#64 ∧ st' s t' = r) t' :=
  swapWith_post_T hp rfl hb.rbp hsi

theorem positionOf_postR {dx : UInt64} (hb : Base s ra u)
    (hp : Post positionOfF positionOfR (callSt u a dx si f) t') (hsi : si.toBitVec = rsi s) :
    t'.regs.rax.toBitVec = encOpt (positionOf (st' s u) (T s)) ∧ st' s t' = st' s u := by
  show _ = encOpt (positionOf _ (rsi s).toNat) ∧ _
  rw [← hsi]
  exact positionOf_post hp rfl hb.rbp

theorem takeBound_postR {w : BitVec 64} (hb : Base s ra u)
    (hp : Post takeBoundF takeBoundR (callSt u a ⟨w⟩ si f) t') (hsi : si.toBitVec = rsi s) :
    Res (rdi s) (takeBound (st' s u) (T s) w.toNat)
      (fun r => rax t' = (if r.2 then 0#64 else 1#64) ∧ st' s t' = r.1) t' := by
  show Res _ (takeBound _ (rsi s).toNat _) _ _
  rw [← hsi]
  exact takeBound_post hp rfl hb.rbp

theorem take_preR {dx : UInt64} (hpre : Pre 152 stepA s) (hb : Base s ra u)
    (hdx : dx.toBitVec.toNat < (st' s u).len) (hops : (st' s u).ops.length < cap s) :
    takeBoundA (callSt u a dx si f) := by
  unfold takeBoundA
  rw [st_callR hb, cap_callR hpre hb]
  exact ⟨hdx, hops⟩

theorem pos_none {st : St} {k : Nat} {w : Word} (hL : st.len ≤ 1024)
    (h : w = encOpt (positionOf st k)) (hm : w.msb = true) : positionOf st k = none := by
  cases hp : positionOf st k with
  | none => rfl
  | some p =>
    rw [hp] at h
    rw [h, encOpt, msb_small (Nat.le_trans (Nat.le_of_lt (positionOf_lt hp)) hL)] at hm
    cases hm

theorem pos_some {st : St} {k : Nat} {w : Word} (hL : st.len ≤ 1024)
    (h : w = encOpt (positionOf st k)) (hm : w.msb = false) : positionOf st k = some w.toNat := by
  cases hp : positionOf st k with
  | none =>
    rw [hp] at h
    rw [h, encOpt] at hm
    exact absurd hm (by decide)
  | some p =>
    rw [hp] at h
    rw [h, encOpt, toNat_small (Nat.le_trans (Nat.le_of_lt (positionOf_lt hp)) hL)]

theorem bound_none {e : Env} {st : St} {k : Nat} (h : positionOf st k = none) :
    bound e st k = (generate e st k).bind (afterGen k) := by
  simp only [bound, h]

theorem bound_some {e : Env} {st : St} {k b : Nat} (h : positionOf st k = some b) :
    bound e st k = (takeBound st k b).bind (afterTake k) := by
  simp only [bound, h]

theorem take_true {w : Word} {b : Bool} (h : w = if b then 0#64 else 1#64) (h0 : w = 0) :
    b = true := by
  cases b
  · rw [h] at h0; exact absurd h0 (by decide)
  · rfl

theorem take_false {w : Word} {b : Bool} (h : w = if b then 0#64 else 1#64) (h0 : w ≠ 0) :
    b = false := by
  cases b
  · rfl
  · exact absurd h h0

theorem succ_T {w : Word} (h : w = rsi s) : w + 1#64 = BitVec.ofNat 64 (T s + 1) := by
  rw [h, BitVec.ofNat_add, ofNat_T]

theorem at96_mk2 {q : St} (hb : Base s ra
      ⟨⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩, z, f, u.dmem⟩)
    (hst : st' s u = q) (hlt : T s < q.len) (hd : q.dest (T s) ≠ T s)
    (h3 : a3.toBitVec = BitVec.ofNat 64 q.len) (hops : q.ops.length < cap s)
    (hs : step (env s) (st s) (T s) = placeTop q (T s)) :
    At96 s ra ⟨⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩, z, f,
      u.dmem⟩ := by
  subst hst
  exact ⟨hb, hlt, hd, h3, hops, hs⟩

theorem stack_mk (h : a6.toBitVec = rsp s - 32#64) :
    (MachineData.mk ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩
      z f d).StackAtOrBelow (s.pushRa ra) :=
  stack_of h

theorem stack_mk' (h : r.rsp.toBitVec = rsp s - 32#64) :
    (MachineData.mk r z f d).StackAtOrBelow (s.pushRa ra) :=
  stack_of h

theorem base_mk (hb : Base s ra u) (h1 : a1 = u.regs.rbx) (h6 : a6 = u.regs.rsp)
    (h7 : a7 = u.regs.rbp) (h12 : a12 = u.regs.r12) (h13 : a13 = u.regs.r13)
    (h15 : a15 = u.regs.r15) :
    Base s ra ⟨⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩, z, f,
      u.dmem⟩ := by
  subst h1 h6 h7 h12 h13 h15
  exact ⟨hb.fm, hb.rsp, hb.rbp, hb.rbx, hb.r12, hb.r13, hb.r15⟩

theorem base_mk' (hb : Base s ra u) : Base s ra ⟨u.regs, z, f, u.dmem⟩ :=
  ⟨hb.fm, hb.rsp, hb.rbp, hb.rbx, hb.r12, hb.r13, hb.r15⟩

theorem at89_mk' (h : At89 s ra u) : At89 s ra ⟨u.regs, z, f, u.dmem⟩ :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, stepR_congr h.2.2.2.2.2.2 rfl rfl⟩

theorem at89_mk :
    At89 s ra ⟨⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩, z, f, d⟩ ↔
      Fm s ra d ∧ a6.toBitVec = rsp s - 32#64 ∧ a1.toBitVec = rsi s ∧ a12 = s.regs.r12
        ∧ a13 = s.regs.r13 ∧ a15 = s.regs.r15
        ∧ Res (rdi s) (step (env s) (st s) (T s))
          (fun r => a0.toBitVec = encNext r.2 ∧ stOf d (rdi s) = r.1)
          ⟨⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩, z, f, d⟩ :=
  Iff.rfl

theorem at94_mk' :
    At94 s ra ⟨u.regs, z, f, u.dmem⟩ ↔ Base s ra ⟨u.regs, z, f, u.dmem⟩ ∧ st' s u = st s
      ∧ (st s).pending ≠ 0
      ∧ step (env s) (st s) (T s) = (generate (env s) (st s) (T s)).bind (afterGen (T s)) :=
  Iff.rfl

theorem at97_mk' :
    At97 s ra ⟨u.regs, z, f, u.dmem⟩ ↔ Base s ra ⟨u.regs, z, f, u.dmem⟩
      ∧ step (env s) (st s) (T s) = .ok (st' s u, .next (T s + 1)) :=
  Iff.rfl

theorem at97_mk :
    At97 s ra ⟨⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩, z, f, d⟩ ↔
      Base s ra ⟨⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩, z, f, d⟩
      ∧ step (env s) (st s) (T s) = .ok (stOf d (rdi s), .next (T s + 1)) :=
  Iff.rfl

theorem at107_mk :
    At107 s ra ⟨⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩, z, f, d⟩ ↔
      Base s ra ⟨⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩, z, f, d⟩
      ∧ a3.toBitVec = BitVec.ofNat 64 ((stOf d (rdi s)).len - T s)
      ∧ T s + 17 < (stOf d (rdi s)).len
      ∧ step (env s) (st s) (T s)
        = .error (.blocked (T s) ((stOf d (rdi s)).len - 1 - T s - 16)) :=
  Iff.rfl

theorem at96_mk :
    At96 s ra ⟨⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩, z, f, d⟩ ↔
      Base s ra ⟨⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩, z, f, d⟩
      ∧ T s < (stOf d (rdi s)).len ∧ (stOf d (rdi s)).dest (T s) ≠ T s
      ∧ a3.toBitVec = BitVec.ofNat 64 (stOf d (rdi s)).len ∧ (stOf d (rdi s)).ops.length < cap s
      ∧ step (env s) (st s) (T s) = placeTop (stOf d (rdi s)) (T s) :=
  Iff.rfl

theorem atErr_mk :
    AtErr s ra ⟨⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩, z, f, d⟩ ↔
      Base s ra ⟨⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩, z, f, d⟩
      ∧ step (env s) (st s) (T s) = .error .assertion :=
  Iff.rfl
end
end Step
end Bbu

-- A jump to a label of the cfg: the stack, the invariant and the variant.
local macro "cfg_goto" : tactic => `(tactic| (
  apply Program.Intercept.intro_label
  · repeat ((fail_if_success (apply List.getElem?_cons_zero)); (apply List.getElem?_cons_succ_of))
    apply List.getElem?_cons_zero
  refine Or.inl ⟨?_, ?_, ?_⟩))

-- A hypothesis found by reducible defeq only: the `kvcgen64` contexts are large.
local macro "hyp% " t:term : term => `((by with_reducible assumption : $t))

-- The normal form of the `kvcgen64` goals: loads are `rd` of `wordAt`.
local macro "step_norm" : tactic => `(tactic| try simp only [Bbu.Step.rd_def, Bbu.Step.pushes_eq,
  Reg64s.get64_rax, Reg64s.get64_rbx, Reg64s.get64_rcx, Reg64s.get64_rdx, Reg64s.get64_rsi,
  Reg64s.get64_rdi, Reg64s.get64_rsp, Reg64s.get64_rbp, Reg64s.get64_r14,
  Reg64s.rax_mk, Reg64s.rbx_mk, Reg64s.rcx_mk, Reg64s.rdx_mk, Reg64s.rsi_mk, Reg64s.rdi_mk,
  Reg64s.rsp_mk, Reg64s.rbp_mk, Reg64s.r8_mk, Reg64s.r9_mk, Reg64s.r10_mk, Reg64s.r11_mk,
  Reg64s.r12_mk, Reg64s.r13_mk, Reg64s.r14_mk, Reg64s.r15_mk,
  MachineData.regs_mk, MachineData.dmem_mk, MachineData.status_mk, MachineData.zmms_mk,
  Bbu.Step.pushRa_rax, Bbu.Step.pushRa_rbx, Bbu.Step.pushRa_rcx, Bbu.Step.pushRa_rdx,
  Bbu.Step.pushRa_rsi, Bbu.Step.pushRa_rdi, Bbu.Step.pushRa_rbp, Bbu.Step.pushRa_r14,
  Bbu.Step.disp0, Bbu.Step.disp1, Bbu.Step.disp3, Bbu.Step.disp7, Bbu.Step.disp_dest,
  Bbu.Step.ofInt_one, Bbu.Step.ofInt_m1, Bbu.Step.ofInt_16,
  Bbu.Step.sf_test, Bbu.Step.ns_test, Bbu.Step.z_test, Bbu.Step.z_sub, Bbu.Step.nz_sub,
  CondCode.interp_nc, CondCode.interp_c, StatusFlags.cf_from_result,
  Bbu.Step.cf_sub, Bbu.Step.cf_sub', Bool.not_eq_true', Bool.not_eq_false', beq_iff_eq,
  Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false, beq_eq_false_iff_ne] at *)

namespace Bbu
open Step

/-! ## `.LB92` -/

section
variable {s : MachineData} {ra : Int64}

-- `setb; setb; testb; je`: the zero flag of the `and` of two borrows.
theorem j2_z_setb (a b c d : Word) (af : Bool) :
    CondCode.z.interp (StatusFlags.from_result
      (BitVec.ofNat 8 ((((a - b).toNat : Int) != (a.toNat : Int) - (b.toNat : Int))).toNat &&&
        BitVec.ofNat 8 ((((c - d).toNat : Int) != (c.toNat : Int) - (d.toNat : Int))).toNat)
      { cf := false, af := af, of := false })
      = !(decide (a.toNat < b.toNat) && decide (c.toNat < d.toNat)) := by
  have e1 : (((a - b).toNat : Int) != (a.toNat : Int) - (b.toNat : Int))
      = decide (a.toNat < b.toNat) := by rw [Bool.eq_iff_iff, cf_sub, decide_eq_true_iff]
  have e2 : (((c - d).toNat : Int) != (c.toNat : Int) - (d.toNat : Int))
      = decide (c.toNat < d.toNat) := by rw [Bool.eq_iff_iff, cf_sub, decide_eq_true_iff]
  rw [e1, e2]
  cases decide (a.toNat < b.toNat) <;> cases decide (c.toNat < d.toNat) <;> rfl

-- A callee keeps `r14`.
theorem j2_r14 {G L : Nat} {c t' : MachineData} (hag : (mod G c).Agree c t')
    (h : c.regs.r14.toBitVec.toNat = L) : t'.regs.r14.toBitVec.toNat = L := by
  have h' := hag.reg .r14 (by simp [mod])
  simp only [Reg64s.get64_r14] at h'
  rw [h']; exact h

theorem j2_add16 {t : MachineData} (hpre : Pre 152 stepA s) (hb : Base s ra t) :
    (t.regs.rbx.toBitVec + 16#64).toNat = T s + 16 := by
  rw [hb.rbx]; exact toNat_add (rsi_small hpre)

theorem j2_msb_encOpt {o : Option Nat} (h : ∀ p, o = some p → p ≤ 1024) :
    (encOpt o).msb = true ↔ o = none := by
  cases o with
  | none => exact ⟨fun _ => rfl, fun _ => by decide⟩
  | some p =>
    show (BitVec.ofNat 64 p).msb = true ↔ _
    rw [msb_small (h p rfl)]
    simp

-- `afterUrgent` falls to `bound` when the second test fails.
theorem j2_bound {e : Env} {st : St} {t u : Nat} (hu : u = t ∨ u = e.n)
    (h : u = e.n → t < st.len → st.len < e.n → positionOf st st.len = none →
      ¬ st.len < t + 16) :
    afterUrgent e st t u = bound e st t := by
  have h1 : ¬ (u ≠ e.n ∧ u ≠ t ∧ st.len < t + MAX_SWAP_DEPTH) := fun h' =>
    hu.elim h'.2.1 h'.1
  have h2 : ¬ (u = e.n ∧ t < st.len ∧ st.len < e.n ∧ positionOf st st.len = none ∧
      st.len < t + MAX_SWAP_DEPTH) := fun ⟨a, b, c, d, f⟩ => h a b c d f
  rw [afterUrgent, ite_eq_right_of_eq_false _ _ (eq_false h1),
    ite_eq_right_of_eq_false _ _ (eq_false h2)]

-- `afterUrgent` generates the slot for `st.len` when the second test holds.
theorem j2_gen {e : Env} {st : St} {t u : Nat} (hu : u = e.n) (h1 : t < st.len)
    (h2 : st.len < e.n) (h3 : positionOf st st.len = none) (h4 : st.len < t + 16) :
    afterUrgent e st t u = (generate e st st.len).map (·, .next t) := by
  have h0 : ¬ (u ≠ e.n ∧ u ≠ t ∧ st.len < t + MAX_SWAP_DEPTH) := fun h' => h'.1 hu
  have h5 : u = e.n ∧ t < st.len ∧ st.len < e.n ∧ positionOf st st.len = none ∧
      st.len < t + MAX_SWAP_DEPTH := ⟨hu, h1, h2, h3, h4⟩
  rw [afterUrgent, ite_eq_right_of_eq_false _ _ (eq_false h0),
    ite_eq_left_of_eq_true _ _ (eq_true h5)]

theorem j2_at93 {u : Nat} {t : MachineData} (hb : Base s ra t) (hst : st' s t = st s)
    (hpd : (st s).pending ≠ 0) (hu : u = T s ∨ u = (env s).n)
    (hs : step (env s) (st s) (T s) = afterUrgent (env s) (st s) (T s) u)
    (h : u = (env s).n → T s < (st s).len → (st s).len < (env s).n →
      positionOf (st s) (st s).len = none → ¬ (st s).len < T s + 16) : At93 s ra t :=
  ⟨hb, hst, hpd, hs.trans (j2_bound hu h)⟩

theorem j2_pos_post {c t t2 : MachineData} {L : Nat} (hp : Post positionOfF positionOfR c t2)
    (hc : c.dmem = t.dmem) (hdi : rdi c = rdi s) (hst : st' s t = st s) (hsi : (rsi c).toNat = L) :
    rax t2 = encOpt (positionOf (st s) L) ∧ st' s t2 = st s := by
  have h := positionOf_post hp hc hdi
  rw [hst, hsi] at h
  exact h

theorem j2_gen_post {c t' t2 : MachineData} {L : Nat} (hpre : Pre 152 stepA s)
    (hb : Base s ra t') (hp : Post generateF generateR c t2) (hc : c.dmem = t'.dmem)
    (hdi : rdi c = rdi s) (hst : st' s t' = st s) (hsi : (rsi c).toNat = L) :
    Res (rdi s) (generate (env s) (st s) L) (fun r => rax t2 = 0#64 ∧ st' s t2 = r) t2 := by
  have h := generate_post hpre hb hp hc hdi
  rw [hst, hsi] at h
  exact h
end

theorem step_body [Host] [FunDecls]
    (hurg : Spec "urgent" urgentF urgentA urgentR)
    (hgen : Spec "generate" generateF generateA generateR)
    (hpos : Spec "position_of" positionOfF positionOfA positionOfR)
    (htake : Spec "take_bound" takeBoundF takeBoundA takeBoundR)
    (hswap : Spec "swap_with" swapWithF swapWithA swapWithR) :
    Body stepAsm stepF stepA stepR := by
  intro s ra
  refine ⟨fun s₀ ⟨h₀, hpre⟩ => ?_⟩
  subst h₀
  replace hpre : Pre 152 stepA s := hpre
  refine Program.WP.cfg (fun
      | .entry, t | .label "step", t => t = s.pushRa ra
      | .label ".LB90", t => At90 s ra t
      | .label ".LB92", t => At92 s ra t
      | .label ".LB106", t => At106 s ra t
      | .label ".LB93", t => At93 s ra t
      | .label ".LB94", t => At94 s ra t
      | .label ".LB96", t => At96 s ra t
      | .label ".LB97", t => At97 s ra t
      | .label ".LB107", t => At107 s ra t
      | .label ".LB99", t => At99 s ra t
      | .label ".LB103", t | .label ".LB104", t => AtErr s ra t
      | .label ".LB89", t => At89 s ra t
      | _, _ => False)
    (fun l _ => V l) ?_ rfl
  cfg_cases
  case left t ht =>
    subst ht
    kvcgen64
  case right.left t ht =>
    subst ht
    have hmap0 : Mem.Mapped [frame 152 s] (s.pushRa ra).dmem := hpre.2.1.mapped.storeInt _ _ _
    have hle := hpre.2.1.le
    kvcgen64
    all_goals clear hurg hgen hpos htake hswap
    case vc1 | vc2 | vc3 =>
      refine Mem.Mapped.loadInt_isSome (bs := [frame 152 s]) ?_ (Or.inl ?_)
      · repeat (first | (with_reducible exact hmap0) | apply Mem.Mapped.storeInt)
      · simp only [Reg64s.get64_rsp, pushRa_rsp, rsp] at *
        bv_omega
    all_goals step_norm
    case vc4 => exact hdr_isSome (fm_pushes hpre).wf (by decide)
    case vc5 =>
      rename_i hlen
      cfg_goto
      · exact stack_of (by simp only [pushRa_rsp]; bv_omega)
      · refine ⟨base_pushes hpre rfl rfl rfl rfl rfl rfl rfl, st_pushes hpre, ?_⟩
        rw [← st_pushes hpre (ra := ra), st_len]
        simp only [T, rsi, rdi, Reg64s.get64_rsi, Reg64s.get64_rdi]
        omega
      · simp [V]
    case vc6 =>
      rename_i hlt
      have hw := (fm_pushes hpre (ra := ra)).wf
      have : _ ≤ 1024 := hw.len_le
      refine arr_isSome hw (by simp only [STACK, DEST_eq]; omega) ?_
      simp only [WORDS_eq, DEST_eq, rdi, Reg64s.get64_rdi] at *
      omega
    case vc7 =>
      rename_i hlt hd
      cfg_goto
      · exact stack_of (by simp only [pushRa_rsp]; bv_omega)
      · refine ⟨fm_pushes hpre, by simp only [pushRa_rsp]; bv_omega, rfl, rfl, rfl, rfl, ?_⟩
        show Res _ (step (env s) (st s) (T s)) _ _
        rw [← st_pushes hpre (ra := ra), step_done (t := T s) (st := stOf (pushes s ra) (rdi s))
          ⟨by rw [st_len]; exact hlt, (dest_iff hlt).2 hd⟩]
        refine ⟨?_, rfl⟩
        simp only [encNext, rax, T, rsi, Reg64s.get64_rax, Reg64s.get64_rsi]
        bv_omega
      · simp [V]
    case vc8 =>
      rename_i hlt hd
      refine ⟨base_pushes hpre rfl rfl rfl rfl rfl rfl rfl, st_pushes hpre, ?_⟩
      rw [← st_pushes hpre (ra := ra)]
      exact fun h => hd ((dest_iff hlt).1 h.2)
    case vc9 => simp [V]
  case right.right.left t ht =>
    have hb := ht.1
    have hle := hpre.2.1.le
    have hn := n_le hpre
    have htn : T s < (env s).n := hpre.2.2.1
    kvcgen64 [hurg]
    all_goals clear hgen hpos htake hswap
    all_goals step_norm
    all_goals obtain ⟨-, hst, hnd⟩ := ht
    all_goals try (
      have hp := hyp% (Post urgentF urgentR _ _)
      have hag := hyp% ((mod urgentF _).Agree _ _)
      have hb' := Base.call (by decide) hpre hb hp hag rfl rfl hb.rbp rfl rfl rfl rfl rfl
      have hu := urgent_post hpre hb hp rfl hb.rbp hb.rbx
      rw [hst] at hu
      have hpd : (st s).pending ≠ 0 := by
        have h := hyp% (rd t.dmem (wordAt t.regs.rbp.toBitVec 1) ≠ 0#64)
        rw [hb.rbp] at h
        rw [← hst, ← rd_pending]
        exact fun h' => h (BitVec.eq_of_toNat_eq h')
      have hstep := step_eq (e := env s) hnd hpd
      clear hp hag)
    case vc1 => rw [hb.rbp]; exact hdr_isSome hb.fm.wf (by decide)
    case vc2 =>
      rename_i hz
      cfg_goto
      · exact stack_of hb.rsp
      · refine ⟨⟨hb.fm, hb.rsp, hb.rbp, hb.rbx, hb.r12, hb.r13, hb.r15⟩, ?_⟩
        rw [hb.rbp] at hz
        rw [step_fin hnd (by rw [← hst, ← rd_pending, hz]; rfl)]
        exact congrArg (fun x => Except.ok (x, Next.finish)) hst.symm
      · simp [V]
    case vc3 => rw [hb.rsp]; exact Fm.call_isSome hpre hb.fm
    case vc4 => exact Fm.pre (by decide) hpre hb.fm rfl hb.rsp hb.rbp trivial
    case vc5 =>
      rename_i hm
      cfg_goto
      · exact stack_of hb'.rsp
      · exact at89_err ⟨hb'.fm, hb'.rsp, hb'.rbp, hb'.rbx, hb'.r12, hb'.r13, hb'.r15⟩ hu hm (fun u hr h => by rw [h.1]; exact msb_small (Nat.le_trans (urgent_le hr) hn))
          (fun e he => by rw [hstep, he]; rfl)
      · simp [V]
    case vc6 => rw [hb'.rbp]; exact hdr_isSome hb'.fm.wf (by decide)
    case vc7 =>
      rename_i hm heq
      obtain ⟨u, hr, hrax, hst'⟩ := res_ok_of_msb hu hm
      have hul := Nat.le_trans (urgent_le hr) hn
      cfg_goto
      · exact stack_of hb'.rsp
      · refine ⟨⟨hb'.fm, hb'.rsp, hb'.rbp, hb'.rbx, hb'.r12, hb'.r13, hb'.r15⟩, hst', hpd, u, hrax,
          ?_, Or.inl ?_, ?_⟩
        · show rd _ _ = _
          rw [hb'.rbp]; exact rd_n hpre hb'.fm
        · exact eq_toNat_of_ofNat hul (hrax.symm.trans (heq.symm.trans hb'.rbx))
        · rw [hstep, hr]; rfl
      · simp [V]
    case vc8 =>
      rename_i hm hne heq
      obtain ⟨u, hr, hrax, hst'⟩ := res_ok_of_msb hu hm
      have hul := Nat.le_trans (urgent_le hr) hn
      rw [hb'.rbp, rd_n hpre hb'.fm] at heq
      cfg_goto
      · exact stack_of hb'.rsp
      · refine ⟨⟨hb'.fm, hb'.rsp, hb'.rbp, hb'.rbx, hb'.r12, hb'.r13, hb'.r15⟩, hst', hpd, u, hrax,
          ?_, Or.inr ?_, ?_⟩
        · show rd _ _ = _
          rw [hb'.rbp]; exact rd_n hpre hb'.fm
        · have := eq_toNat_of_ofNat hul (hrax.symm.trans heq.symm)
          exact this.trans (toNat_small hn)
        · rw [hstep, hr]; rfl
      · simp [V]
    case vc9 => rw [hb'.rbp]; exact hdr_isSome hb'.fm.wf (by decide)
    case vc10 =>
      rename_i t' _ _ _ _ _ hm hne hne' hlt
      obtain ⟨u, hr, hrax, hst'⟩ := res_ok_of_msb hu hm
      have hul := Nat.le_trans (urgent_le hr) hn
      have hun : u ≠ (env s).n := fun h =>
        hne' (by rw [hb'.rbp, rd_n hpre hb'.fm, ← h]; exact hrax.symm)
      have hut : u ≠ T s := fun h => hne (by rw [hb'.rbx, ← ofNat_T, ← h]; exact hrax.symm)
      rw [hb'.rbp, hb'.rbx, len_of hst', toNat_add (rsi_small hpre)] at hlt
      have hrax' : (rax t').toNat = u := by rw [hrax]; exact toNat_small hul
      cfg_goto
      · exact stack_of hb'.rsp
      · refine ⟨⟨hb'.fm, hb'.rsp, hb'.rbp, hb'.rbx, hb'.r12, hb'.r13, hb'.r15⟩, hst', hpd, ?_⟩
        rw [hstep, hr]
        show afterUrgent (env s) (st s) (T s) u
          = (generate (env s) (st s) (rax t').toNat).map (·, Next.next (T s))
        rw [hrax', afterUrgent, if_pos ⟨hun, hut, hlt⟩]
      · simp [V]
    case vc11 =>
      rename_i t' _ _ _ _ _ hm hne hne' hlt
      obtain ⟨u, hr, hrax, hst'⟩ := res_ok_of_msb hu hm
      rw [hb'.rbp, hb'.rbx, len_of hst', toNat_add (rsi_small hpre)] at hlt
      refine ⟨⟨hb'.fm, hb'.rsp, hb'.rbp, hb'.rbx, hb'.r12, hb'.r13, hb'.r15⟩, hst', hpd, ?_⟩
      rw [hstep, hr]
      show afterUrgent (env s) (st s) (T s) u = _
      have hl : ¬ (st s).len < T s + MAX_SWAP_DEPTH := Nat.not_lt.2 hlt
      rw [afterUrgent, if_neg (fun h => hl h.2.2), if_neg (fun h => hl h.2.2.2.2)]
    case vc12 => simp [V]
  case right.right.right.right.right.right.left t ht =>
    obtain ⟨hfm, hsp, hbx, h12, h13, h15, hR⟩ := ht
    have hle := hpre.2.1.le
    obtain ⟨hp0, hp1, hp2⟩ := hfm.pops hsp
    kvcgen64
    all_goals clear hurg hgen hpos htake hswap
    case vc1 | vc2 | vc3 =>
      refine Mem.Mapped.loadInt_isSome hfm.map (Or.inl ?_)
      simp only [Reg64s.get64_rsp, rsp] at *
      bv_omega
    case vc4 =>
      refine Option.isSome_iff_exists.2 ⟨ra, retAddr_of hpre hfm ?_⟩
      show t.regs.rsp.toBitVec + 8#64 + 8#64 + 8#64 = _
      rw [hsp]; simp only [Bbu.rsp]; bv_omega
    case vc5 =>
      refine ret hpre hfm
        (by show t.regs.rsp.toBitVec + 8#64 + 8#64 + 8#64 = _; rw [hsp]; simp only [Bbu.rsp]; bv_omega) ?_ ?_
      · intro q hq
        simp only [rd] at hp0 hp1 hp2
        cases q <;> simp_all
      · intro t' hm hax
        exact stepR_congr hR hm hax
  case right.right.right.right.right.left t ht =>
    obtain ⟨hb, hs⟩ := ht
    kvcgen64
    all_goals clear hurg hgen hpos htake hswap
    case vc1 =>
      refine ⟨hb.fm, hb.rsp, hb.rbx, hb.r12, hb.r13, hb.r15, ?_⟩
      show Res _ (step _ _ _) _ _
      rw [hs]
      refine ⟨?_, rfl⟩
      have := rsi_small hpre
      simp only [encNext, rax, Reg64s.get64_rax, hb.rbx, show Int64.toInt 1 = 1 from rfl]
      simp only [rsi] at *
      bv_omega
    case vc2 => simp [V]
  case right.right.right.right.right.right.right.right.right.right.right.left t ht =>
    obtain ⟨hb, hs⟩ := ht
    kvcgen64
    all_goals clear hurg hgen hpos htake hswap
    cfg_goto
    · exact stack_of hb.rsp
    · refine ⟨hb.fm, hb.rsp, hb.rbx, hb.r12, hb.r13, hb.r15, ?_⟩
      show Res _ (step _ _ _) _ _
      rw [hs]
      exact ⟨rfl, rfl⟩
    · simp [V]
  case right.right.right.right.right.right.right.right.right.right.right.right.left t ht | right.right.right.right.right.right.right.right.right.right.right.right.right t ht =>
    obtain ⟨hb, hs⟩ := ht
    kvcgen64
    all_goals clear hurg hgen hpos htake hswap
    cfg_goto
    · exact stack_of hb.rsp
    · refine ⟨hb.fm, hb.rsp, hb.rbx, hb.r12, hb.r13, hb.r15, ?_⟩
      show Res _ (step _ _ _) _ _
      rw [hs]
      rfl
    · simp [V]
  case right.right.right.right.right.right.right.left t ht =>
    have hb := ht.1
    kvcgen64 [hgen]
    all_goals clear hurg hpos htake hswap hgen
    all_goals step_norm
    all_goals obtain ⟨-, hst, hpd, hs⟩ := ht
    case vc1 => rw [hb.rsp]; exact Fm.call_isSome hpre hb.fm
    case vc2 => exact Fm.pre (by decide) hpre hb.fm rfl hb.rsp hb.rbp (gen_pre hpre hb hst hpd rfl hb.rbp)
    case vc3 =>
      have hp := hyp% (Post generateF generateR _ _)
      have hag := hyp% ((mod generateF _).Agree _ _)
      have hb' := Base.call (by decide) hpre hb hp hag rfl rfl hb.rbp rfl rfl rfl rfl rfl
      have hg := generate_post hpre hb hp rfl hb.rbp
      rw [hst] at hg
      cfg_goto
      · exact stack_of hb'.rsp
      · exact at89_cmov hb' ⟨hb'.fm, hb'.rsp, hb'.rbp, hb'.rbx, hb'.r12, hb'.r13, hb'.r15⟩ hg hs rfl rfl
      · simp [V]
  case right.right.right.right.right.right.right.right.right.left t ht =>
    have hb := ht.1
    kvcgen64 [hgen]
    all_goals clear hurg hpos htake hswap hgen
    all_goals step_norm
    all_goals obtain ⟨-, hst, hpd, hs⟩ := ht
    all_goals try (
      have hp := hyp% (Post generateF generateR _ _)
      have hag := hyp% ((mod generateF _).Agree _ _)
      have hb' := Base.call (by decide) hpre hb hp hag rfl rfl hb.rbp rfl rfl rfl rfl rfl
      have hg := generate_post_T hpre hb hp rfl hb.rbp hb.rbx hst
      clear hp hag)
    case vc1 => rw [hb.rsp]; exact Fm.call_isSome hpre hb.fm
    case vc2 => exact Fm.pre (by decide) hpre hb.fm rfl hb.rsp hb.rbp (gen_pre hpre hb hst hpd rfl hb.rbp)
    case vc3 =>
      rename_i hm
      cfg_goto
      · exact stack_of hb'.rsp
      · exact at89_err ⟨hb'.fm, hb'.rsp, hb'.rbp, hb'.rbx, hb'.r12, hb'.r13, hb'.r15⟩ hg hm
          (fun r _ h => by rw [h.1]; rfl) (fun e he => by rw [hs, he]; rfl)
      · simp [V]
    case vc4 => rw [hb'.rbp]; exact hdr_isSome hb'.fm.wf (by decide)
    case vc5 =>
      rename_i t' _ _ _ _ hm hge
      obtain ⟨r, hr, hrax, hst'⟩ := res_ok_of_msb hg hm
      rw [hb'.rbp, hb'.rbx, rd_len] at hge
      have hlen : r.len ≤ T s := hst' ▸ hge
      cfg_goto
      · exact stack_of hb'.rsp
      · refine at89_of ⟨hb'.fm, hb'.rsp, hb'.rbp, hb'.rbx, hb'.r12, hb'.r13, hb'.r15⟩ ?_
        rw [hs, hr]
        show Res _ (afterGen (T s) r) _ _
        rw [afterGen, if_neg (fun h => absurd h.1 (by omega)), placeTop_len hlen]
        rfl
      · simp [V]
    case vc6 =>
      rename_i hlt
      rw [hb'.rbp]
      exact dest_isSome hb'.fm.wf (by rw [← hb'.rbp]; exact hlt)
    case vc7 =>
      rename_i t' _ _ _ _ hm hlt hd
      obtain ⟨r, hr, hrax, hst'⟩ := res_ok_of_msb hg hm
      rw [hb'.rbp, hb'.rbx] at hlt hd
      have hlt' : T s < r.len := Nat.lt_of_lt_of_eq hlt (rd_len.trans (congrArg St.len hst'))
      have hd' : r.dest (T s) ≠ T s := by rw [← hst']; exact fun h => hd ((dest_iff hlt).1 h)
      cfg_goto
      · exact stack_of hb'.rsp
      · refine ⟨⟨hb'.fm, hb'.rsp, hb'.rbp, hb'.rbx, hb'.r12, hb'.r13, hb'.r15⟩, ?_, ?_, ?_, ?_, ?_⟩
        · show T s < (st' s t').len
          rw [hst']; exact hlt'
        · show (st' s t').dest (T s) ≠ T s
          rw [hst']; exact hd'
        · show rd t'.dmem (wordAt t'.regs.rbp.toBitVec 0) = BitVec.ofNat 64 (st' s t').len
          rw [hb'.rbp]; exact rd_len'
        · show (st' s t').ops.length < cap s
          have h1 := (generate_shape hr).2.1
          have h2 := hpre.2.2.2.2
          rw [hst']; omega
        · show step (env s) (st s) (T s) = placeTop (st' s t') (T s)
          rw [hs, hr, hst']
          show afterGen (T s) r = _
          rw [afterGen, if_neg (fun h => hd' h.2)]
      · simp [V]
    case vc8 =>
      rename_i t' _ _ _ _ hm hlt hd
      obtain ⟨r, hr, hrax, hst'⟩ := res_ok_of_msb hg hm
      rw [hb'.rbp, hb'.rbx] at hlt hd
      have hlt' : T s < r.len := Nat.lt_of_lt_of_eq hlt (rd_len.trans (congrArg St.len hst'))
      have hd' : r.dest (T s) = T s := by rw [← hst']; exact (dest_iff hlt).2 hd
      cfg_goto
      · exact stack_of hb'.rsp
      · refine at89_of ⟨hb'.fm, hb'.rsp, hb'.rbp, hb'.rbx, hb'.r12, hb'.r13, hb'.r15⟩ ?_
        rw [hs, hr]
        show Res _ (afterGen (T s) r) _ _
        rw [afterGen, if_pos ⟨hlt', hd'⟩]
        refine ⟨?_, hst'⟩
        have := rsi_small hpre
        simp only [encNext, rax, Reg64s.get64_rax, hb'.rbx]
        simp only [rsi] at *
        bv_omega
      · simp [V]
  case right.right.right.right.right.right.right.right.right.right.left t ht =>
    have hb := ht.1
    kvcgen64
    all_goals clear hurg hpos htake hswap hgen
    all_goals step_norm
    all_goals obtain ⟨-, hdx, hlt, hs⟩ := ht
    all_goals have hw := hb.fm.wf
    case vc1 => rw [hb.rbp]; exact hdr_isSome hw (by decide)
    case vc2 => rw [hb.rbp, blkOf_def]; exact blk_isSome hw hw.mapped (by decide)
    case vc3 => rw [hb.rbp]; exact hdr_isSome' hw (hw.mapped.storeInt _ _ _) (by decide)
    case vc4 =>
      rw [hb.rbp, blkOf_def, blkOf_def, blkOf_store hw (by decide)]
      exact blk_isSome hw (hw.mapped.storeInt _ _ _) (by decide)
    case vc5 =>
      cfg_goto
      · exact stack_of hb.rsp
      · exact at107_out hpre hb hdx hlt hs rfl rfl rfl rfl rfl rfl rfl
      · simp [V]
  case right.right.right.right.left t ht =>
    have hb := ht.1
    kvcgen64 [hswap]
    all_goals clear hurg hpos htake hswap hgen
    all_goals step_norm
    all_goals obtain ⟨-, hlt, hd, hdx, hops, hs⟩ := ht
    all_goals have hL : (st' s t).len ≤ 1024 := (by have h := hb.fm.wf.len_le; rw [rd_len] at h; exact h)
    all_goals have hdx' : t.regs.rdx.toBitVec = BitVec.ofNat 64 (st' s t).len := hdx
    all_goals try (
      have hp := hyp% (Post swapWithF swapWithR _ _)
      have hag := hyp% ((mod swapWithF _).Agree _ _)
      have hb' := Base.callR (by decide) hpre hb hp hag
      have hw := swapWith_postR hb hp hb.rbx
      clear hp hag)
    case vc1 =>
      rename_i heq
      rw [hdx', hb.rbx, ← ofNat_T] at heq
      have h1 := last_of hL hlt heq
      cfg_goto
      · exact stack_mk hb.rsp
      · refine at97_mk.2 ⟨base_mk hb rfl rfl rfl rfl rfl rfl, ?_⟩
        rw [hs, placeTop_last hlt hd h1]
      · simp [V]
    case vc2 =>
      rename_i hne hja
      rw [a_sub16, decide_eq_true_eq, hdx', hb.rbx, ← ofNat_T, gap_of hL hlt] at hja
      cfg_goto
      · exact stack_mk hb.rsp
      · refine at107_mk.2 ⟨base_mk hb rfl rfl rfl rfl rfl rfl, ?_, (by show T s + 17 < (st' s t).len; omega), ?_⟩
        · show t.regs.rdx.toBitVec - t.regs.rbx.toBitVec = _
          rw [hdx', hb.rbx, ← ofNat_T, sub_of (Nat.le_of_lt hlt)]
        · rw [hs, placeTop_far hlt hd hja]
      · simp [V]
    case vc3 => rw [hb.rsp]; exact Fm.call_isSome hpre hb.fm
    case vc4 => exact Fm.preR (by decide) hpre hb (swap_preR hpre hb hops)
    case vc7 => simp [V]
    all_goals rename_i hne hja _ _ hm
    all_goals rw [hdx', hb.rbx, ← ofNat_T, ofNat_pred (by omega)] at hne
    all_goals rw [a_sub16, decide_eq_false_iff_not, hdx', hb.rbx, ← ofNat_T, gap_of hL hlt] at hja
    all_goals have hne' : T s ≠ (st' s t).len - 1 := fun h => hne (by rw [h])
    all_goals have hst := placeTop_swap hlt hd hne' (by omega)
    case vc5 =>
      cfg_goto
      · exact stack_mk' hb'.rsp
      · exact at89_mk' (at89_err hb' hw hm
          (fun r _ h => by rw [h.1]; rfl) (fun e he => by rw [hs, hst, he]; rfl))
      · simp [V]
    case vc6 =>
      obtain ⟨r, hr, -, hst'⟩ := res_ok_of_msb hw hm
      exact at97_mk'.2 ⟨base_mk' hb', by rw [hs, hst, hr, hst']; rfl⟩
  case right.right.right.left t ht =>
    have hb := ht.1
    kvcgen64 [hpos, htake]
    all_goals clear hurg hgen hpos htake hswap
    all_goals step_norm
    all_goals obtain ⟨-, hst, hpd, hs⟩ := ht
    all_goals have hL : (st s).len ≤ 1024 := (by
      rw [← hst]; have h := hb.fm.wf.len_le; rw [rd_len] at h; exact h)
    all_goals try (
      have hp := hyp% (Post positionOfF positionOfR _ _)
      have hag := hyp% ((mod positionOfF _).Agree _ _)
      have hb1 := Base.callR (by decide) hpre hb hp hag
      have hq := positionOf_postR hb hp hb.rbx
      clear hp hag)
    all_goals try rw [hst] at hq
    all_goals try (
      have hp := hyp% (Post takeBoundF takeBoundR _ _)
      have hag := hyp% ((mod takeBoundF _).Agree _ _)
      have hb2 := Base.callR (by decide) hpre hb1 hp hag
      have hw := takeBound_postR hb1 hp hb1.rbx
      clear hp hag)
    all_goals try rw [hq.2] at hw
    case vc1 => rw [hb.rsp]; exact Fm.call_isSome hpre hb.fm
    case vc2 => exact Fm.preR (by decide) hpre hb trivial
    case vc3 =>
      rename_i hm
      have hn := pos_none hL hq.1 hm
      cfg_goto
      · exact stack_mk' hb1.rsp
      · exact at94_mk'.2 ⟨base_mk' hb1, hq.2, hpd, by rw [hs, bound_none hn]⟩
      · simp [V]
    case vc4 => rw [hb1.rsp]; exact Fm.call_isSome hpre hb1.fm
    case vc5 =>
      rename_i hm
      have hps := pos_some hL hq.1 hm
      have hops := hpre.2.2.2.2
      exact Fm.preR (by decide) hpre hb1 (take_preR hpre hb1
        (by rw [hq.2]; exact positionOf_lt hps) (by rw [hq.2]; omega))
    case vc6 =>
      rename_i hm1 hm2
      have hps := pos_some hL hq.1 hm1
      cfg_goto
      · exact stack_mk' hb2.rsp
      · exact at89_mk' (at89_err hb2 hw hm2 (fun r _ h => by rw [h.1]; split <;> rfl)
          (fun e he => by rw [hs, bound_some hps, he]; rfl))
      · simp [V]
    case vc8 => rw [hb2.rbp]; exact hdr_isSome hb2.fm.wf (by decide)
    case vc10 =>
      rename_i hlt
      rw [hb2.rbp]
      exact dest_isSome hb2.fm.wf (by rw [← hb2.rbp]; exact hlt)
    case vc13 => simp [V]
    case vc7 =>
      rename_i hm1 hm2 hz
      have hps := pos_some hL hq.1 hm1
      obtain ⟨r, hr, hra, hst2⟩ := res_ok_of_msb hw hm2
      have h2 := take_true hra hz
      cfg_goto
      · exact stack_mk hb2.rsp
      · refine at89_mk.2 ⟨hb2.fm, hb2.rsp, hb2.rbx, hb2.r12, hb2.r13, hb2.r15, ?_⟩
        rw [hs, bound_some hps, hr]
        show Res _ (afterTake (T s) r) _ _
        rw [afterTake, if_pos h2]
        exact ⟨succ_T hb2.rbx, hst2⟩
      · simp [V]
    case vc9 =>
      rename_i hm1 hm2 hne hge
      have hps := pos_some hL hq.1 hm1
      obtain ⟨r, hr, hra, hst2⟩ := res_ok_of_msb hw hm2
      have h2 := take_false hra hne
      rw [hb2.rbp, hb2.rbx, rd_len] at hge
      have hlen : r.1.len ≤ T s := hst2 ▸ hge
      cfg_goto
      · exact stack_mk hb2.rsp
      · refine atErr_mk.2 ⟨base_mk hb2 rfl rfl rfl rfl rfl rfl, ?_⟩
        rw [hs, bound_some hps, hr]
        show afterTake (T s) r = _
        rw [afterTake, if_neg (by simp [h2]), placeTop_len hlen]
      · simp [V]
    case vc11 =>
      rename_i hm1 hm2 hne hlt hd
      have hps := pos_some hL hq.1 hm1
      obtain ⟨r, hr, hra, hst2⟩ := res_ok_of_msb hw hm2
      have h2 := take_false hra hne
      rw [hb2.rbp, hb2.rbx] at hlt hd
      have hd' : r.1.dest (T s) = T s := by rw [← hst2]; exact (dest_iff hlt).2 hd
      cfg_goto
      · exact stack_mk hb2.rsp
      · refine atErr_mk.2 ⟨base_mk hb2 rfl rfl rfl rfl rfl rfl, ?_⟩
        rw [hs, bound_some hps, hr]
        show afterTake (T s) r = _
        rw [afterTake, if_neg (by simp [h2]), placeTop_dest hd']
      · simp [V]
    case vc12 =>
      rename_i hm1 hm2 hne hlt hd
      have hps := pos_some hL hq.1 hm1
      obtain ⟨r, hr, hra, hst2⟩ := res_ok_of_msb hw hm2
      have h2 := take_false hra hne
      rw [hb2.rbp, hb2.rbx] at hlt hd
      have hlt' : T s < r.1.len := Nat.lt_of_lt_of_eq hlt (rd_len.trans (congrArg St.len hst2))
      have hd' : r.1.dest (T s) ≠ T s := by rw [← hst2]; exact fun h => hd ((dest_iff hlt).1 h)
      have hsh := takeBound_shape (positionOf_lt hps) hr
      have hops := hpre.2.2.2.2
      refine at96_mk2 (base_mk hb2 rfl rfl rfl rfl rfl rfl) hst2 hlt' hd' ?_ (by omega) ?_
      · show rd _ _ = _
        rw [hb2.rbp, rd_len']
        exact congrArg (fun q => BitVec.ofNat 64 q.len) hst2
      · rw [hs, bound_some hps, hr]
        show afterTake (T s) r = _
        rw [afterTake, if_neg (by simp [h2])]
  case right.right.right.right.right.right.right.right.left t ht =>
    have hb := ht.1
    obtain ⟨-, hst, hpd, u, hcx, hdx, hu, hs⟩ := ht
    have hn := n_le hpre
    have htn := T_lt hpre
    have hll : (st s).len < 1024 := by have := hpre.2.2.2.1; omega
    have hun' : u ≤ 1024 := by rcases hu with h | h <;> omega
    have hlen : (rd t.dmem (wordAt t.regs.rbp.toBitVec 0)).toNat = (st s).len := by
      rw [hb.rbp]; exact len_of hst
    have hbx : t.regs.rbx.toBitVec.toNat = T s := by rw [hb.rbx]
    have hdx' : t.regs.rdx.toBitVec.toNat = (env s).n :=
      (congrArg BitVec.toNat hdx).trans (toNat_small hn)
    kvcgen64 [hpos, hgen]
    all_goals clear hurg hpos htake hswap hgen
    all_goals step_norm
    all_goals try (
      have hz := hyp% (CondCode.z.interp _ = false)
      have heq := hyp% (t.regs.rdx.toBitVec = t.regs.rcx.toBitVec)
      rw [j2_z_setb, hbx, hlen, hdx'] at hz
      simp only [Bool.not_eq_false', Bool.and_eq_true, decide_eq_true_eq] at hz
      have hun : u = (env s).n :=
        (eq_toNat_of_ofNat hun' (hcx.symm.trans (heq.symm.trans hdx))).trans (toNat_small hn)
      have hp := hyp% (Post positionOfF positionOfR _ _)
      have hag := hyp% ((mod positionOfF _).Agree _ _)
      have hb' := Base.call (by decide) hpre hb hp hag rfl rfl hb.rbp rfl rfl rfl rfl rfl
      have hpo := j2_pos_post hp rfl hb.rbp hst hlen
      have hr14 := j2_r14 hag hlen
      have hadd := j2_add16 hpre hb'
      have key := j2_msb_encOpt (o := positionOf (st s) (st s).len)
        (fun _ h => Nat.le_of_lt (Nat.lt_trans (positionOf_lt h) hll))
      clear hp hag)
    case vc1 => rw [hb.rbp]; exact hdr_isSome hb.fm.wf (by decide)
    case vc2 =>
      rename_i hz
      rw [j2_z_setb, hbx, hlen, hdx'] at hz
      simp only [Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not] at hz
      cfg_goto
      · exact stack_mk hb.rsp
      · exact j2_at93 (base_mk hb rfl rfl rfl rfl rfl rfl) hst hpd hu hs
          (fun _ h1 h2 _ => (hz.elim (· h1) (· h2)).elim)
      · simp [V]
    case vc3 =>
      rename_i hne
      cfg_goto
      · exact stack_mk hb.rsp
      · exact j2_at93 (base_mk hb rfl rfl rfl rfl rfl rfl) hst hpd hu hs
          (fun h _ _ _ => absurd (hdx.trans (h ▸ hcx.symm)) hne)
      · simp [V]
    case vc4 => rw [hb.rsp]; exact Fm.call_isSome hpre hb.fm
    case vc5 => exact Fm.pre (by decide) hpre hb.fm rfl hb.rsp hb.rbp trivial
    case vc6 =>
      rename_i hm
      have hsome : positionOf (st s) (st s).len ≠ none := fun h =>
        Bool.false_ne_true (hm.symm.trans ((congrArg BitVec.msb hpo.1).trans (key.2 h)))
      cfg_goto
      · exact stack_mk' hb'.rsp
      · exact j2_at93 (base_mk' hb') hpo.2 hpd hu hs (fun _ _ _ h => absurd h hsome)
      · simp [V]
    case vc7 =>
      rename_i hm hc
      rw [hadd, hr14] at hc
      cfg_goto
      · exact stack_mk hb'.rsp
      · exact j2_at93 (base_mk hb' rfl rfl rfl rfl rfl rfl) hpo.2 hpd hu hs
          (fun _ _ _ _ => Nat.not_lt.2 hc)
      · simp [V]
    case vc8 => rw [hb'.rsp]; exact Fm.call_isSome hpre hb'.fm
    case vc9 =>
      exact Fm.pre (by decide) hpre hb'.fm rfl hb'.rsp hb'.rbp
        (gen_pre hpre hb' hpo.2 hpd rfl hb'.rbp)
    case vc10 =>
      rename_i hm hc _ _
      rw [hadd, hr14] at hc
      have hnone := key.1 ((congrArg BitVec.msb hpo.1).symm.trans hm)
      have hp := hyp% (Post generateF generateR _ _)
      have hag := hyp% ((mod generateF _).Agree _ _)
      have hb'' := Base.call (by decide) hpre hb' hp hag rfl rfl hb'.rbp rfl rfl rfl rfl rfl
      have hg := j2_gen_post hpre hb' hp rfl hb'.rbp hpo.2 hr14
      cfg_goto
      · exact stack_of hb''.rsp
      · exact at89_cmov hb''
          ⟨hb''.fm, hb''.rsp, hb''.rbp, hb''.rbx, hb''.r12, hb''.r13, hb''.r15⟩ hg (hs.trans (j2_gen hun hz.1 hz.2 hnone hc)) rfl rfl
      · simp [V]

end Bbu
