module

public import Lift.Sem.StackRoom
public import Lift.Sem.HeapLemmas
public import Lift.Sem.SimAt

@[expose] public section

/-! The pushes and pops of the L2 memory form (PIL-CALL3, U5b part H3).

A function with memory in its L2 state writes its pushes into that memory (`writeRam` of a word
below `sp`) and reads its pops from it (`readRam`). The L2⁺ model has no stack state. So the
relation of the two states needs: the room of the L2 memory (`RoomAt`: the permits and the mapped
words, as `StackRoom` of the entry state), and that no object of the L2⁺ heap meets the room. Then
a push keeps the bytes outside the room (so `Holds` and the frame clause stay), a heap store keeps
the bytes of the room (the stored bytes are owned, so they are not in the room), and a pop reads
the pushed word. -/

namespace Lift.Sem.SysV

open Lift.P2.Total

/-- The room of `n` bytes below `sp` in the memory `m`: for each word at `sp - k` with `8 ≤ k ≤ n`
and `8 ∣ k`, the policy permits the write and the read, and the word is mapped. `StackRoom` of a
state is `RoomAt` of its memory and `rsp`. -/
def RoomAt (policy : CpuPolicy) (m : DataMem) (sp : BitVec 64) (n : Nat) : Prop :=
  ∀ k, 8 ≤ k → k ≤ n → 8 ∣ k →
    policy.permits (.write (sp - BitVec.ofNat 64 k) .W64) = true ∧
    policy.permits (.read (sp - BitVec.ofNat 64 k) .W64) = true ∧
    Mem.loadInt m (sp - BitVec.ofNat 64 k) 8 ≠ none

theorem RoomAt.of_stackRoom {policy : CpuPolicy} {s : MachineState} {n : Nat}
    (h : StackRoom policy s n) : RoomAt policy s.data.dmem s.data.regs.rsp.toBitVec n := h

/-- The bytes of the word at `sp - k` are below `sp`. -/
theorem below_word {sp : BitVec 64} {n k i : Nat} (hk8 : 8 ≤ k) (hkn : k ≤ n) (_hn : n < 2 ^ 64)
    (hi : i < 8) : Below sp n (sp - BitVec.ofNat 64 k + BitVec.ofNat 64 i) := by
  unfold Below
  bv_omega

/-- A memory with the same bytes below `sp` has the same room. -/
theorem RoomAt.congr {policy : CpuPolicy} {m m' : DataMem} {sp : BitVec 64} {n : Nat}
    (h : RoomAt policy m sp n) (hn : n < 2 ^ 64) (e : ∀ b, Below sp n b → m'.get? b = m.get? b) :
    RoomAt policy m' sp n := by
  intro k hk8 hkn hd
  obtain ⟨h1, h2, h3⟩ := h k hk8 hkn hd
  refine ⟨h1, h2, ?_⟩
  rw [Mem.loadInt_congr fun i hi => e _ (below_word hk8 hkn hn hi)]
  exact h3

/-- A read of a word below `sp` gives the same value in a memory with the same bytes below `sp`. -/
theorem readRam_below {policy : CpuPolicy} {m m' : DataMem} {sp a v : BitVec 64} {n k : Nat}
    (hr : readRam policy m a .W64 = .ok v) (ha : a = sp - BitVec.ofNat 64 k) (hk8 : 8 ≤ k)
    (hkn : k ≤ n) (hn : n < 2 ^ 64) (e : ∀ b, Below sp n b → m'.get? b = m.get? b) :
    readRam policy m' a .W64 = .ok v := by
  subst ha
  exact readRam_of_loadInt (Mem.loadInt_congr fun i hi => e _ (below_word hk8 hkn hn hi)) hr

/-- A read at another text of the same address (PIL-CALL4: a pop at `sp - 24 + 8` of a word at `sp - 16`). -/
theorem readRam_at {policy : CpuPolicy} {m : DataMem} {a : BitVec 64} {w : Width} {r : RamResult w.type}
    (h : readRam policy m a w = r) (a' : BitVec 64) (e : a' = a) : readRam policy m a' w = r := e ▸ h

/-- A push to the word at `a = sp - k` of the room: the write succeeds, the new memory has the
room, the word reads as the pushed value, and each byte outside the room is the same. -/
theorem RoomAt.push {policy : CpuPolicy} {m : DataMem} {sp a : BitVec 64} {n k : Nat}
    (h : RoomAt policy m sp n) (hk8 : 8 ≤ k) (hkn : k ≤ n) (hd : 8 ∣ k) (hn : n < 2 ^ 64)
    (ha : a = sp - BitVec.ofNat 64 k) (v : BitVec 64) :
    ∃ m', writeRam policy m a .W64 v = .ok m' ∧ RoomAt policy m' sp n ∧
      readRam policy m' a .W64 = .ok v ∧ ∀ b, ¬ Below sp n b → m'.get? b = m.get? b := by
  subst ha
  obtain ⟨hw, hr, hm⟩ := h k hk8 hkn hd
  refine ⟨_, writeRam_of_mapped hw hm, ?_, readRam_storeInt hr, ?_⟩
  · intro j hj8 hjn hdj
    obtain ⟨g1, g2, g3⟩ := h j hj8 hjn hdj
    refine ⟨g1, g2, ?_⟩
    rcases Nat.lt_trichotomy j k with hjk | rfl | hjk
    · exact mapped_storeInt_of_disjoint (fun i hi i' hi' => by bv_omega) g3
    · exact mapped_storeInt _ _ _
    · exact mapped_storeInt_of_disjoint (fun i hi i' hi' => by bv_omega) g3
  · intro b hb
    exact Mem.get?_storeInt_of_ne _ _ _ _ _ fun i hi e => hb (by subst e; exact below_word hk8 hkn hn hi)

/-- A write that succeeds is the store of its bytes. -/
theorem writeRam_ok_eq {policy : CpuPolicy} {m m' : DataMem} {a v : BitVec 64}
    (hw : writeRam policy m a .W64 v = .ok m') : m' = Mem.storeInt m a 8 v.toInt := by
  unfold Lift.P2.Total.writeRam at hw
  split at hw
  · split at hw
    · cases hw; rfl
    · cases hw
  · cases hw

/-- A push to the word at `sp - j` keeps the read of another word at `sp - k` of the room. -/
theorem readRam_push_other {policy : CpuPolicy} {m m' : DataMem} {sp a b u v : BitVec 64} {j k n : Nat}
    (hr : readRam policy m b .W64 = .ok u) (hw : writeRam policy m a .W64 v = .ok m')
    (ha : a = sp - BitVec.ofNat 64 j) (hb : b = sp - BitVec.ofNat 64 k) (hj : j ≤ n) (hk : k ≤ n)
    (hn : n + 8 ≤ 2 ^ 64) (hdj : 8 ∣ j) (hdk : 8 ∣ k) (hjk : j ≠ k) :
    readRam policy m' b .W64 = .ok u := by
  subst ha hb
  rw [writeRam_ok_eq hw]
  exact readRam_storeInt_of_disjoint (fun i hi i' hi' => by bv_omega) hr

end Lift.Sem.SysV

namespace Lift.Sem

open Lift.P2.Total

/-- A store does not change the covered bytes. -/
theorem Heap.covered_store {h h' : Heap} {a : BitVec 64} {w : Width} {v : w.type}
    (hs : h.store a w v = .ok h') (b : BitVec 64) : Covered h' b ↔ Covered h b := by
  obtain ⟨rfl, -⟩ := Heap.store_ok hs
  constructor
  · rintro ⟨o', ho', hc⟩
    obtain ⟨o, ho, rfl⟩ := List.mem_map.mp ho'
    simp only [Obj.Covers, Obj.set_addr, Obj.set_size] at hc
    exact ⟨o, ho, hc⟩
  · rintro ⟨o, ho, hc⟩
    exact ⟨Obj.set a w v o, List.mem_map_of_mem ho, by simp only [Obj.Covers, Obj.set_addr, Obj.set_size]; exact hc⟩

/-- A heap store keeps each byte below `sp` that no object of the heap covers. -/
theorem Heap.store_below {h : Heap} {m m' : DataMem} {sp : BitVec 64} {n : Nat} (hfr : ∀ b, ¬ h.Owned b → m'.get? b = m.get? b)
    (hcov : ∀ b, SysV.Below sp n b → ¬ Covered h b) :
    ∀ b, SysV.Below sp n b → m'.get? b = m.get? b :=
  fun b hb => hfr b fun ho => hcov b hb (covered_of_owned ho)

/-- A push (a write outside every object) keeps `Holds`. -/
theorem Heap.Holds.push {policy : CpuPolicy} {h : Heap} {m m' : DataMem} {sp : BitVec 64} {n : Nat}
    (hh : h.Holds policy m) (hcov : ∀ b, SysV.Below sp n b → ¬ Covered h b)
    (hout : ∀ b, ¬ SysV.Below sp n b → m'.get? b = m.get? b) : h.Holds policy m' :=
  holds_congr hh fun b hc => hout b fun hb => hcov b hb hc

end Lift.Sem
