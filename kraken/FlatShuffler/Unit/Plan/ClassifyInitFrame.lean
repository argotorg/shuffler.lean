module

public import FlatShuffler.Unit.Plan.Classify
import all FlatShuffler.Unit.Plan.Classify

@[expose] public section

namespace FlatShuffler.Unit.ClassifyU
open FlatShuffler.Sep

def pushRegs (s : MachineData) : List Word :=
  [s.regs.r15.toBitVec, s.regs.r14.toBitVec, s.regs.r13.toBitVec,
    s.regs.r12.toBitVec, s.regs.rbp.toBitVec, s.regs.rbx.toBitVec]

def pushed (s : MachineData) (ra : Int64) : Mem 64 :=
  pushes (s.pushRa ra).dmem (s.pushRa ra).regs.rsp.toBitVec (pushRegs s)

theorem init_frame {P : Addr} {c : CG} {F : MProp 64} {s : MachineData} {ra : Int64}
    {lo : List Word} {w q a b d e f g : Word} (hl : lo.length = 8)
    (hk : Kg (CView P c ∗ F) s ra (lo ++ [w, q, a, b, d, e, f, g]) (s.pushRa ra)) :
    PushOk (s.pushRa ra).dmem (s.pushRa ra).regs.rsp.toBitVec (pushRegs s) ∧
      (Stk (rsp s) (fr s lo w q) ra.toBitVec ∗ CView P c ∗ F).get (pushed s ra) := by
  have h := hk.pushes (xs := pushRegs s) (by simp [pushRegs, hl])
  have he : (lo ++ [w, q, a, b, d, e, f, g]).take
      ((lo ++ [w, q, a, b, d, e, f, g]).length - (pushRegs s).length) = lo ++ [w, q] := by
    simp [pushRegs, List.take_append, hl, List.take_of_length_le (by omega : lo.length ≤ 10)]
  rw [he] at h
  simpa only [pushed, pushRegs, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.append_nil, List.singleton_append, List.append_assoc, List.cons_append, fr, saved, MProp.sep_assoc] using h

theorem Wd.storeHi32 {a : Addr} {v : Word} {F : MProp 64} {m : Mem 64}
    (h : (Wd a v ∗ F).get m) (x : BitVec 32) :
    (Wd a (x ++ v.extractLsb' 0 32) ∗ F).get (m.storeInt (a + 4#64) 4 x.toInt) := by
  rw [Wd.split34] at h ⊢
  simp only [MProp.sep_assoc] at h ⊢
  have hs := B32.store h x.toInt
  have e1 : (x ++ v.extractLsb' 0 32).extractLsb' 32 32 = x := by bv_decide
  have e2 : (x ++ v.extractLsb' 0 32).extractLsb' 24 8 = v.extractLsb' 24 8 := by bv_decide
  have e3 : Int.toBytes 3 (x ++ v.extractLsb' 0 32).toInt = Int.toBytes 3 v.toInt := by
    rw [toBytes_sext 3, toBytes_sext 3 v]
    congr 2
    bv_decide
  simpa only [BitVec.ofInt_toInt, e1, e2, e3] using hs

theorem Stk.storeHi32 {P : MProp 64} {s : MachineData} {ra : Int64}
    {lo : List Word} {w q : Word} {m : Mem 64} {a : Addr}
    (h : (Stk (rsp s) (fr s lo w q) ra.toBitVec ∗ P).get m)
    (ha : a = rsp s - 8#64 - 56#64) (x : BitVec 32) :
    (Stk (rsp s) (fr s lo w (x ++ q.extractLsb' 0 32)) ra.toBitVec ∗ P).get
      (m.storeInt (a + 4#64) 4 x.toInt) := by
  obtain ⟨R, e⟩ := Stk.wd_focus (rsp s) (lo ++ [w]) (saved s) ra.toBitVec P
  change (Stk (rsp s) ((lo ++ [w]) ++ q :: saved s) ra.toBitVec ∗ P).get m at h
  rw [e] at h
  have hs := Wd.storeHi32 h x
  unfold fr
  rw [e]
  simpa only [ha, saved, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul] using hs

theorem Stk.store34 {P : MProp 64} {s : MachineData} {ra : Int64}
    {lo : List Word} {w q : Word} {m : Mem 64} {a : Addr}
    (h : (Stk (rsp s) (fr s lo w q) ra.toBitVec ∗ P).get m)
    (ha : a = rsp s - 8#64 - 56#64) (x : BitVec 32) (o : BitVec 8) :
    (Stk (rsp s) (fr s lo w (x ++ o ++ q.extractLsb' 0 24)) ra.toBitVec ∗ P).get
      ((m.storeInt (a + 4#64) 4 x.toInt).storeInt (a + 3#64) 1 o.toInt) := by
  obtain ⟨R, e⟩ := Stk.wd_focus (rsp s) (lo ++ [w]) (saved s) ra.toBitVec P
  change (Stk (rsp s) ((lo ++ [w]) ++ q :: saved s) ra.toBitVec ∗ P).get m at h
  rw [e] at h
  have hs := Wd.store34 h x o
  unfold fr
  rw [e]
  simpa only [ha, saved, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul] using hs

end FlatShuffler.Unit.ClassifyU
