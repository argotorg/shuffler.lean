module

public import Lift.Toys.L1
public import Lift.P2.Total.Machine

@[expose] public section

/-! A runner of the exact L1 of the toy unit under a policy, for the tests of the held-out toys.
`handle_sound` shows that each step of the runner is a step of `Handled`. -/

namespace Lift.Toys.Test.Run

open Lift.P2.Total Lift.Toys

/-- One step under `p`, with `false` for an undefined flag; `none` for a denied access or another
failure. -/
def handle (p : CpuPolicy) : Effects → Option MachineState
  | .done s => some s
  | .require_exec_access r k => if p.permits (.execute r.lower r.upper) then handle p (k ()) else none
  | .require_read_access a w k => if p.permits (.read a w) then handle p (k ()) else none
  | .require_write_access a w k => if p.permits (.write a w) then handle p (k ()) else none
  | @Effects.undefined _ .bool k => handle p (k false)
  | _ => none

/-- A result of `handle` is a result of `Handled`: the runner follows the semantics. -/
theorem handle_sound (p : CpuPolicy) (m : DataMem) (e : Effects) (t : MachineState)
    (h : handle p e = some t) : Handled p id m e (.next t) := by
  fun_induction handle p e with
  | case1 => cases h; exact .done _
  | case2 r k hp ih => exact .execAllow hp (ih h)
  | case3 => simp at h
  | case4 a w k hp ih => exact .readAllow hp (ih h)
  | case5 => simp at h
  | case6 a w k hp ih => exact .writeAllow hp (ih h)
  | case7 => simp at h
  | case8 k ih => exact .choice false (ih h)
  | case9 => simp at h <;> split at h <;> simp_all

/-- The sites of a table by PC (as a number); the first entry for a PC wins. -/
def index (t : List Lift.P1.Site) : Std.HashMap Nat (MachineData → Effects) :=
  t.foldr (fun (pc, code) m => m.insert pc.toBitVec.toNat code) {}

/-- The step of `dispatch t` from the index of `t`. `dispatch` scans the table, which takes about 0.4 us for
each entry in the interpreter: 1 ms for a step of the 2,401 sites of the shuffler. The index must be a
constant of the caller (`def idx := index t`), so that it is built once: a call of `stepWith (index t) s`
builds it for each state. -/
def stepWith (idx : Std.HashMap Nat (MachineData → Effects)) (s : MachineState) : Effects :=
  match idx[s.pc.toBitVec.toNat]? with
  | some code => code s.data
  | none => .done s

/-- The indexed step is the step of `dispatch`: for each state, the same effects. -/
theorem stepWith_index (t : List Lift.P1.Site) (s : MachineState) :
    stepWith (index t) s = Lift.P1.dispatch t s := by
  simp only [stepWith]
  induction t with
  | nil => simp [index, Lift.P1.dispatch]
  | cons e rest ih =>
    obtain ⟨pc, code⟩ := e
    simp only [index, List.foldr_cons, Std.HashMap.getElem?_insert, Lift.P1.dispatch] at ih ⊢
    by_cases h : pc.toBitVec.toNat = s.pc.toBitVec.toNat
    · have : s.pc = pc := by
        apply Int64.toBitVec_inj.mp
        apply BitVec.eq_of_toNat_eq; omega
      simp [h, this]
    · have : ¬ s.pc = pc := fun e => h (by rw [e])
      simp [h, this, ih]

/-- How a run ends. -/
inductive Stop
  | ret (s : MachineState)
  | fault (pc : Int64)
  | fuel

/-- At most `n` steps from `s`; stop at the PC `ra`. -/
def exec (p : CpuPolicy) (ra : Int64) : Nat → MachineState → Stop
  | 0, _ => .fuel
  | n + 1, s =>
    if s.pc == ra then .ret s
    else
      let pc := s.pc
      match handle p (L1.step s) with
      | some t => exec p ra n t
      | none => .fault pc

/-- `rax` and `rsp` at the return, or the PC of the fault, or the end of the fuel. -/
def outcome : Stop → String ⊕ (BitVec 64 × BitVec 64)
  | .ret s => .inr (s.data.regs.rax.toBitVec, s.data.regs.rsp.toBitVec)
  | .fault pc => .inl s!"fault at {pc.toBitVec.toHex}"
  | .fuel => .inl "fuel"

end Lift.Toys.Test.Run
