import Shuffler.Optimality.GenerationChoice.Cost
import Shuffler.Optimality.Replay.Cost
import Shuffler.Optimality.Schedule.Simulation
import Shuffler.Placement.Necessity

namespace Shuffler.Optimality.Schedule

open Shuffler.Placement

def BirthOp : Op → Prop
  | .dup _ | .push _ | .load _ => True
  | .swap _ | .pop => False

theorem birthOp_step (costs : PrimitiveCosts) (spills : SpillSet) (source : Stack)
    (op : Op) (result : ReplayResult spills source) (hb : BirthOp op)
    (hr : replayStep spills source op = some result) :
    ∃ value, result.target = source ++ [value] ∧
      ∃ offered ∈ generationOps spills source value, offered.cost costs = op.cost costs := by
  cases op with
  | swap _ | pop => exact False.elim hb
  | dup index =>
      simp only [replayStep] at hr
      split at hr
      next h =>
        cases hr
        let value := source[source.length - index]'(by omega)
        have hm : value ∈ source.reverse.take (MAX_DUP_DEPTH + 1) := by
          apply List.mem_take_iff_getElem.mpr
          refine ⟨index - 1, ?_, ?_⟩
          · simp only [List.length_reverse]
            omega
          · rw [List.getElem_reverse]
            dsimp [value]
            congr 1
            omega
        refine ⟨value, rfl, .dup ((source.reverse.take (MAX_DUP_DEPTH + 1)).idxOf value + 1), ?_, rfl⟩
        simp [generationOps, hm]
      next => simp at hr
  | push value =>
      simp only [replayStep] at hr
      split at hr
      next hf =>
        cases hr
        refine ⟨value, rfl, .push value, ?_, rfl⟩
        simp [generationOps, hf]
      next => simp at hr
  | load id =>
      simp only [replayStep] at hr
      split at hr
      next hs =>
        cases hr
        refine ⟨.Var id, rfl, .load id, ?_, rfl⟩
        simp [generationOps, hs]
      next => simp at hr

theorem simulate_cons (spills : SpillSet) (source : Stack) (op : Op) (ops : List Op) :
    simulate spills source (op :: ops) =
      (replayStep spills source op).bind (fun step => simulate spills step.target ops) := by
  rw [show op :: ops = [op] ++ ops from rfl, simulate_append, simulate_singleton]
  cases replayStep spills source op <;> rfl

theorem births_suffix (costs : PrimitiveCosts) (spills : SpillSet) (source target : Stack)
    (ops : List Op) (hb : ∀ op ∈ ops, BirthOp op)
    (hs : simulate spills source ops = some target) :
    ∃ values, target = source ++ values := by
  induction ops generalizing source with
  | nil =>
      have he : source = target := Option.some.inj hs
      exact ⟨[], by simpa using he.symm⟩
  | cons op ops ih =>
      rw [simulate_cons] at hs
      cases hr : replayStep spills source op with
      | none => simp [hr] at hs
      | some step =>
          simp only [hr, Option.bind_some] at hs
          obtain ⟨value, ht, _⟩ := birthOp_step costs spills source op step (hb op (by simp)) hr
          obtain ⟨values, he⟩ := ih step.target (fun op ho => hb op (by simp [ho])) hs
          exact ⟨value :: values, by simpa [ht, List.append_assoc] using he⟩

theorem reserve_after_birth (spills : SpillSet) (source target : Stack)
    (missing : Multiset Value) (value : Value) (ops : List Op)
    (hb : (target : Multiset Value) = (source : Multiset Value) + missing)
    (hs : simulate spills (source ++ [value]) ops = some target) :
    value ∈ missing ∧ Reserve spills (source ++ [value]) target (missing.erase value) := by
  cases hr : replay spills (source ++ [value]) ops with
  | none => simp [simulate, hr] at hs
  | some tail =>
      have ht : tail.target = target := by
        simpa only [simulate, hr, Option.map_some, Option.some.injEq] using hs
      have hm : missing = {value} + tail.added := by
        apply add_left_cancel (a := (source : Multiset Value))
        calc
          (source : Multiset Value) + missing = (target : Multiset Value) := hb.symm
          _ = (tail.target : Multiset Value) := by rw [ht]
          _ = (source : Multiset Value) + ({value} + tail.added) := by
            simpa only [tail.built.additions, ← Multiset.coe_add,
              Multiset.coe_singleton, Multiset.add_assoc] using
              tail.built.trace.noPop_balance tail.built.noPop
      have he : tail.added = missing.erase value := by simp [hm, Multiset.singleton_add]
      have checked := tail.built.cast rfl ht he
      refine ⟨by simp [hm], ?_⟩
      exact (show CanPlace spills (source ++ [value]) target (missing.erase value) from
        ⟨checked.trace, checked.noPop, checked.additions⟩).reserve

theorem flatten_births (trace : Trace spills source target) (hp : trace.noPop)
    (hz : trace.swapCount = 0) : ∀ op ∈ flatten trace, BirthOp op := by
  induction trace with
  | Lit => simp [flatten]
  | Swap _ _ _ _ _ => simp [Trace.swapCount] at hz
  | Pop _ _ => exact False.elim hp
  | Dup _ _ _ _ trace ih | Push _ _ trace ih | Load _ _ trace ih =>
      have hi := ih hp hz
      intro op ho
      simp only [flatten, List.mem_append, List.mem_singleton] at ho
      rcases ho with ho | rfl
      · exact hi op ho
      · trivial

end Shuffler.Optimality.Schedule
