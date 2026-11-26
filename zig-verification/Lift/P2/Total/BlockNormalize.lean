module

public import Lift.P2.Total.BlockFinite
public import Lift.P2.Total.Memory

@[expose] public section

namespace Lift.P2.Total

/-- Rewrite a block edge without expanding the system inside later unrolls. -/
theorem block_step_nf {S O : Type} (m : System S O) (cut : S → Prop) (s t : S) :
    (blockSystem m cut).step s t ↔ m.step s t ∧ ¬ cut t := Iff.rfl

theorem block_stop_nf {S O : Type} (m : System S O) (cut : S → Prop) (s : S) (out : BlockExit S O) :
    (blockSystem m cut).stop s out ↔ match out with
      | .next t => m.step s t ∧ cut t
      | .finished out => m.stop s out := Iff.rfl

/-- Factor the edge shared by a cut exit and an interior block step. -/
theorem unroll_block_next {S O : Type} (m : System S O) (cut : S → Prop)
    (depth : Nat) (s next : S) :
    unroll (blockSystem m cut) (depth + 1) s (.finished (.next next)) ↔
    ∃ target, m.step s target ∧
      ((target = next ∧ cut target) ∨
        (¬ cut target ∧ unroll (blockSystem m cut) depth target (.finished (.next next)))) := by
  simp only [unroll, blockSystem]
  constructor
  · rintro (⟨out, stop, equality⟩ | ⟨target, ⟨edge, interior⟩, tail⟩)
    · cases equality
      exact ⟨next, stop.1, Or.inl ⟨rfl, stop.2⟩⟩
    · exact ⟨target, edge, Or.inr ⟨interior, tail⟩⟩
  · rintro ⟨target, edge, (⟨rfl, atCut⟩ | ⟨interior, tail⟩)⟩
    · exact Or.inl ⟨.next target, ⟨edge, atCut⟩, rfl⟩
    · exact Or.inr ⟨target, ⟨edge, interior⟩, tail⟩

/-- Expose one pending block step without expanding its later path. -/
theorem unroll_block_pending {S O : Type} (m : System S O) (cut : S → Prop)
    (depth : Nat) (s next : S) :
    unroll (blockSystem m cut) (depth + 1) s (.pending next) ↔
    ∃ target, m.step s target ∧ ¬ cut target ∧
      unroll (blockSystem m cut) depth target (.pending next) := by
  simp only [unroll, block_step_nf, reduceCtorEq, and_false, exists_false, false_or,
    and_assoc]

/-- A left shift is zero exactly when its surviving low bits are zero. -/
theorem shiftLeft_zero_iff_mask {width : Nat} (value : BitVec width) (shift : Nat) :
    (value <<< shift = 0#width) ↔
      value &&& (BitVec.allOnes width >>> shift) = 0#width := by
  constructor
  · intro shifted
    apply BitVec.eq_of_getLsbD_eq
    intro i inside
    by_cases live : shift + i < width
    · have bit := congrArg (fun word : BitVec width => word.getLsbD (shift + i)) shifted
      have high : ¬ shift + i < shift := by omega
      simpa only [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight,
        BitVec.getLsbD_allOnes, BitVec.getLsbD_zero, BitVec.getLsbD_shiftLeft,
        live, high, decide_true, decide_false, Bool.not_false, Bool.true_and,
        Bool.and_true, Nat.add_sub_cancel_left] using bit
    · simp only [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight,
        BitVec.getLsbD_allOnes, BitVec.getLsbD_zero, live, decide_false, Bool.and_false]
  · intro masked
    apply BitVec.eq_of_getLsbD_eq
    intro i inside
    by_cases low : i < shift
    · simp [BitVec.getLsbD_shiftLeft, low]
    · have live : shift + (i - shift) < width := by omega
      have bit := congrArg (fun word : BitVec width => word.getLsbD (i - shift)) masked
      simp only [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight,
        BitVec.getLsbD_allOnes, BitVec.getLsbD_zero, live, decide_true, Bool.and_true] at bit
      simpa only [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_zero, inside, low,
        decide_true, decide_false, Bool.not_false, Bool.true_and] using bit

/-- Substitute a successor state after two independent machine choices. -/
theorem exists_two_choice_state {A B C : Type} (state : B → C → A)
    (predicate : A → Prop) :
    (∃ value, (∃ first second, value = state first second) ∧ predicate value) ↔
      ∃ first second, predicate (state first second) := by
  constructor
  · rintro ⟨_, ⟨first, second, rfl⟩, h⟩
    exact ⟨first, second, h⟩
  · rintro ⟨first, second, h⟩
    exact ⟨state first second, ⟨first, second, rfl⟩, h⟩

/-- Compare a machine word with its exact bit-vector representation. -/
theorem int64_ofBitVec_eq_iff (value : BitVec 64) (other : Int64) :
    Int64.ofBitVec value = other ↔ value = other.toBitVec := by
  constructor
  · intro equality
    exact congrArg Int64.toBitVec equality
  · intro equality
    subst value
    exact Int64.ofBitVec_toBitVec other

/-- A successful RAM read supplies its exact word and read permission. -/
theorem readRam_ok_witness (policy : CpuPolicy) (memory : DataMem)
    (address : BitVec 64) (width : Width) (value : width.type)
    (read : readRam policy memory address width = .ok value) :
    ∃ word, Mem.loadInt memory address width.bytes = some word ∧
      policy.permits (.read address width) = true ∧
      value = BitVec.ofInt width.bits word := by
  cases allowed : policy.permits (.read address width) with
  | false => simp [readRam, allowed] at read
  | true =>
    cases mapped : Mem.loadInt memory address width.bytes with
    | none => simp [readRam, allowed, mapped] at read
    | some word =>
      have equality : BitVec.ofInt width.bits word = value := by
        simpa only [readRam, allowed, ↓reduceIte, mapped, Except.ok.injEq] using read
      exact ⟨word, rfl, rfl, equality.symm⟩

end Lift.P2.Total
