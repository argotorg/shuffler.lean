module

/-
The `@[vcgen_simp]` set folds the machine state while `vcgen` steps. A write to a named register or
to a part of one rebuilds the register file as a literal, and a read of a named register from a
literal is the field. The projections of the machine record, the `UInt64` round trip and
reassociation present adjacent literals to `evalGround`, so a chain of ground arithmetic and its
flags fold. A return address read from the slot that a push wrote is the pushed value.
`vcgen … with kfinish` discharges each verification condition with `cfg_exit` and `finish`.
-/
public import Kraken.X64.Registers
public import Std.Tactic.Do.Syntax
public meta import Lean.Elab.Tactic

public section

/-- Reassociation, so a chain of additions over a symbolic start presents
adjacent literals to `evalGround`. -/
@[vcgen_simp] theorem BitVec.add_assoc_rev {w : Nat} (a b c : BitVec w) : a + (b + c) = a + b + c :=
  (BitVec.add_assoc a b c).symm

@[vcgen_simp] theorem BitVec.add_ofNat_zero {w : Nat} (x : BitVec w) : x + (0 : BitVec w) = x :=
  BitVec.add_zero x

@[vcgen_simp] theorem BitVec.ofInt_toInt_int64_zero {w : Nat} :
    BitVec.ofInt w (Int64.toInt 0) = (0 : BitVec w) := by
  simp

attribute [vcgen_simp] UInt64.toBitVec_ofBitVec Int64.toBitVec_ofNat BitVec.ofNat_eq_ofNat
  BitVec.setWidth_eq BitVec.add_zero BitVec.toNat_ofNat Nat.zero_mod Int.add_zero Int.cast_ofNat_Int
  bne_self_eq_false BitVec.xor_self Bool.toNat_false Bool.toNat_true Option.map_some Option.get!_some Option.isSome_some
  BitVec.ofInt_toInt Int64.ofBitVec_toBitVec List.cons_append List.nil_append UInt64.toNat_ofBitVec
  Program.labels_nil Program.labels_cons_instr Program.labels_cons_label Program.labels_cons_byteArray
  List.cons_ne_nil

@[vcgen_rintro] theorem List.forall_mem_cons_intro {α : Type _} {G : α → Prop} {a : α} {l : List α}
    (ha : G a) (hl : ∀ x, x ∈ l → G x) : ∀ x, x ∈ a :: l → G x :=
  List.forall_mem_cons.mpr ⟨ha, hl⟩

@[vcgen_rintro] theorem List.forall_mem_nil_intro {α : Type _} {G : α → Prop} :
    ∀ x, x ∈ ([] : List α) → G x :=
  fun _ h => nomatch h

@[vcgen_simp] theorem MachineState.data_mk (d : MachineData) (pc : Int64) : (⟨d, pc⟩ : MachineState).data = d := rfl

syntax (name := cfgExit) "cfg_exit" : grind

macro_rules
  | `(grind| cfg_exit) => `(grind| skip)

syntax (name := kfinish) "kfinish" (ppSpace Lean.Parser.Tactic.configItem)*
    (ppSpace &"only")? (" [" withoutPosition(Lean.Parser.Tactic.grindParam,*) "]")? : grind

macro_rules
  | `(grind| kfinish $cfg* $[only%$o]? $[[$ps,*]]?) =>
    `(grind| (cfg_exit; finish $cfg* $[only%$o]? $[[$ps,*]]?))
