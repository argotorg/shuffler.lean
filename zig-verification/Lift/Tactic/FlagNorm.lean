module

public import Lift.Tactic.LoopSimpAttr
public meta import Lean.Elab.Tactic

@[expose] public section

/-! The flag normal form of `loop_close` (task UP-OBJ3).

The code computes a condition as a flag byte: `setcc` gives `(if c then 1 else 0)`, `or`, `and` and `xor` combine the
bytes, `movzx` casts them, and `test` or `cmp` compares the result with a number. A hypothesis of a path is then such a
comparison, for example `¬((if 8 ≤ x then 1 else 0) ||| (if 8 ≤ y then 1 else 0)).toUInt8.toUInt64 = 1`, and `omega`
does not read it. The rules of `flag_norm`:

1. combine: `(if p then 1 else 0) ⊙ (if q then 1 else 0) = (if p ⊙' q then 1 else 0)`, for `|||` (`∨`), `&&&` (`∧`) and
   `^^^` (`(p ∧ ¬q) ∨ (¬p ∧ q)`), on `UInt8`, `UInt16`, `UInt32`, `UInt64`, `BitVec w` and `Nat`; so a term with any
   number of conditions becomes one `ite`;
2. casts: `toUInt8`, `toUInt64`, ..., `toNat`, `toBitVec` and `setWidth` of `(if p then 1 else 0)` are
   `(if p then 1 else 0)`;
3. compare: `(if p then 1 else 0) R c ↔ (p ∧ 1 R c) ∨ (¬p ∧ 0 R c)` for `=`, `≤` and `<`, on each side; the comparisons of
   numbers then reduce (`decide`);
4. the Boolean connectives go to the atoms (`¬¬`, `¬ (a ∨ b)`, `¬ (a ∧ b)`, `¬ a ≤ b`), and each order of `UInt` or
   `BitVec` becomes an order of `toNat`.

The result is a Boolean combination of linear facts of `toNat`; `loop_close` splits its conjunctions, and `omega` reads its
disjunctions. -/

namespace Lift.Tactic.FlagNorm

/-! ### 1. Combine -/

/-- The three rules of step 1 on the type `T`, with the names `n.or`, `n.and` and `n.xor`. -/
local macro "flag_combine " n:ident " : " T:term : command => do
  let orN := Lean.mkIdent (n.getId ++ `or)
  let andN := Lean.mkIdent (n.getId ++ `and)
  let xorN := Lean.mkIdent (n.getId ++ `xor)
  `(@[flag_norm] theorem $orN (p q : Prop) [Decidable p] [Decidable q] :
        ((if p then 1 else 0 : $T) ||| (if q then 1 else 0)) = if p ∨ q then 1 else 0 := by
      by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]
    @[flag_norm] theorem $andN (p q : Prop) [Decidable p] [Decidable q] :
        ((if p then 1 else 0 : $T) &&& (if q then 1 else 0)) = if p ∧ q then 1 else 0 := by
      by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]
    @[flag_norm] theorem $xorN (p q : Prop) [Decidable p] [Decidable q] :
        ((if p then 1 else 0 : $T) ^^^ (if q then 1 else 0)) = if (p ∧ ¬q) ∨ (¬p ∧ q) then 1 else 0 := by
      by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq])

flag_combine u8 : UInt8
flag_combine u16 : UInt16
flag_combine u32 : UInt32
flag_combine u64 : UInt64
flag_combine nat : Nat

@[flag_norm] theorem bv.or {w : Nat} (p q : Prop) [Decidable p] [Decidable q] :
    ((if p then 1 else 0 : BitVec w) ||| (if q then 1 else 0)) = if p ∨ q then 1 else 0 := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

@[flag_norm] theorem bv.and {w : Nat} (p q : Prop) [Decidable p] [Decidable q] :
    ((if p then 1 else 0 : BitVec w) &&& (if q then 1 else 0)) = if p ∧ q then 1 else 0 := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

@[flag_norm] theorem bv.xor {w : Nat} (p q : Prop) [Decidable p] [Decidable q] :
    ((if p then 1 else 0 : BitVec w) ^^^ (if q then 1 else 0)) = if (p ∧ ¬q) ∨ (¬p ∧ q) then 1 else 0 := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

/-! ### 2. Casts -/

/-- The rule of step 2 for the cast `f` from `S` to `T`, with the name `n`. -/
local macro "flag_cast " n:ident " : " f:ident " from " S:term:max " to " T:term:max : command =>
  `(@[flag_norm] theorem $n (p : Prop) [Decidable p] :
        $f (if p then (1 : $S) else 0) = (if p then (1 : $T) else 0) := by
      by_cases hp : p <;> simp [hp] <;> decide)

flag_cast u64_u8 : UInt64.toUInt8 from UInt64 to UInt8
flag_cast u64_u16 : UInt64.toUInt16 from UInt64 to UInt16
flag_cast u64_u32 : UInt64.toUInt32 from UInt64 to UInt32
flag_cast u32_u8 : UInt32.toUInt8 from UInt32 to UInt8
flag_cast u16_u8 : UInt16.toUInt8 from UInt16 to UInt8
flag_cast u8_u16 : UInt8.toUInt16 from UInt8 to UInt16
flag_cast u8_u32 : UInt8.toUInt32 from UInt8 to UInt32
flag_cast u8_u64 : UInt8.toUInt64 from UInt8 to UInt64
flag_cast u16_u32 : UInt16.toUInt32 from UInt16 to UInt32
flag_cast u16_u64 : UInt16.toUInt64 from UInt16 to UInt64
flag_cast u32_u64 : UInt32.toUInt64 from UInt32 to UInt64
flag_cast u8_nat : UInt8.toNat from UInt8 to Nat
flag_cast u16_nat : UInt16.toNat from UInt16 to Nat
flag_cast u32_nat : UInt32.toNat from UInt32 to Nat
flag_cast u64_nat : UInt64.toNat from UInt64 to Nat
flag_cast u8_bv : UInt8.toBitVec from UInt8 to (BitVec 8)
flag_cast u64_bv : UInt64.toBitVec from UInt64 to (BitVec 64)

@[flag_norm] theorem bv_nat {w : Nat} (p : Prop) [Decidable p] :
    (if p then (1 : BitVec (w + 1)) else 0).toNat = if p then 1 else 0 := by
  by_cases hp : p <;> simp [hp, Nat.one_mod_two_pow]

@[flag_norm] theorem bv_setWidth {w v : Nat} (p : Prop) [Decidable p] :
    (if p then (1 : BitVec (w + 1)) else 0).setWidth (v + 1) = if p then 1 else 0 := by
  by_cases hp : p <;> simp [hp] <;> apply BitVec.eq_of_toNat_eq <;> simp [Nat.one_mod_two_pow]

/-! ### 3. Compare -/

@[flag_norm] theorem ite_eq {α : Type} [OfNat α 0] [OfNat α 1] (p : Prop) [Decidable p] (c : α) :
    ((if p then 1 else 0 : α) = c) ↔ (p ∧ 1 = c) ∨ (¬p ∧ 0 = c) := by
  by_cases hp : p <;> simp [hp]

@[flag_norm] theorem eq_ite {α : Type} [OfNat α 0] [OfNat α 1] (p : Prop) [Decidable p] (c : α) :
    (c = (if p then 1 else 0 : α)) ↔ (p ∧ c = 1) ∨ (¬p ∧ c = 0) := by
  by_cases hp : p <;> simp [hp]

@[flag_norm] theorem ite_le {α : Type} [OfNat α 0] [OfNat α 1] [LE α] (p : Prop) [Decidable p] (c : α) :
    ((if p then 1 else 0 : α) ≤ c) ↔ (p ∧ 1 ≤ c) ∨ (¬p ∧ 0 ≤ c) := by
  by_cases hp : p <;> simp [hp]

@[flag_norm] theorem le_ite {α : Type} [OfNat α 0] [OfNat α 1] [LE α] (p : Prop) [Decidable p] (c : α) :
    (c ≤ (if p then 1 else 0 : α)) ↔ (p ∧ c ≤ 1) ∨ (¬p ∧ c ≤ 0) := by
  by_cases hp : p <;> simp [hp]

@[flag_norm] theorem ite_lt {α : Type} [OfNat α 0] [OfNat α 1] [LT α] (p : Prop) [Decidable p] (c : α) :
    ((if p then 1 else 0 : α) < c) ↔ (p ∧ 1 < c) ∨ (¬p ∧ 0 < c) := by
  by_cases hp : p <;> simp [hp]

@[flag_norm] theorem lt_ite {α : Type} [OfNat α 0] [OfNat α 1] [LT α] (p : Prop) [Decidable p] (c : α) :
    (c < (if p then 1 else 0 : α)) ↔ (p ∧ c < 1) ∨ (¬p ∧ c < 0) := by
  by_cases hp : p <;> simp [hp]

/-! ### 4. Connectives and atoms -/

/-- The number of a `BitVec` number in the form `OfNat.ofNat n` (the form of the flags). -/
@[flag_norm] theorem bv_toNat_ofNat (n w : Nat) : (OfNat.ofNat n : BitVec w).toNat = n % 2 ^ w := rfl

attribute [flag_norm] and_true true_and and_false false_and or_false false_or or_true true_or not_true_eq_false
  not_false_eq_true Classical.not_not not_or not_and Nat.not_le Nat.not_lt ne_eq eq_self_iff_true
  UInt8.le_iff_toNat_le UInt8.lt_iff_toNat_lt UInt16.le_iff_toNat_le UInt16.lt_iff_toNat_lt
  UInt32.le_iff_toNat_le UInt32.lt_iff_toNat_lt UInt64.le_iff_toNat_le UInt64.lt_iff_toNat_lt
  BitVec.le_def BitVec.lt_def BitVec.toNat_ofNat
  UInt8.toNat_ofNat UInt16.toNat_ofNat UInt32.toNat_ofNat UInt64.toNat_ofNat UInt64.toNat_ofBitVec UInt64.toNat_toBitVec
  UInt8.toNat_zero UInt16.toNat_zero UInt32.toNat_zero UInt64.toNat_zero UInt64.toNat_one
  BitVec.toNat_zero

end Lift.Tactic.FlagNorm

namespace Lift.Tactic

open Lean Meta

/-- Whether `e` is the number `n` in the form `OfNat.ofNat _ n _` (the form of the rules of step 1). -/
meta def isNum (n : Nat) (e : Expr) : Bool :=
  e.isAppOfArity ``OfNat.ofNat 3 && e.appFn!.appArg! == .lit (.natVal n)

/-- Whether `e` is a flag `(if c then 1 else 0)`. -/
meta def isFlagIte (e : Expr) : Bool :=
  e.isAppOfArity ``ite 5 && isNum 1 (e.getArg! 3) && isNum 0 (e.getArg! 4)

/-- Whether `e` is an order `≤` or `<` on a `UInt` or a `BitVec`. -/
meta def isFixedOrder (e : Expr) : Bool :=
  (e.isAppOfArity ``LE.le 4 || e.isAppOfArity ``LT.lt 4) &&
    (let t := e.getArg! 0
     [``UInt8, ``UInt16, ``UInt32, ``UInt64].any t.isConstOf || t.isAppOfArity ``BitVec 1)

/-- `simp only [flag_norm, Nat.reducePow, Nat.reduceMod]` (with `decide`) at each hypothesis that has a flag or an order of a
`UInt` or a `BitVec`. `none` if a hypothesis becomes `False`. The goal does not change. -/
meta def flagNormHyps (g : MVarId) : MetaM (Option MVarId) := g.withContext do
  let mut fvars := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let t ← instantiateMVars d.type
    if (t.find? fun e => isFlagIte e || isFixedOrder e).isSome && (← isProp t) then
      fvars := fvars.push d.fvarId
  if fvars.isEmpty then return some g
  let some ext ← getSimpExtension? `flag_norm | throwError "flag_norm: no simp set"
  let ctx ← Simp.mkContext (config := { decide := true }) (simpTheorems := #[← ext.getTheorems])
    (congrTheorems := ← getSimpCongrTheorems)
  -- Not the default simprocs: they turn the numbers of `BitVec` into `1#w` before the rules of step 1 apply.
  let mut procs : Simprocs := {}
  for n in [``Nat.reducePow, ``Nat.reduceMod] do
    procs ← procs.add n (post := true)
  let (r, _) ← simpGoal g ctx (simprocs := #[procs]) (fvarIdsToSimp := fvars) (simplifyTarget := false)
  return r.map (·.2)

end Lift.Tactic
