module

/-
Userspace `grind` propagators that constant-fold ground `BitVec` arithmetic.

The builtin `BitVec` propagators deliberately skip `+`/`*`/`-`/comparisons,
leaving them to `cutsat`, which keeps them relational rather than folding a
ground application to a literal e-class node. In carry-chain proofs that starves
the downstream `toNat`/`!=` folds and forces exponential case splitting. These
propagators materialize a ground `BitVec` sum (and the `Nat` sum feeding the
carry comparison) as an e-class literal, so each carry collapses to `false`
before the next instruction.
-/
public import Lean.Meta.Tactic.Grind.Simp
public import Lean.Meta.Tactic.Grind.PropagatorAttr

public section

open Lean Lean.Meta Lean.Meta.Grind

namespace Kraken.GrindFold

private def mkBVLit (n : Nat) (v : BitVec n) : GoalM Expr := do
  shareCommon (← mkNumeral (mkApp (mkConst ``BitVec) (mkNatLit n)) v.toNat)

/--
Given `e = f a₁ a₂` with the last two arguments matched modulo equalities,
push `e = b` where `b` is computed by `eval` from the argument roots. Mirrors
the builtin `binOp` glue, using only public `grind` API.
-/
private def binOp (e : Expr) (eval : Expr → Expr → GoalM (Option Expr)) : GoalM Unit := do
  let a₂ := e.appArg!
  let a₁ := e.appFn!.appArg!
  let r₁ ← getRoot a₁
  let r₂ ← getRoot a₂
  let some b ← eval r₁ r₂ | return ()
  internalize b 0
  let eType ← inferType e
  let proof := mkApp9 (mkConst ``Grind.eval_congr₂ [1, 1, 1])
    (← inferType a₁) (← inferType a₂) eType e.appFn!.appFn! a₁ r₁ a₂ r₂ b
  let proof := mkApp3 proof (← mkEqProof a₁ r₁) (← mkEqProof a₂ r₂)
    (mkApp2 (mkConst ``Eq.refl [1]) eType b)
  pushEq e b proof

/-- Fold a ground `BitVec` `+` (both operand roots literal) to a `BitVec` literal. -/
def propagateBVAdd (e : Expr) : GoalM Unit := do
  unless e.isAppOfArity ``HAdd.hAdd 6 do return ()
  unless (← inferType e).isAppOf ``BitVec do return ()
  -- Idempotence: if `e` is already equated to a literal, there is nothing to fold.
  -- Upward propagators re-fire on every merge touching an argument class, so without
  -- this guard the same sum is re-internalized and re-pushed on each firing.
  if (← getBitVecValue? (← getRoot e)).isSome then return ()
  binOp e fun r₁ r₂ => do
    let some ⟨n₁, v₁⟩ ← getBitVecValue? r₁ | return none
    let some ⟨n₂, v₂⟩ ← getBitVecValue? r₂ | return none
    if h : n₁ = n₂ then
      some <$> mkBVLit n₁ (v₁ + h ▸ v₂)
    else
      return none

initialize registerBuiltinUpwardPropagator ``HAdd.hAdd propagateBVAdd

end Kraken.GrindFold
