import Lean
import Std.Tactic.BVDecide

/-! # An axiom gate that accepts `bv_decide` certificates

In this toolchain each native run of `bv_decide` adds one fresh axiom (`Lean.Meta.nativeEqTrue`):

    axiom D._native.bv_decide.ax_I_J :
      Std.Tactic.BVDecide.Reflect.verifyBVExpr D._expr_def_K_L D._cert_def_K_L = true

where `_expr_def` is a `BVLogicalExpr` literal and `_cert_def` is an LRAT certificate as a `String`
literal. `checkAxioms env d` accepts `d` when each axiom in its dependency cone is

- `propext`, `Classical.choice` or `Quot.sound`, or
- an axiom of the form above whose claim is true: the gate parses the two literals into values
  and runs `verifyBVExpr` (the compiled code of `Std`, not code of `env`) on them.

The second rule depends on the truth of the claim, not on who made the axiom. The name rule
(`_native.bv_decide.ax_`, `_expr_def`, `_cert_def`) only refuses axioms that `bv_decide` did not
name. The parse is checked by a round trip: `toExpr` of the parsed value must be the literal. -/

open Lean Std.Tactic.BVDecide Lean.Meta.Tactic.BVDecide

namespace LeanTools

def kernelAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-! ## Literals to values

Each parser reads the form that `toExpr` writes. A parser can be loose: `ofLiteral` refuses each
value whose `toExpr` is not the literal. -/

def nat (e : Expr) : Except String Nat :=
  match e.nat? <|> e.rawNatLit? with
  | some n => .ok n
  | none => .error s!"not a natural number literal: {e}"

/-- The value among `xs` whose `toExpr` is `e`. -/
def oneOf {α : Type} [ToExpr α] (what : String) (xs : List α) (e : Expr) : Except String α :=
  match xs.find? (toExpr · == e) with
  | some x => .ok x
  | none => .error s!"not a {what} literal: {e}"

def unOp (e : Expr) : Except String BVUnOp :=
  match e.getAppFnArgs with
  | (``BVUnOp.rotateLeft, #[n]) => .rotateLeft <$> nat n
  | (``BVUnOp.rotateRight, #[n]) => .rotateRight <$> nat n
  | (``BVUnOp.arithShiftRightConst, #[n]) => .arithShiftRightConst <$> nat n
  | _ => oneOf "BVUnOp" [.not, .reverse, .clz, .cpop] e

partial def bvExpr (w : Nat) (e : Expr) : Except String (BVExpr w) := do
  match e.getAppFnArgs with
  | (``BVExpr.var, #[_, i]) => return .var (← nat i)
  | (``BVExpr.const, #[_, v]) =>
    match v.getAppFnArgs with
    | (``BitVec.ofNat, #[_, n]) => return .const (BitVec.ofNat w (← nat n))
    | _ => throw s!"not a BitVec literal: {v}"
  | (``BVExpr.bin, #[_, l, op, r]) =>
    return .bin (← bvExpr w l) (← oneOf "BVBinOp" [.and, .or, .xor, .add, .mul, .udiv, .umod] op)
      (← bvExpr w r)
  | (``BVExpr.un, #[_, op, x]) => return .un (← unOp op) (← bvExpr w x)
  | (``BVExpr.extract, #[w₀, start, len, x]) =>
    let len ← nat len
    if h : len = w then return h ▸ .extract (← nat start) len (← bvExpr (← nat w₀) x)
    else throw s!"extract: width {len} is not {w}"
  | (``BVExpr.append, #[l, r, _, a, b, _]) =>
    let l ← nat l
    let r ← nat r
    if h : w = l + r then return .append (← bvExpr l a) (← bvExpr r b) h
    else throw s!"append: width {w} is not {l} + {r}"
  | (``BVExpr.replicate, #[w₀, _, n, x, _]) =>
    let w₀ ← nat w₀
    let n ← nat n
    if h : w = w₀ * n then return .replicate n (← bvExpr w₀ x) h
    else throw s!"replicate: width {w} is not {w₀} * {n}"
  | (``BVExpr.shiftLeft, #[_, n, a, b]) => return .shiftLeft (← bvExpr w a) (← bvExpr (← nat n) b)
  | (``BVExpr.shiftRight, #[_, n, a, b]) => return .shiftRight (← bvExpr w a) (← bvExpr (← nat n) b)
  | (``BVExpr.arithShiftRight, #[_, n, a, b]) =>
    return .arithShiftRight (← bvExpr w a) (← bvExpr (← nat n) b)
  | _ => throw s!"not a BVExpr literal: {e}"

def bvPred (e : Expr) : Except String BVPred := do
  match e.getAppFnArgs with
  | (``BVPred.bin, #[w, l, op, r]) =>
    let w ← nat w
    return .bin (← bvExpr w l) (← oneOf "BVBinPred" [.eq, .ult] op) (← bvExpr w r)
  | (``BVPred.getLsbD, #[w, x, i]) => return .getLsbD (← bvExpr (← nat w) x) (← nat i)
  | _ => throw s!"not a BVPred literal: {e}"

partial def logical (e : Expr) : Except String BVLogicalExpr := do
  match e.getAppFnArgs with
  | (``BVLogicalExpr.literal, #[p]) => return .literal (← bvPred p)
  | (``BVLogicalExpr.const, #[b]) => return .const (← oneOf "Bool" [true, false] b)
  | (``BVLogicalExpr.not, #[x]) => return .not (← logical x)
  | (``BVLogicalExpr.gate, #[g, x, y]) =>
    return .gate (← oneOf "Gate" [.and, .xor, .beq, .or] g) (← logical x) (← logical y)
  | (``BVLogicalExpr.ite, #[c, x, y]) => return .ite (← logical c) (← logical x) (← logical y)
  | _ => throw s!"not a BVLogicalExpr literal: {e}"

/-- The value of a literal: parse, then demand that `toExpr` gives the literal back. -/
def ofLiteral {α : Type} [ToExpr α] (parse : Expr → Except String α) (e : Expr) : Except String α := do
  let x ← parse e
  unless toExpr x == e do throw s!"the literal is not in the form of `toExpr`: {e}"
  return x

/-! ## The `bv_decide` axiom -/

/-- A `bv_decide` claim, parsed: `verifyBVExpr expr cert = true`. -/
structure Claim where
  expr : BVLogicalExpr
  cert : String

/-- The last component of `n` starts with `s`. -/
def lastStartsWith (n : Name) (s : String) : Bool :=
  match n with
  | .str _ c => c.startsWith s
  | _ => false

/-- The value of a closed, safe definition of type `type`. -/
def defValue (env : Environment) (n : Name) (type : Name) : Except String Expr :=
  match env.find? n with
  | some (.defnInfo d) =>
    if !d.levelParams.isEmpty then .error s!"{n} has universe parameters"
    else if d.safety != .safe then .error s!"{n} is not safe"
    else if d.type != mkConst type then .error s!"{n} does not have type {type}"
    else .ok d.value
  | some _ => .error s!"{n} is not a definition"
  | none => .error s!"{n} is not in the environment"

/-- Parses the axiom `ax` as a `bv_decide` claim. -/
def parseClaim (env : Environment) (ax : Name) : Except String Claim := do
  let some (.axiomInfo a) := env.find? ax | throw s!"{ax} is not an axiom"
  unless lastStartsWith ax "ax_" && ax.getPrefix.getPrefix.components.getLast? == some `_native
      && ax.getPrefix.components.getLast? == some `bv_decide do
    throw s!"{ax} does not have the name of a bv_decide axiom"
  unless a.levelParams.isEmpty && !a.isUnsafe do
    throw s!"{ax} has universe parameters or is unsafe"
  let .app (.app (.const ``Std.Tactic.BVDecide.Reflect.verifyBVExpr []) (.const e [])) (.const c []) :=
      a.type.appFn!.appArg!
    | throw s!"{ax} is not a claim `verifyBVExpr <constant> <constant> = true`"
  let expected := mkApp3 (mkConst ``Eq [Level.one]) (mkConst ``Bool)
    (mkApp2 (mkConst ``Std.Tactic.BVDecide.Reflect.verifyBVExpr) (mkConst e) (mkConst c))
    (mkConst ``Bool.true)
  unless a.type == expected do
    throw s!"{ax} is not a claim `verifyBVExpr <constant> <constant> = true`"
  unless lastStartsWith e "_expr_def" && lastStartsWith c "_cert_def" do
    throw s!"{ax}: {e} and {c} do not have the names of bv_decide definitions"
  let expr ← ofLiteral logical (← defValue env e ``BVLogicalExpr)
  let .lit (.strVal cert) ← defValue env c ``String | throw s!"{c} is not a string literal"
  return { expr, cert }

/-- Accepts the axiom `ax` when it is a `bv_decide` claim and the compiled checker confirms it. -/
def checkClaim (env : Environment) (ax : Name) : Except String Unit := do
  let claim ← parseClaim env ax
  unless Std.Tactic.BVDecide.Reflect.verifyBVExpr claim.expr claim.cert do
    throw s!"{ax}: the LRAT certificate does not check: the claim is false"

/-- `ax` is a kernel axiom or a `bv_decide` claim that the compiled checker confirms. -/
def allowedAxiom (env : Environment) (ax : Name) : Bool :=
  kernelAxioms.contains ax || (checkClaim env ax).isOk

/-! ## The gate -/

private instance : MonadEnv (StateM Environment) where
  getEnv := get
  modifyEnv := modify

/-- The axioms of the dependency cone of `decl`. -/
def coneAxioms (env : Environment) (decl : Name) : Array Name :=
  (collectAxioms decl : StateM Environment _).run' env

/-- The axioms of `decl`, when each one is standard or a checked `bv_decide` claim. -/
def checkAxioms (env : Environment) (decl : Name) : Except String (Array Name) := do
  unless env.contains decl do throw s!"{decl}: unknown declaration"
  let axioms := coneAxioms env decl
  let problems := axioms.toList.filterMap fun ax =>
    if kernelAxioms.contains ax then none
    else match checkClaim env ax with
      | .ok () => none
      | .error reason => some s!"{decl} depends on {ax}: {reason}"
  unless problems.isEmpty do throw ("\n".intercalate problems)
  return axioms

/-- `#gate_axioms d` reports the axioms of `d`, or the reasons that the gate refuses it. -/
elab "#gate_axioms " id:ident : command => do
  let decl ← Elab.Command.liftCoreM (Elab.realizeGlobalConstNoOverloadWithInfo id)
  match checkAxioms (← getEnv) decl with
  | .ok axioms => logInfo m!"{decl}: accepted, axioms [{", ".intercalate (axioms.toList.map toString)}]"
  | .error reason => logError reason

end LeanTools
