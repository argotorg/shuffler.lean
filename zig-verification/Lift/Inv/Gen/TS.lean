/-
The transition system of a loop and the cvc5 queries about it, as text.

This module imports no module of the loop planner. `TS` is the state of a loop: its state variables, its frame, its havoc variables, the paths of
the body and the entries. `TS.rankQuery` and `TS.counterQuery` build the SyGuS texts of the queries, and `eval` evaluates a formula of these
texts. `buildTS`, which reads the AST of a function, stays in `Lift.Inv.Gen.LoopSys`, and so does the meaning of the queries (see its doc).
-/
import Lift.Inv.Gen.SExp

namespace Lift.Inv.Gen.Loop

inductive VKind where
  | nat
  | bv (w : Nat)
  | ptr
  deriving BEq, Repr, Inhabited

structure Var where
  name : String
  kind : VKind
  deriving BEq, Repr, Inhabited

/-- One path of the body that ends at the back edge. -/
structure Path where
  pc : List String
  wg : List String
  /-- The new value of each PHI of the header (an SMT term). -/
  next : List (String × String)
  deriving Repr

structure TS where
  hdr : Nat
  state : List Var
  frame : List Var
  havoc : List Var
  paths : List Path
  /-- The entry: for each path from the function entry to the header, its conditions and the value of each PHI. -/
  entries : List (List String × List (String × String))
  /-- The word guards of the operations on numbers in the body: the guard number is looked up by the caller. -/
  numeric : List (Nat × Nat × String × Nat)   -- block, index, dst, width
  deriving Repr

def twoPow (w : Nat) : String := toString (2 ^ w)

def smtInt (n : Int) : String := if n < 0 then s!"(- {-n})" else toString n

def Var.dom (v : Var) (suffix : String := "") : String :=
  let n := v.name ++ suffix
  match v.kind with
  | .nat => s!"(>= {n} 0)"
  | .bv w => s!"(and (>= {n} 0) (< {n} {twoPow w}))"
  | .ptr => s!"(and (>= {n} 0) (< {n} {twoPow 64}))"

/-! ### The queries -/

def prime (v : Var) : String := v.name ++ "_p"

def TS.vars (t : TS) : List Var := t.state ++ t.frame ++ t.havoc

/-- The step relation: some path, its conditions (and its word guards, if `guards`) and the new state. -/
def TS.cont (t : TS) (guards : Bool) : String :=
  let path (p : Path) : String :=
    let conds := p.pc ++ (if guards then p.wg else []) ++ t.state.map fun v =>
      s!"(= {prime v} {(p.next.lookup v.name).getD v.name})"
    s!"(and {" ".intercalate (if conds.isEmpty then ["true"] else conds)})"
  match t.paths with
  | [] => "false"
  | ps => s!"(or {" ".intercalate (ps.map path)})"

def TS.init (t : TS) : String :=
  let one (pc : List String) (vals : List (String × String)) : String :=
    let conds := pc ++ vals.map fun (n, v) => s!"(= {n} {v})"
    s!"(and {" ".intercalate (if conds.isEmpty then ["true"] else conds)})"
  match t.entries with
  | [] => "false"
  | es => s!"(or {" ".intercalate (es.map fun (pc, vals) => one pc vals)})"

def TS.dom (t : TS) : String :=
  let ds := t.vars.map (·.dom) ++ t.state.map (·.dom "_p")
  s!"(and {" ".intercalate ds})"

def TS.decls (t : TS) : String :=
  "\n".intercalate ((t.vars ++ t.state.map fun (v : Var) => ({ name := prime v, kind := v.kind } : Var)).map fun v =>
    s!"(declare-var {v.name} Int)")

def TS.args (t : TS) : String :=
  " ".intercalate ((t.state ++ t.frame).map fun v => s!"({v.name} Int)")

def TS.call (t : TS) (fn : String) (suffix : String := "") : String :=
  s!"({fn} {" ".intercalate ((t.state.map fun v => v.name ++ suffix) ++ t.frame.map (·.name))})"

/-- The invariant and the ranking function. -/
def TS.rankQuery (t : TS) : String :=
  let d := t.dom
  let c := t.cont true
  "\n".intercalate [
    "(set-logic LIA)",
    s!"(synth-fun inv ({t.args}) Bool)",
    -- small terms: the variables, 0 and 1, sums and differences (the default grammar finds `n + 2^32` for `n`)
    s!"(synth-fun rho ({t.args}) Int ((I Int)) ((I Int ({" ".intercalate ((t.state ++ t.frame).map (·.name))} 0 1 (+ I I) (- I I)))))",
    t.decls,
    s!"(constraint (=> (and {d} {t.init}) {t.call "inv"}))",
    s!"(constraint (=> (and {d} {t.call "inv"} {c}) {t.call "inv" "_p"}))",
    s!"(constraint (=> (and {d} {t.call "inv"} {c}) (and (> {t.call "rho"} {t.call "rho" "_p"}) (>= {t.call "rho" "_p"} 0))))",
    "(check-synth)", ""]

/-- The bound `δ` of the increase of the counter `c` in a step. -/
def TS.counterQuery (t : TS) (c : String) : String :=
  let d := t.dom
  "\n".intercalate [
    "(set-logic LIA)",
    "(synth-fun delta () Int ((I Int)) ((I Int (0 1 2 3 4 5 6 7 8 9 10 16 32 64))))",
    t.decls,
    s!"(constraint (=> (and {d} {t.cont false}) (<= (- {c}_p {c}) delta)))",
    "(check-synth)", ""]

/-! ### An evaluator of the formulas of the queries (for the tests)

The fragment that the queries use: integers, `+ - * mod div`, comparisons, `and or not => ite`, `true`, `false`. -/

inductive Val where
  | int (n : Int)
  | bool (b : Bool)
  deriving Repr

partial def eval (env : List (String × Int)) : SExp → Option Val
  | .atom "true" => some (.bool true)
  | .atom "false" => some (.bool false)
  | .atom s => match s.toInt? with
    | some n => some (.int n)
    | none => (env.lookup s).map .int
  | .list (.atom op :: args) => do
    let vs ← args.mapM (eval env)
    let ints : Option (List Int) := vs.mapM fun | .int n => some n | _ => none
    let bools : Option (List Bool) := vs.mapM fun | .bool b => some b | _ => none
    match op, vs with
    | "+", _ => do return .int ((← ints).foldl (· + ·) 0)
    | "-", _ => do
      match ← ints with
      | [x] => return .int (-x)
      | x :: xs => return .int (xs.foldl (· - ·) x)
      | [] => none
    | "*", _ => do return .int ((← ints).foldl (· * ·) 1)
    | "mod", [.int x, .int y] => some (.int (x % y))
    | "div", [.int x, .int y] => some (.int (x / y))
    | "=", [.int x, .int y] => some (.bool (x == y))
    | "=", [.bool x, .bool y] => some (.bool (x == y))
    | "<", [.int x, .int y] => some (.bool (x < y))
    | "<=", [.int x, .int y] => some (.bool (x ≤ y))
    | ">", [.int x, .int y] => some (.bool (x > y))
    | ">=", [.int x, .int y] => some (.bool (x ≥ y))
    | "and", _ => do return .bool ((← bools).all id)
    | "or", _ => do return .bool ((← bools).any id)
    | "not", [.bool x] => some (.bool (!x))
    | "=>", [.bool x, .bool y] => some (.bool (!x || y))
    | "ite", [.bool c, x, y] => some (if c then x else y)
    | _, _ => none
  | _ => none

end Lift.Inv.Gen.Loop
