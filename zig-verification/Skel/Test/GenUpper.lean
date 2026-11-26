import Skel.Gen.Upper

/-! The tests of `Skel/Gen/Upper.lean` (suite `genupper`): `lake exe skel-test --only genupper`. Each check is a value that
must hold. A check that does not hold prints one `FAIL` line. The plans of `toySum`, `toyFind`, `toyWalk` and `toyFill` are
written by hand from section 2 of `docs/one-way-lift-g3-plan-20261118.md` and from the texts that the fixtures held (`Lift/Spike/Sum.lean`,
`Lift/Toys/Fixtures/{Find,Walk,Fill}L2p.lean`, removed in G3-19 except `FindL2p.lean`). The property draws `max 200 cases` random plans; the `i`-th plan comes
from the seed `seed + i`. A plan that breaks the property prints one `FAIL` line. The suite gives the number of failed
checks and plans. -/

namespace GenUpperTests

open Skel.Gen

/-- A name of a plan. The names here are valid, so the parse gives `some`; the default only fills the type. -/
def nm (s : String) : Ident := (Ident.parse s).getD ⟨"x", by decide⟩

/-! ## The plans of the fixtures, written by hand -/

/-- The parameter `p` of an address. -/
def pParam : Binder := ⟨nm "p", .addr⟩

/-- The parameter `ps` of a list of addresses. -/
def psParam : Binder := ⟨nm "ps", .addrs⟩

/-- `toyFill` (L). Section 2: `In2p` is `policy heap rsi rdi` (the result is a heap); `St` has `mem`, and `input rax mem`;
`rax` is a counter (`x.rax * 8` in `o7`, and the compare with `rsi` in `LBB7_1`, 5.2); the parameter is `p`. The head is
`LBB7_1` at `⟨a, 0, a.heap⟩` (`init` of `FillL2p.lean:69`); the cycle has two blocks (`LBB7_1`, `o7`), so the cycle is 2 and the fuel 20. The
statement has no ghost. -/
def toyFill : UpperPlan :=
  { fn := "toyFill", inputs := [.rsi, .rdi], mem := true, state := [(.rax, .counter)], kind := .heap,
    params := [pParam], heads := [⟨nm "LBB7_1", [(.rax, .lit 0)], 2, false⟩], ghosts := [] }

/-- `toySum` (S). Section 2: `In2p` is the heap and the registers in `Reg64` order, `rsi` then `rdi` (the fixture writes
`rdi rsi`, see the report); `St` is `input rax rcx` with no `mem`; `rax` is an accumulator and `rcx` a counter (5.2); the
result is a value; the parameter is `p`. The head is `LBB1_1` at `init a = ⟨a, 0, 0⟩`; fuel 20; no ghost. -/
def toySum : UpperPlan :=
  { fn := "toySum", inputs := [.rsi, .rdi], mem := false, state := [(.rax, .accumulator), (.rcx, .counter)],
    kind := .value, params := [pParam], heads := [⟨nm "LBB1_1", [(.rax, .lit 0), (.rcx, .lit 0)], 2, false⟩], ghosts := [] }

/-- `toyFind` (F). Section 2: `In2p` is `heap rdx rsi rdi`; the result is a value. `rax` and `rcx` are counters, since the
branch `x.rax = x.rcx` (`FindL2p.lean:70`) reads both (5.2, the branch rule). The head is `LBB2_1` at `⟨a, a.rsi, 0⟩`
(`FindRefute.lean:37`); the cycle has three blocks (`LBB2_1`, `o10`, `o16`), so fuel 26; no ghost (`xs` and `key` are
fields of the L3 input). -/
def toyFind : UpperPlan :=
  { fn := "toyFind", inputs := [.rdx, .rsi, .rdi], mem := false, state := [(.rax, .counter), (.rcx, .counter)],
    kind := .value, params := [pParam], heads := [⟨nm "LBB2_1", [(.rax, .input .rsi), (.rcx, .lit 0)], 3, false⟩],
    ghosts := [] }

/-- `toyWalk` (W). Section 2: `In2p` is `heap rdi`; the result is a value. `rdi` is a pointer (the base of the load at
`rdi + 8` in `o7`), `rax` an accumulator. The parameter is the list `ps`. The head is `LBB9_1` at `⟨a, 0, a.rdi⟩`
(`WalkL2p.lean:62`); fuel 20. One ghost: `rest_rdi`, the chain from `rdi` with offset 8 (4.7). -/
def toyWalk : UpperPlan :=
  { fn := "toyWalk", inputs := [.rdi], mem := false, state := [(.rax, .accumulator), (.rdi, .pointer)], kind := .value,
    params := [psParam], heads := [⟨nm "LBB9_1", [(.rax, .lit 0), (.rdi, .input .rdi)], 2, false⟩],
    ghosts := [⟨.rdi, 8⟩] }

/-- The `Repr` text of a value contains the text `sub`. -/
def hasText (s sub : String) : Bool := (s.splitOn sub).length > 1

/-- The next result kind of a cycle, used to build a plan that differs in its kind. -/
def nextKind : ResultKind → ResultKind
  | .value => .heap
  | .heap => .both
  | .both => .value

/-- The checks of the plans, each with its name. The first group reads the four plans; the second gives the cases of
the illegal and the legal values; the last reads the `Repr` text. -/
def checks : List (String × Bool) :=
  [ -- toyFill (L)
    ("toyFill: the name is toyFill", toyFill.fn == "toyFill"),
    ("toyFill: In2p has rsi and rdi in Reg64 order", toyFill.inputs == [.rsi, .rdi]),
    ("toyFill: St has mem", toyFill.mem == true),
    ("toyFill: the result is a heap, so In2p has a policy", toyFill.kind == .heap && toyFill.kind.hasPolicy),
    ("toyFill: the parameter is p, an address", toyFill.params == [pParam]),
    ("toyFill: the only head is LBB7_1", toyFill.heads.map (·.name.s) == ["LBB7_1"]),
    ("toyFill: the head state is rax := 0", toyFill.heads.map (·.state) == [[(.rax, .lit 0)]]),
    ("toyFill: the fuel of the head is 20", toyFill.heads.map (·.fuel) == [20]),
    ("toyFill: the cycle of the head has 2 blocks", toyFill.heads.map (·.cycle) == [2]),
    ("toyFill: rax is the only state register, a counter", toyFill.state == [(.rax, .counter)]),
    ("toyFill: there is no ghost", toyFill.ghosts.isEmpty),
    -- toySum (S)
    ("toySum: In2p has rsi and rdi in Reg64 order", toySum.inputs == [.rsi, .rdi]),
    ("toySum: St has no mem", toySum.mem == false),
    ("toySum: the result is a value, so In2p has no policy", toySum.kind == .value && !toySum.kind.hasPolicy),
    ("toySum: rax is an accumulator and rcx a counter", toySum.state == [(.rax, .accumulator), (.rcx, .counter)]),
    ("toySum: the only head is LBB1_1", toySum.heads.map (·.name.s) == ["LBB1_1"]),
    ("toySum: the head state is rax := 0 and rcx := 0", toySum.heads.map (·.state) == [[(.rax, .lit 0), (.rcx, .lit 0)]]),
    ("toySum: the fuel of the head is 20", toySum.heads.map (·.fuel) == [20]),
    ("toySum: the cycle of the head has 2 blocks", toySum.heads.map (·.cycle) == [2]),
    ("toySum: there is no ghost", toySum.ghosts.isEmpty),
    -- toyFind (F)
    ("toyFind: In2p has rdx, rsi and rdi in Reg64 order", toyFind.inputs == [.rdx, .rsi, .rdi]),
    ("toyFind: the result is a value", toyFind.kind == .value),
    ("toyFind: rax and rcx are counters", toyFind.state == [(.rax, .counter), (.rcx, .counter)]),
    ("toyFind: the only head is LBB2_1", toyFind.heads.map (·.name.s) == ["LBB2_1"]),
    ("toyFind: the head state is rax := rsi (input) and rcx := 0", toyFind.heads.map (·.state) == [[(.rax, .input .rsi), (.rcx, .lit 0)]]),
    ("toyFind: the fuel of the head is 26 (three blocks)", toyFind.heads.map (·.fuel) == [26]),
    ("toyFind: the cycle of the head has 3 blocks", toyFind.heads.map (·.cycle) == [3]),
    ("toyFind: there is no ghost", toyFind.ghosts.isEmpty),
    -- toyWalk (W)
    ("toyWalk: In2p has rdi", toyWalk.inputs == [.rdi]),
    ("toyWalk: the parameter is ps, a list of addresses", toyWalk.params == [psParam]),
    ("toyWalk: rdi is a pointer, rax an accumulator", toyWalk.state == [(.rax, .accumulator), (.rdi, .pointer)]),
    ("toyWalk: the only head is LBB9_1", toyWalk.heads.map (·.name.s) == ["LBB9_1"]),
    ("toyWalk: the head state is rax := 0 and rdi := rdi (input)", toyWalk.heads.map (·.state) == [[(.rax, .lit 0), (.rdi, .input .rdi)]]),
    ("toyWalk: the fuel of the head is 20", toyWalk.heads.map (·.fuel) == [20]),
    ("toyWalk: the cycle of the head has 2 blocks", toyWalk.heads.map (·.cycle) == [2]),
    ("toyWalk: one ghost, rest_rdi with offset 8", toyWalk.ghosts == [⟨.rdi, 8⟩]),
    -- values that differ in one field are not equal
    ("a plan with mem changed is not equal", toyFill != { toyFill with mem := false }),
    ("a plan with the result kind changed is not equal", toyFill != { toyFill with kind := .both }),
    ("a plan with the name changed is not equal", toyFill != { toyFill with fn := "toyFilL" }),
    ("a plan with the fuel changed is not equal", toyFill != { toyFill with heads := [⟨nm "LBB7_1", [(.rax, .lit 0)], 3, false⟩] }),
    ("a plan with a head state value changed is not equal", toyFill != { toyFill with heads := [⟨nm "LBB7_1", [(.rax, .lit 1)], 2, false⟩] }),
    ("a plan with a head generalized changed is not equal",
      toyFill != { toyFill with heads := toyFill.heads.map fun h => { h with generalized := true } }),
    ("a plan with a ghost added is not equal", toyWalk != { toyWalk with ghosts := [] }),
    ("a plan is equal to itself", toyFind == toyFind),
    ("two different fixtures are not equal", toySum != toyFind),
    -- boundary: legal values with empty lists
    ("a plan with no head and no ghost is legal", ({ toyFill with heads := [], ghosts := [] } : UpperPlan).heads.isEmpty),
    ("a plan with no head and no ghost is equal to itself",
      let p : UpperPlan := { toyFill with heads := [], ghosts := [] }
      p == p),
    ("a plan with no input and no state is legal", ({ toyFill with inputs := [], state := [] } : UpperPlan).state.isEmpty),
    ("a plan with no parameter is legal", ({ toyFill with params := [] } : UpperPlan).params.isEmpty),
    -- the result kind decides the policy of In2p (4.2, 4.4)
    ("a value result has no policy", !ResultKind.value.hasPolicy),
    ("a heap result has a policy", ResultKind.heap.hasPolicy),
    ("a result that is both has a policy", ResultKind.both.hasPolicy),
    -- the names are the only values that Ident.parse gives
    ("the keyword end is not a name of a plan", (Ident.parse "end").isNone),
    -- Repr
    ("the Repr text of toyFill has its name", hasText (reprStr toyFill) "fn := \"toyFill\""),
    ("the Repr text of toyFill has its memory flag", hasText (reprStr toyFill) "mem := true"),
    ("the Repr text of toyFill has its head", hasText (reprStr toyFill) "heads := [{ name := \"LBB7_1\""),
    ("the Repr text of toyFill has no ghost", hasText (reprStr toyFill) "ghosts := []"),
    ("the Repr texts of two plans differ", reprStr toyFill != reprStr toySum) ]

/-! ## The property -/

/-- The next state of the linear congruential generator of `GenTypes` (the constants of Numerical Recipes), modulo 2^32. -/
def lcg (x : Nat) : Nat := (1664525 * x + 1013904223) % 4294967296

/-- The `k`-th draw of the seed `s`: a number of 16 bits or more. -/
def draw (s k : Nat) : Nat := Nat.repeat lcg (k + 1) s / 65536

/-- The registers of the random plans. -/
def pool : List Reg64 := [.rax, .rcx, .rdx, .rsi, .rdi, .r8]

/-- The class of a state register, from a draw. -/
def classOf (n : Nat) : FieldClass :=
  match n % 3 with
  | 0 => .pointer
  | 1 => .counter
  | _ => .accumulator

/-- The result kind, from a draw. -/
def kindOf (n : Nat) : ResultKind :=
  match n % 3 with
  | 0 => .value
  | 1 => .heap
  | _ => .both

/-- The random plan of the seed `s`. Each list is a prefix of a fixed list, or a list of a fixed length, so each plan is a
legal value. -/
def sample (s : Nat) : UpperPlan :=
  let k := draw s 1 % 4
  { fn := ["toySum", "toyFind", "toyWalk", "toyFill"].getD (draw s 2 % 4) "toySum",
    inputs := pool.take (draw s 3 % 4),
    mem := draw s 4 % 2 == 0,
    state := ((pool.drop 2).take k).zip ((List.range k).map fun i => classOf (draw s (5 + i))),
    kind := kindOf (draw s 0),
    params := [pParam, psParam].take (draw s 9 % 3),
    heads := if draw s 10 % 2 == 0 then [] else [⟨nm "LBB9_1", [(.rdi, .input .rdi)], draw s 11 % 40, false⟩],
    ghosts := if draw s 12 % 2 == 0 then [] else [⟨.rdi, draw s 13 % 16⟩] }

/-- Changes one field of the plan, chosen by `m`. Each change appends an element to a list or changes a value, so the
result differs from the plan in that field only. -/
def mutate (m : Nat) (p : UpperPlan) : UpperPlan :=
  match m % 8 with
  | 0 => { p with fn := p.fn ++ "x" }
  | 1 => { p with inputs := p.inputs ++ [.r15] }
  | 2 => { p with mem := !p.mem }
  | 3 => { p with kind := nextKind p.kind }
  | 4 => { p with params := p.params ++ [⟨nm "zz", .addr⟩] }
  | 5 => { p with state := p.state ++ [(.r15, .pointer)] }
  | 6 => { p with heads := p.heads ++ [⟨nm "LBB9_9", [], 1, false⟩] }
  | _ => { p with ghosts := p.ghosts ++ [⟨.r15, 1⟩] }

/-- The plans of the property: the `i`-th from the seed `seed + i`. At least 200. -/
def samples (seed cases : Nat) : List UpperPlan :=
  (List.range (max 200 cases)).map fun i => sample (seed + i)

/-- Does the property hold for the seed `s`? `BEq` is reflexive on the plan, and a plan with one field changed is not
equal to it. -/
def holds (s : Nat) : Bool :=
  let p := sample s
  p == p && p != mutate (draw s 14) p

/-- The seeds of the property that break it. -/
def failures (seed cases : Nat) : List Nat :=
  (List.range (max 200 cases)).map (seed + ·) |>.filter fun s => !holds s

/-- Gives the number of failed checks and plans. The suite runs when `only` is none or `genupper`. -/
def run (seed cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "genupper" then return 0
  let mut failed := 0
  for (name, ok) in checks do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  genupper: {name}"
  let kinds := (samples seed cases).map (·.kind)
  unless [ResultKind.value, .heap, .both].all (kinds.contains ·) do
    failed := failed + 1
    IO.println "FAIL  genupper: the random plans do not have all three result kinds"
  let mutations := (List.range (max 200 cases)).map fun i => draw (seed + i) 14 % 8
  unless (List.range 8).all (mutations.contains ·) do
    failed := failed + 1
    IO.println "FAIL  genupper: the random plans do not use all eight field changes"
  for s in failures seed cases do
    failed := failed + 1
    IO.println s!"FAIL  genupper: the property fails for seed {s}"
  return failed

end GenUpperTests
