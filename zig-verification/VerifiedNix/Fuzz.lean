module

public import Kraken.StateCfg
public import Kraken.X64.Parser
public meta import Lean.Elab.Command
public meta import Lean.Elab.Tactic
import all Kraken.SeparationMem

/-!
# A fuzzer for invariants and specs

`#fuzz` runs a program on random start states and checks, at each visit of a label, the invariant
of a `vcgen` proof, on each edge between labels its variant, and at the exit a postcondition. A
check that fails shows a wrong invariant, variant or spec before any proof is tried; a check that
holds proves nothing.

    #fuzz sum8 args (c : MachineData) (ra : Int64) (n : Nat) with
      (gen := do
        let n ← Fuzz.nat 10
        let c ← Fuzz.stack (← Fuzz.machine)
        let c ← Fuzz.buffer c .rdi (← Fuzz.bytes (8 * n))
        return (Fuzz.setReg c .rsi n, Fuzz.ret, n))
      (start := c.push64 ra)
      (invariant := fun {s₀} l s' => match l with | "sum8" => s' = s₀ | … | _ => False)
      (variant := fun l s' => …)

(`FuzzTest.lean` has the whole example.)

`args` are the theorem's variables; `gen` gives values for them (a `Fuzz.Gen` of the tuple of the
variables that are not hypotheses); `start` is the state at the program's first instruction.
Optional clauses, in this order: `gen`; `pre` (a proposition that each sample must satisfy; the
others are skipped), `post` after `variant` (the exit condition `fun a t => …` of the triple; a
run that falls through the end of the program is not checked), then `runs`, `seed`, `fuel`. The
invariant and the variant have the types that `vcgen` takes. Each proposition must be decidable:
comparisons, `Mem.Contains`, `Mem.Mapped`, `Mem.Blocks.Disjoint`, `Mem.WritesOnly` (decided
below). A label visit inside a call is not checked, as `vcgen` takes a callee by its spec.

Hypothesis binders (`(h : P)`) are not values: `pre` is the conjunction of them and of the `pre`
clause. Without `gen`, the generator comes from the binders' types and the hypotheses (section
"The generator from the hypotheses"). A hypothesis that is not decidable, or a binder without a
generator, gives "not run" and the reason.

The same test runs inside `vcgen` (section "Inside `vcgen`"): at a `vcgen … invariants · I · V` of
a program with a back edge that leaves VCs open, from the goal and its hypotheses.
-/

@[expose] public section

open Std

namespace Fuzz

/-! ## Decision procedures for the memory predicates -/

/-- A filtered map is empty when no entry passes the filter. -/
theorem isEmpty_filter_iff {w : Nat} (m : Mem w) (f : BitVec w → UInt8 → Bool) :
    (m.filter f).isEmpty = true ↔ ∀ k v, m[k]? = some v → f k v = false := by
  rw [ExtHashMap.isEmpty_iff]
  constructor
  · intro h k v hk
    have := congrArg (·[k]?) h
    simp only [ExtHashMap.getElem?_filter', hk, ExtHashMap.getElem?_empty] at this
    simpa [Option.filter] using this
  · intro h
    ext k : 1
    simp only [ExtHashMap.getElem?_filter', ExtHashMap.getElem?_empty]
    cases hk : m[k]? with
    | none => rfl
    | some v => simp [Option.filter, h k v hk]

/-- The bytes of the blocks: each address inside a block `(a, len)` is `a + i` for an `i < len`. -/
theorem forall_inside_iff {w : Nat} (bs : List (BitVec w × Nat)) (P : BitVec w → Prop) :
    (∀ b, Mem.Blocks.Inside b 1 bs → P b) ↔ ∀ p ∈ bs, ∀ i < p.2, P (p.1 + BitVec.ofNat w i) := by
  induction bs with
  | nil => simp [Mem.Blocks.Inside]
  | cons p bs ih =>
    simp only [Mem.Blocks.Inside, List.mem_cons, forall_eq_or_imp, ← ih]
    constructor
    · intro h
      refine ⟨fun i hi => h _ (Or.inl ?_), fun b hb => h b (Or.inr hb)⟩
      rw [show p.1 + BitVec.ofNat w i - p.1 = BitVec.ofNat w i by
        rw [BitVec.add_comm, BitVec.add_sub_cancel], BitVec.toNat_ofNat]
      have := Nat.mod_le i (2 ^ w)
      omega
    · rintro ⟨h1, h2⟩ b (hb | hb)
      · have := h1 (b - p.1).toNat (by omega)
        rwa [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel] at this
      · exact h2 b hb

/-! The memory predicates of Kraken have no exposed bodies; these theorems unfold them (with
`import all Kraken.SeparationMem`), for the instances below. -/

theorem mapped_iff {w : Nat} (bs : List (BitVec w × Nat)) (m : Mem w) :
    Mem.Mapped bs m ↔ ∀ p ∈ bs, ∀ i < p.2, (m.get? (p.1 + BitVec.ofNat w i)).isSome = true :=
  forall_inside_iff bs fun b => (m.get? b).isSome = true

theorem disjoint_iff {w : Nat} (bs bs' : List (BitVec w × Nat)) :
    Mem.Blocks.Disjoint bs bs' ↔ ∀ p ∈ bs, ∀ i < p.2, ¬ Mem.Blocks.Inside (p.1 + BitVec.ofNat w i) 1 bs' :=
  forall_inside_iff bs fun b => ¬ Mem.Blocks.Inside b 1 bs'

theorem contains_iff {w : Nat} (m : Mem w) (a : BitVec w) (bs : List UInt8) :
    Mem.Contains m a bs ↔ m.loadBytes a bs.length = some bs := Iff.rfl

theorem writesOnly_iff {w : Nat} (bs : List (BitVec w × Nat)) (m m' : Mem w) :
    Mem.WritesOnly bs m m' ↔ Mem.UnchangedOutside bs m m' ∧ Mem.DomainGrows m m' := Iff.rfl

instance {w : Nat} (bs : List (BitVec w × Nat)) (m : Mem w) : Decidable (Mem.Mapped bs m) :=
  decidable_of_iff' _ (mapped_iff bs m)

instance {w : Nat} (bs bs' : List (BitVec w × Nat)) : Decidable (Mem.Blocks.Disjoint bs bs') :=
  decidable_of_iff' _ (disjoint_iff bs bs')

instance {w : Nat} (m : Mem w) (a : BitVec w) (bs : List UInt8) : Decidable (Mem.Contains m a bs) :=
  decidable_of_iff' _ (contains_iff m a bs)

/-- The entries of `m'` outside the blocks are those of `m`. -/
theorem unchangedOutside_iff {w : Nat} (bs : List (BitVec w × Nat)) (m m' : Mem w) :
    Mem.UnchangedOutside bs m m' ↔
      (m'.filter fun k v => decide (¬ Mem.Blocks.Inside k 1 bs) && m[k]? != some v).isEmpty = true
      ∧ (m.filter fun k v => decide (¬ Mem.Blocks.Inside k 1 bs) && m'[k]? != some v).isEmpty = true := by
  simp only [isEmpty_filter_iff, Mem.UnchangedOutside, ExtHashMap.get?_eq_getElem?, Bool.and_eq_false_iff,
    decide_eq_false_iff_not, Classical.not_not, bne_eq_false_iff_eq]
  constructor
  · intro h
    exact ⟨fun k v hk => (Classical.em (Mem.Blocks.Inside k 1 bs)).imp id fun hi => by rw [← h k hi, hk],
      fun k v hk => (Classical.em (Mem.Blocks.Inside k 1 bs)).imp id fun hi => by rw [h k hi, hk]⟩
  · rintro ⟨h1, h2⟩ b hb
    cases h : m'[b]? with
    | some v => exact ((h1 b v h).resolve_left hb).symm
    | none =>
      cases h' : m[b]? with
      | none => rfl
      | some v => have := (h2 b v h').resolve_left hb; rw [h] at this; cases this

instance {w : Nat} (bs : List (BitVec w × Nat)) (m m' : Mem w) : Decidable (Mem.UnchangedOutside bs m m') :=
  decidable_of_iff _ (unchangedOutside_iff bs m m').symm

theorem domainGrows_iff {w : Nat} (m m' : Mem w) :
    Mem.DomainGrows m m' ↔ (m.filter fun k _ => m'[k]?.isNone).isEmpty = true := by
  simp only [isEmpty_filter_iff, Mem.DomainGrows, ExtHashMap.get?_eq_getElem?, Option.isNone_eq_false_iff]
  constructor
  · intro h k v hk; exact h k (by simp [hk])
  · intro h b hb
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hb
    exact h b v hv

instance {w : Nat} (m m' : Mem w) : Decidable (Mem.DomainGrows m m') :=
  decidable_of_iff _ (domainGrows_iff m m').symm

instance {w : Nat} (bs : List (BitVec w × Nat)) (m m' : Mem w) : Decidable (Mem.WritesOnly bs m m') :=
  decidable_of_iff' _ (writesOnly_iff bs m m')

/-! ## Generators -/

/-- A random generator. -/
abbrev Gen := StateM StdGen

/-- A number below `n` (0 for `n = 0`). -/
def nat (n : Nat) : Gen Nat := modifyGet fun g => randNat g 0 (n - 1)

/-- A number in `[lo, hi]`. -/
def range (lo hi : Nat) : Gen Nat := modifyGet fun g => randNat g lo hi

def u64 : Gen UInt64 := do return UInt64.ofNat (← nat (2 ^ 64))

def bytes (n : Nat) : Gen (List UInt8) := (List.range n).mapM fun _ => do return UInt8.ofNat (← nat 256)

def pick {α : Type} [Inhabited α] (xs : List α) : Gen α := do return xs[← nat xs.length]!

/-- Random registers and flags, and no memory. -/
def machine : Gen MachineData := do
  let r : Reg64s := {
    rax := ← u64
    rbx := ← u64
    rcx := ← u64
    rdx := ← u64
    rsi := ← u64
    rdi := ← u64
    rsp := ← u64
    rbp := ← u64
    r8 := ← u64
    r9 := ← u64
    r10 := ← u64
    r11 := ← u64
    r12 := ← u64
    r13 := ← u64
    r14 := ← u64
    r15 := ← u64 }
  let b : Gen Bool := do return (← nat 2) == 1
  return { regs := r, status := ⟨← b, ← b, ← b, ← b, ← b, ← b⟩ }

/-- The return address of `start`: no program of the fuzzer is there. -/
def ret : Int64 := 0x0b0b0b0b0b0b0000

def setReg (s : MachineData) (r : Reg64) (v : Nat) : MachineData :=
  { s with regs := s.regs.set64 r (BitVec.ofNat 64 v) }

/-- Writes `bs` at `a`, mapping these bytes. -/
def write (s : MachineData) (a : Nat) (bs : List UInt8) : MachineData :=
  { s with dmem := Mem.storeBytes s.dmem (BitVec.ofNat 64 a) bs }

/-- `rsp` at a fixed address, with `below` random bytes mapped below it and `above` above it. -/
def stack (s : MachineData) (below : Nat := 512) (above : Nat := 64) : Gen MachineData := do
  let top := 0x7ffe0000
  let s := write s (top - below) (← bytes (below + above))
  return setReg s .rsp top

/-- Maps `bs` at an address of its own for `r` (the registers' areas do not overlap, nor the
stack) and points `r` to it. -/
def buffer (s : MachineData) (r : Reg64) (bs : List UInt8) (offset : Nat := 0) : Gen MachineData := do
  let a := 0x10000000 + 0x100000 * r.idx + offset
  return setReg (write s a bs) r a

/-- A machine with a stack; for each register of `blocks` and `contents` a buffer of its own; then
the registers of `regs` set. A block `(r, o, n)`: `n` bytes at `r + o` are mapped; a content
`(r, o, bs)`: the bytes `bs` are at `r + o`. The buffer of `r` is random bytes up to the end of its
last block or content, with the contents written over them. -/
def state (blocks : List (Reg64 × Nat × Nat)) (contents : List (Reg64 × Nat × List UInt8))
    (regs : List (Reg64 × Nat)) : Gen MachineData := do
  let mut s ← stack (← machine)
  for r in (blocks.map (·.1) ++ contents.map (·.1)).eraseDups do
    let len := (blocks.filter (·.1 == r)).foldl (fun m (_, o, n) => max m (o + n)) 0
    let cs := contents.filter (·.1 == r)
    let len := cs.foldl (fun m (_, o, bs) => max m (o + bs.length)) len
    s ← buffer s r (← bytes len)
    let a := s.regs.get64 r
    s := cs.foldl (fun s (_, o, bs) => write s (a + BitVec.ofNat 64 o).toNat bs) s
  return regs.foldl (fun s (r, v) => setReg s r v) s

/-- A small number, for a `Nat` variable. -/
def small : Gen Nat := nat 10

/-- Up to 12 random bytes, for a `List UInt8` variable. -/
def someBytes : Gen (List UInt8) := do bytes (← nat 13)

/-- A small number, for a `BitVec w` variable. -/
def smallBV (w : Nat) : Gen (BitVec w) := do return BitVec.ofNat w (← nat 10)

/-! ## Running a program -/

structure Visit where
  label : String
  data : MachineData

inductive Outcome where
  | exit (pc : Int64) (data : MachineData)
  | fault (pc : Int64) (msg : String)
  | fuel

/-- Resolves the effects of one step; an undefined value is chosen from `h`. -/
partial def resolve (h : UInt64) : Effects → Except String MachineState
  | .done s => .ok s
  | .unimplemented msg => .error s!"unimplemented: {msg}"
  | .gp_unaligned a w => .error s!"#GP: unaligned {w}-byte access at {a.toNat}"
  | .fault f => .error (toString f)
  | .nonmem_load _ a _ _ => .error s!"load at the unmapped address {a.toNat}"
  | .nonmem_store _ a _ _ => .error s!"store at the unmapped address {a.toNat}"
  | @Effects.undefined _ t cont => resolve h (cont (t.from_hash h))
  | .require_read_access _ _ ok | .require_write_access _ _ ok | .require_exec_access _ ok => resolve h (ok ())

def isCall : Directive → Bool
  | .instr (.regular _ _ (.call _)) => true
  | _ => false

def isRet : Directive → Bool
  | .instr (.regular _ _ .ret) => true
  | _ => false

/-- The label of a target `l` (the parser gives `l - after_current_instruction`). -/
def relLabel? : RelRegOrMem → Option Label
  | .rel (.label l) | .rel (.sub (.label l) .after_current_instruction) => some l
  | _ => none

/-- The label that a jump goes to. -/
def jumpTarget? : Directive → Option Label
  | .instr (.regular _ _ (.jcc _ l)) => some l
  | .instr (.regular _ _ (.jmp t)) => relLabel? t
  | _ => none

/-- `p` has a back edge: a jump to a label at or before the jump in the text, so at or before the
jump's block. -/
def hasBackEdge (p : Program) : Bool :=
  (p.foldl (init := (([] : List Label), false)) fun (seen, found) d => match d with
    | .label l => (l :: seen, found)
    | d => (seen, found || (jumpTarget? d).any seen.contains)).2

/-- `p` has a call of code outside it: of a label that is not in `p`, or of a register or memory. -/
def callsOutside (p : Program) : Bool :=
  p.any fun d => match d with
    | .instr (.regular _ _ (.call t)) => !(relLabel? t).any (Program.labels p).contains
    | _ => false

/-- Runs `p` from its first directive in state `s` and gives the visits of its labels (outside
calls) and how the run ended: at an address outside `p`, by a fault, or out of fuel. -/
def run (p : Program) (s : MachineData) (fuel : Nat) (seed : Nat) : Array Visit × Outcome := Id.run do
  let exe := p.fakeLayout
  let ds := exe.withAddresses
  let some first := ds.head? | return (#[], .exit exe.startAddr s)
  let mut st : MachineState := ⟨s, first.addr⟩
  let mut visits : Array Visit := #[]
  let mut depth := 0
  for _ in [0:fuel] do
    let here := ds.filter (·.addr == st.pc)
    if here.isEmpty then return (visits, .exit st.pc st.data)
    if depth == 0 then
      for d in here do
        if let .label l := d.directive then visits := visits.push ⟨l, st.data⟩
    let call := here.any (isCall ·.directive)
    let ret := here.any (isRet ·.directive)
    match resolve (hash (st.data.regs, seed)) (exe.step st .done) with
    | .error msg => return (visits, .fault st.pc msg)
    | .ok st' =>
      if call then depth := depth + 1
      else if ret && depth > 0 then depth := depth - 1
      -- a step that stays at the same address (a jump to itself) visits its labels again
      st := st'
  return (visits, .fuel)

/-! ## The check -/

/-- A conjunct of an invariant: its label, its number, its text, and its value. -/
structure Conjunct (T : Type) where
  label : String
  index : Nat
  text : String
  eval : T → MachineData → MachineData → Bool

/-- A conjunct of the postcondition. -/
structure PostConjunct (T : Type) where
  index : Nat
  text : String
  eval : T → Int64 → MachineData → Bool

def showRegs (s : MachineData) : String :=
  let r := s.regs
  s!"rax={r.rax.toNat} rbx={r.rbx.toNat} rcx={r.rcx.toNat} rdx={r.rdx.toNat} rsi={r.rsi.toNat} " ++
  s!"rdi={r.rdi.toNat} rsp={r.rsp.toNat} r8={r.r8.toNat} r9={r.r9.toNat}"

/-- Runs the samples and reports the first failure of each kind. A run that ends at the end of `p`
falls through: `fall` is checked there (the `Q` of a triple), and `post` at each other exit. -/
def check {T : Type} (p : Program) (gen : Gen T) (pre : T → Bool) (start : T → MachineData)
    (invs : List (Conjunct T)) (var : T → String → MachineData → Nat) (post fall : List (PostConjunct T))
    (runs seed fuel : Nat) : String := Id.run do
  let exe := p.fakeLayout
  let endAddr := exe.startAddr + Int64.ofNat (exe.program.foldl (· + ·.size) 0)
  let labels := Program.labels p
  let idx (l : String) := labels.idxOf l
  let mut g := mkStdGen seed
  let mut ran := 0
  let mut skipped := 0
  let mut visits := 0
  let mut reports : Array String := #[]
  let mut seen : Array String := #[]
  for k in [0:runs * 20] do
    if ran == runs then break
    let (t, g') := gen.run g
    g := g'
    if !pre t then skipped := skipped + 1; continue
    ran := ran + 1
    let s₀ := start t
    let (vs, out) := run p s₀ fuel (seed + k)
    visits := visits + vs.size
    let report (key msg : String) (reports seen : Array String) : Array String × Array String :=
      if seen.contains key then (reports, seen) else (reports.push s!"sample {ran}: {msg}", seen.push key)
    let mut prev : Option Visit := none
    for v in vs do
      for c in invs.filter (·.label == v.label) do
        unless c.eval t s₀ v.data do
          (reports, seen) := report s!"inv {c.label} {c.index}"
            s!"invariant at {c.label}, conjunct {c.index}, false at a visit: {c.text}\n  state: {showRegs v.data}" reports seen
      if let some u := prev then
        let a := var t u.label u.data
        let b := var t v.label v.data
        unless b < a || (b == a && idx u.label < idx v.label) do
          (reports, seen) := report s!"var {u.label} {v.label}"
            s!"variant does not decrease from {u.label} ({a}) to {v.label} ({b})" reports seen
      prev := some v
    match out with
    | .exit pc d =>
      if pc == endAddr then
        for c in fall do
          unless c.eval t pc d do
            (reports, seen) := report s!"fall {c.index}"
              s!"fall-through condition, conjunct {c.index}, false at the end of the program: {c.text}\n  state: {showRegs d}" reports seen
      else
        for c in post do
          unless c.eval t pc d do
            (reports, seen) := report s!"post {c.index}"
              s!"postcondition, conjunct {c.index}, false at the exit to {pc.toBitVec.toNat}: {c.text}\n  state: {showRegs d}" reports seen
    | .fault pc msg =>
      (reports, seen) := report s!"fault {pc}" s!"the run faults: {msg}" reports seen
    | .fuel => (reports, seen) := report "fuel" s!"the run did not end within {fuel} steps" reports seen
  let head := s!"{ran} samples ({skipped} skipped by pre), {visits} label visits: "
  if ran == 0 then return head ++ "no sample satisfied pre."
  if reports.isEmpty then return head ++ "no check failed."
  return head ++ s!"{reports.size} failures\n" ++ "\n".intercalate reports.toList

/-! ## The command -/

open Lean Elab Command Term Meta

/-- Reduces the `match`es at the head of `e` (on the label), and nothing else, so that `<` and the
predicates keep the forms that have `Decidable` instances. -/
meta partial def reduceMatches (e : Expr) : MetaM Expr := do
  match ← reduceMatcher? e.headBeta with
  | .reduced e' => reduceMatches e'
  | _ => return e.headBeta

/-- The conjuncts of a proposition, split at top-level `∧`. -/
meta partial def conjuncts (e : Expr) : MetaM (List Expr) := do
  let e ← reduceMatches (← whnfR e)
  match e.and? with
  | some (a, b) => return (← conjuncts a) ++ (← conjuncts b)
  | none => return [e]

/-- `fun (t : T) => body`, where the `xs` are the projections of `t` (a right-nested tuple). -/
meta def lambdaTuple (xs : Array Expr) (T : Expr) (body : Expr) : MetaM Expr := do
  withLocalDeclD `t T fun t => do
    let mut projs : Array Expr := #[]
    let mut cur := t
    for i in [0:xs.size] do
      if i + 1 == xs.size then projs := projs.push cur
      else
        projs := projs.push (← mkAppM ``Prod.fst #[cur])
        cur ← mkAppM ``Prod.snd #[cur]
    mkLambdaFVars #[t] ((← mkLambdaFVars xs body).beta projs)

/-- `Prod a b` -/
meta def prodTy (a b : Expr) : Expr := mkApp2 (Lean.mkConst ``Prod [Level.zero, Level.zero]) a b

/-- The tuple type of the variables, right-nested (`Unit` for none). -/
meta def tupleType (xs : Array Expr) : MetaM Expr := do
  let tys ← xs.mapM inferType
  if tys.isEmpty then return Lean.mkConst ``Unit
  return tys.pop.foldr prodTy tys.back!

/-- The tuple of the variables, as `tupleType`. -/
meta def tupleOf (xs : Array Expr) : MetaM Expr := do
  if xs.isEmpty then return Lean.mkConst ``Unit.unit
  xs.pop.foldrM (fun a b => mkAppM ``Prod.mk #[a, b]) xs.back!

/-- `throw` of a reason why a test is not run. -/
meta def notRun {m : Type → Type} {α : Type} [MonadExceptOf String m] (reason : String) : m α :=
  throwThe String reason

/-- Expands local lets before a term becomes part of an executable check. -/
meta def expandLets (e : Expr) : MetaM Expr := do
  zetaReduce (← instantiateMVars e)

/-- Unfolds predicates only after instance synthesis fails. The fuel bounds all visits,
including both sides of a connective; successful instance forms are kept. -/
meta partial def unfoldForDecision (fuel : Nat) (p : Expr) : MetaM (Expr × Nat) := do
  match fuel with
  | 0 => return (p, 0)
  | fuel + 1 =>
    if (← synthInstance? (mkApp (Lean.mkConst ``Decidable) p)).isSome then
      return (p, fuel)
    match p.getAppFnArgs with
    | (op, #[a, b]) =>
      if op == ``And || op == ``Or || op == ``Iff then
        let (a, fuel) ← unfoldForDecision fuel a
        let (b, fuel) ← unfoldForDecision fuel b
        return (mkApp2 (Lean.mkConst op) a b, fuel)
    | (``Not, #[a]) =>
      let (a, fuel) ← unfoldForDecision fuel a
      return (mkApp (Lean.mkConst ``Not) a, fuel)
    | _ => pure ()
    if let .forallE n a b bi := p then
      if !b.hasLooseBVars && (← isProp a) then
        let (a, fuel) ← unfoldForDecision fuel a
        let (b, fuel) ← unfoldForDecision fuel b
        return (.forallE n a b bi, fuel)
    if let some p' ← unfoldDefinition? p then
      if p' != p then return ← unfoldForDecision fuel p'
    return (p, fuel)

/-- `decide p`, or the original reason that `p` is not decidable. -/
meta def decideOr (what : String) (p : Expr) : ExceptT String MetaM Expr := do
  let original := p
  let p ← expandLets p
  if let some inst ← synthInstance? (mkApp (Lean.mkConst ``Decidable) p) then
    return mkApp2 (Lean.mkConst ``Decidable.decide) p inst
  let (p, _) ← unfoldForDecision 32 p
  let some inst ← synthInstance? (mkApp (Lean.mkConst ``Decidable) p)
    | notRun s!"{what} is not decidable: {← ppExpr original}"
  return mkApp2 (Lean.mkConst ``Decidable.decide) p inst

/-- The reason that `e` depends on a free variable other than the `data`, if it does. -/
meta def closedOver (what : String) (data : Array Expr) (e : Expr) : ExceptT String MetaM Unit := do
  let e ← expandLets e
  if let some f := (collectFVars {} e).fvarIds.find? fun f => !data.contains (.fvar f) then
    let d ← f.getDecl
    notRun s!"{what} depends on {d.userName} : {← ppExpr d.type}"

/-! ### The generator from the hypotheses

The vocabulary, for a variable `x : MachineData`: in `Mem.Mapped [(a, n), …] x.dmem`, each block
whose address `a` is a register `r` of `x` (`x.regs.r.toBitVec` or `x.regs.get64 .r`), plus an
offset that does not depend on `x`, gets a buffer of its own at `r` (`Fuzz.state`); so does
`Mem.Contains x.dmem a bs`, with the bytes `bs` written there; an equation between a register of
`x` (`x.regs.r.toNat`, `x.regs.r.toBitVec`, `x.regs.r`) and a term that does not depend on `x`
sets the register. The stack pointer keeps its stack. Other hypotheses do not change the
generator; `pre` decides each of them. -/

/-- `e` is `x.regs` -/
meta def isRegsOf (x e : Expr) : Bool := e.isAppOfArity ``MachineData.regs 1 && e.appArg! == x

/-- The register of `x.regs.r : UInt64`, as a constructor of `Reg64`. -/
meta def regField? (x e : Expr) : MetaM (Option Expr) := do
  let .app (.const f _) rs := e | return none
  unless isRegsOf x rs && f.getPrefix == ``Reg64s do return none
  let r := Name.str ``Reg64 f.getString!
  return if (← getEnv).contains r then some (Lean.mkConst r) else none

/-- The register of `x` as a `BitVec 64`: `x.regs.r.toBitVec` or `x.regs.get64 r`. -/
meta def regBV? (x e : Expr) : MetaM (Option Expr) := do
  match e.getAppFnArgs with
  | (``UInt64.toBitVec, #[u]) => regField? x u
  | (``Reg64s.get64, #[rs, r]) => return if isRegsOf x rs && r.isConst then some r else none
  | _ => return none

/-- The register of `x` as a `Nat`: `x.regs.r.toNat`, or `.toNat` of `regBV?`. -/
meta def regNat? (x e : Expr) : MetaM (Option Expr) := do
  match e.getAppFnArgs with
  | (``UInt64.toNat, #[u]) => regField? x u
  | (``BitVec.toNat, #[_, b]) => regBV? x b
  | _ => return none

/-- An address `r + o` of `x`: `regBV?`, plus an offset that does not depend on `x`; gives the
register and the offset as a `Nat`. -/
meta def regAddr? (x e : Expr) : MetaM (Option (Expr × Expr)) := do
  if let some r ← regBV? x e then return some (r, mkNatLit 0)
  let (``HAdd.hAdd, #[_, _, _, _, a, d]) := e.getAppFnArgs | return none
  if d.containsFVar x.fvarId! then return none
  let some r ← regBV? x a | return none
  return some (r, ← mkAppM ``BitVec.toNat #[d])

/-- The arguments of `Fuzz.state` for a variable `x : MachineData`. -/
structure Facts where
  blocks : Array Expr := #[]
  contents : Array Expr := #[]
  regs : Array Expr := #[]

/-- Adds what the proposition `p` says about `x` (see the vocabulary above). -/
meta def addFact (x : Expr) (fs : Facts) (p : Expr) : MetaM Facts := do
  let free (e : Expr) : Bool := !e.containsFVar x.fvarId!
  let isDmem (m : Expr) : Bool := m.isAppOfArity ``MachineData.dmem 1 && m.appArg! == x
  let set (r v : Expr) : MetaM Facts := do return { fs with regs := fs.regs.push (← mkAppM ``Prod.mk #[r, v]) }
  match p.getAppFnArgs with
  | (``Eq, #[ty, a, b]) =>
    for (u, v) in [(a, b), (b, a)] do
      unless free v do continue
      if ty.isConstOf ``Nat then
        if let some r ← regNat? x u then return ← set r v
      else if ty.isConstOf ``UInt64 then
        if let some r ← regField? x u then return ← set r (← mkAppM ``UInt64.toNat #[v])
      else if ty.isAppOfArity ``BitVec 1 then
        if let some r ← regBV? x u then return ← set r (← mkAppM ``BitVec.toNat #[v])
    return fs
  | (``Mem.Mapped, #[_, bs, m]) =>
    let some (_, elems) := bs.listLit? | return fs
    unless isDmem m do return fs
    let mut fs := fs
    for b in elems do
      let (``Prod.mk, #[_, _, a, n]) := b.getAppFnArgs | continue
      let some (r, o) ← regAddr? x a | continue
      if r.isConstOf ``Reg64.rsp || !free n then continue
      fs := { fs with blocks := fs.blocks.push (← mkAppM ``Prod.mk #[r, ← mkAppM ``Prod.mk #[o, n]]) }
    return fs
  | (``Mem.Contains, #[_, m, a, bs]) =>
    unless isDmem m && free bs do return fs
    let some (r, o) ← regAddr? x a | return fs
    if r.isConstOf ``Reg64.rsp then return fs
    return { fs with contents := fs.contents.push (← mkAppM ``Prod.mk #[r, ← mkAppM ``Prod.mk #[o, bs]]) }
  | _ => return fs

/-- The generator of a variable, from its type and, for a machine, the hypotheses. -/
meta def varGen (hyps : Array Expr) (x : Expr) : ExceptT String MetaM Expr := do
  let ty ← instantiateMVars (← inferType x)
  let nat := Lean.mkConst ``Nat
  if ty.isConstOf ``MachineData then
    let mut fs : Facts := {}
    for h in hyps do
      for p in ← conjuncts h do fs ← addFact x fs p
    let reg := Lean.mkConst ``Reg64
    return mkApp3 (Lean.mkConst ``Fuzz.state)
      (← mkListLit (prodTy reg (prodTy nat nat)) fs.blocks.toList)
      (← mkListLit (prodTy reg (prodTy nat (← mkAppM ``List #[Lean.mkConst ``UInt8]))) fs.contents.toList)
      (← mkListLit (prodTy reg nat) fs.regs.toList)
  if ty.isConstOf ``Int64 then return ← mkAppOptM ``Pure.pure #[Lean.mkConst ``Fuzz.Gen, none, ty, Lean.mkConst ``Fuzz.ret]
  if ty.isConstOf ``Nat then return Lean.mkConst ``Fuzz.small
  if ty == (← mkAppM ``List #[Lean.mkConst ``UInt8]) then return Lean.mkConst ``Fuzz.someBytes
  if ty.isAppOfArity ``BitVec 1 then return mkApp (Lean.mkConst ``Fuzz.smallBV) ty.appArg!
  notRun s!"no generator for {← ppExpr x} : {← ppExpr ty}"

/-- A generator of the tuple of the variables (`tupleType`): the variables other than machines
first, so that the facts of a machine can use them. -/
meta def autoGen (data hyps : Array Expr) : ExceptT String MetaM Expr := do
  let mut machines := #[]
  let mut others := #[]
  for x in data do
    if (← instantiateMVars (← inferType x)).isConstOf ``MachineData then machines := machines.push x
    else others := others.push x
  let order := others ++ machines
  let gens ← order.mapM (varGen hyps)
  let genM := Lean.mkConst ``Fuzz.Gen
  let mut e ← mkAppOptM ``Pure.pure #[genM, none, none, ← tupleOf data]
  for (x, g) in (order.zip gens).reverse do
    e ← mkAppOptM ``Bind.bind #[genM, none, none, none, g, ← mkLambdaFVars #[x] e]
  return e

/-! ### The check -/

/-- The `Fuzz.check` term of a test, closed: `data` are the variables of a sample, `T` their tuple
type, `gen` a generator of `T` (closed), and `hyps` the propositions that `pre` decides (each with
its name for a reason). The other parts are over `data`: `start : MachineData`, `inv` and `var`
with the types that `vcgen` takes, `post : Int64 → MachineData → Prop` (the exits) and
`fall : Unit → MachineData → Prop` (the fall-through). -/
meta def mkCheck (p : Expr) (data : Array Expr) (T gen : Expr) (hyps : Array (String × Expr))
    (start inv var : Expr) (post fall : Option Expr) (runs seed fuel : Nat) : ExceptT String MetaM Expr := do
  let p ← expandLets p
  let T ← expandLets T
  let gen ← expandLets gen
  let hyps ← hyps.mapM fun (n, h) => return (n, ← expandLets h)
  let start ← expandLets start
  let inv ← expandLets inv
  let var ← expandLets var
  let post ← post.mapM fun e => do expandLets e
  let fall ← fall.mapM fun e => do expandLets e
  let md := Lean.mkConst ``MachineData
  for (n, h) in hyps do closedOver n data h
  closedOver "the generator" #[] gen
  closedOver "the start state" data start
  closedOver "the invariant" data inv
  closedOver "the variant" data var
  if let some q := post then closedOver "the postcondition" data q
  if let some q := fall then closedOver "the fall-through condition" data q
  let tup (f : Expr) : MetaM Expr := lambdaTuple data T f
  let preB ← tup (← hyps.foldlM (fun e (n, h) => do return mkApp2 (Lean.mkConst ``and) e (← decideOr n h)) (Lean.mkConst ``true))
  let labels ← unsafe evalExpr (List String) (← mkAppM ``List #[Lean.mkConst ``String]) (← mkAppM ``Program.labels #[p])
  let mut cs : Array Expr := #[]
  for l in labels do
    let cl ← withLocalDeclD `s₀ md fun s₀ => withLocalDeclD `s' md fun s' => do
      let parts ← conjuncts (← instantiateMVars (mkApp3 inv s₀ (toExpr l) s'))
      parts.toArray.mapIdxM fun i c => do
        let f ← tup (← mkLambdaFVars #[s₀, s'] (← decideOr s!"the invariant at {l}, conjunct {i + 1}," c))
        return mkAppN (Lean.mkConst ``Fuzz.Conjunct.mk) #[T, toExpr l, toExpr (i + 1), toExpr (toString (← ppExpr c)), f]
    cs := cs ++ cl
  -- the conjuncts of `app q a t`, for an exit to `a` in the state `t`
  let exitCs (what : String) (q? : Option Expr) (app : Expr → Expr → Expr → Expr) :
      ExceptT String MetaM (List Expr) := do
    let some q := q? | return []
    withLocalDeclD `a (Lean.mkConst ``Int64) fun a => withLocalDeclD `t md fun t => do
      let parts ← conjuncts (← instantiateMVars (app q a t))
      let cs ← parts.toArray.mapIdxM fun i c => do
        let f ← tup (← mkLambdaFVars #[a, t] (← decideOr s!"{what}, conjunct {i + 1}," c))
        return mkAppN (Lean.mkConst ``Fuzz.PostConjunct.mk) #[T, toExpr (i + 1), toExpr (toString (← ppExpr c)), f]
      return cs.toList
  let postCs ← exitCs "the postcondition" post fun q a t => mkApp2 q a t
  let fallCs ← exitCs "the fall-through condition" fall fun q _ t => mkApp2 q (Lean.mkConst ``Unit.unit) t
  let pcTy := mkApp (Lean.mkConst ``Fuzz.PostConjunct) T
  let e := mkAppN (Lean.mkConst ``Fuzz.check) #[T, p, gen, preB, ← tup start,
    ← mkListLit (mkApp (Lean.mkConst ``Fuzz.Conjunct) T) cs.toList, ← tup var,
    ← mkListLit pcTy postCs, ← mkListLit pcTy fallCs, toExpr runs, toExpr seed, toExpr fuel]
  let e ← instantiateMVars e
  if e.hasFVar || e.hasMVar then throwError "Fuzz.mkCheck: the term is not closed{indentExpr e}"
  return e

/-- Runs `x` in `TermElabM`. -/
meta def liftE {α : Type} (x : ExceptT String MetaM α) : ExceptT String TermElabM α := ExceptT.mk x.run

syntax (name := fuzzCmd) "#fuzz " ident &" args " bracketedBinder* " with"
  (atomic(" (" &"gen") " := " term ")")? (atomic(" (" &"pre") " := " term ")")? " (" &"start" " := " term ")"
  " (" &"invariant" " := " term ")" " (" &"variant" " := " term ")" (atomic(" (" &"post") " := " term ")")?
  (atomic(" (" &"runs") " := " num ")")? (atomic(" (" &"seed") " := " num ")")?
  (atomic(" (" &"fuel") " := " num ")")? : command

@[command_elab fuzzCmd] meta def elabFuzz : CommandElab := fun stx => do
  let `(command| #fuzz $prog:ident args $bs* with $[(gen := $gen?)]? $[(pre := $pre?)]? (start := $start)
      (invariant := $inv) (variant := $var) $[(post := $post?)]? $[(runs := $runs?)]? $[(seed := $seed?)]?
      $[(fuel := $fuel?)]?) := stx
    | throwUnsupportedSyntax
  let runs := runs?.map (·.getNat) |>.getD 200
  let seed := seed?.map (·.getNat) |>.getD 0
  let fuel := fuel?.map (·.getNat) |>.getD 100000
  let r ← runTermElabM fun _ => elabBinders bs fun xs => ExceptT.run do
    let md := Lean.mkConst ``MachineData
    let p ← elabTerm prog (some (Lean.mkConst ``Program))
    let mut data := #[]
    let mut hyps := #[]
    for x in xs do
      let ty ← instantiateMVars (← inferType x)
      if ← isProp ty then hyps := hyps.push (s!"the hypothesis {← ppExpr x}", ty) else data := data.push x
    if let some q := pre? then hyps := hyps.push ("pre", ← elabTermEnsuringType q (some (mkSort 0)))
    hyps ← hyps.mapM fun (n, h) => return (n, ← expandLets h)
    let T ← tupleType data
    let gen ← match gen? with
      | some g => elabTermEnsuringType g (some (mkApp (Lean.mkConst ``Fuzz.Gen) T))
      | none => liftE (autoGen data (hyps.map (·.2)))
    let start ← elabTermEnsuringType start (some md)
    let invTy ← withLocalDecl `s₀ .implicit md fun s₀ => do
      mkForallFVars #[s₀] (← mkArrow (Lean.mkConst ``String) (← mkArrow md (mkSort 0)))
    let inv ← elabTermEnsuringType inv (some invTy)
    let var ← elabTermEnsuringType var (some (← mkArrow (Lean.mkConst ``String) (← mkArrow md (Lean.mkConst ``Nat))))
    let post ← post?.mapM fun q => do
      elabTermEnsuringType q (some (← mkArrow (Lean.mkConst ``Int64) (← mkArrow md (mkSort 0))))
    synthesizeSyntheticMVarsNoPostponing
    let e ← liftE (mkCheck p data T gen hyps start inv var post none runs seed fuel)
    unsafe evalExpr String (Lean.mkConst ``String) e
  match r with
  | .ok msg => logInfo msg
  | .error reason => logInfo s!"not run: {reason}"

end Fuzz

/-! ## Inside `vcgen`

An elaborator of `vcgen` before Kraken's: it runs `vcgen` (with `fuzz.vcgen` false, so that the
call reaches the next elaborator), and when VCs remain open (goals, or an error) on a program with
a back edge, it runs the test of the `invariants · I · V` of the call on the goal: `gen` and `pre`
from the local context and the precondition, the start state from the precondition's `s₀ = …`
(or the state of `WP.wp`), `post` from `E` and the fall-through condition from `Q`. The result is
one message at `vcgen` that starts with `fuzz:`. Then the error of `vcgen`, if any, is thrown
again: the VCs and errors are those of `vcgen` alone. -/

register_option fuzz.vcgen : Bool := {
  defValue := true
  descr := "at a `vcgen` of a program with a back edge that leaves VCs open, a fuzz test of its invariants" }

initialize Lean.registerTraceClass `Fuzz

namespace Fuzz

open Lean Elab Tactic Meta

/-- The results of the tests in this process, by the hash of their `Fuzz.check` term: the same
invariant, variant and goal again give the result without a new run. -/
meta initialize cache : IO.Ref (Std.HashMap UInt64 String) ← IO.mkRef {}

/-- The samples, the seed and the steps of a run of a test inside `vcgen`. -/
meta def vcgenRuns : Nat := 200
meta def vcgenSeed : Nat := 0
meta def vcgenFuel : Nat := 10000

/-- How a goal of `vcgen` gives the start state. -/
inductive Start where
  /-- the precondition `P` of a triple -/
  | pre (P : Expr)
  /-- the state `s` of `WP.wp p Q E s` -/
  | state (s : Expr)

/-- A goal `⦃ P ⦄ p ⦃ Q; E ⦄` or `WP.wp p Q E s` of a `p : Program`: `p`, the start, `Q` and `E`. -/
meta def vcgenGoal? (t : Expr) : Option (Expr × Start × Expr × Expr) :=
  match t.consumeMData.getAppFnArgs with
  | (``Std.WP.Triple, #[_, _, prog, _, _, _, p, _, P, Q, E]) =>
    if prog.isConstOf ``Program then some (p, .pre P, Q, E) else none
  | (``Std.WP.WP.wp, #[prog, _, _, _, _, _, _, p, Q, E, s]) =>
    if prog.isConstOf ``Program then some (p, .state s, Q, E) else none
  | _ => none

/-- The start state of a precondition `fun s₀ => … ∧ s₀ = e ∧ …`, and its other conjuncts, with
`e` for `s₀`. -/
meta def startOf (P : Expr) : ExceptT String MetaM (Expr × Array Expr) :=
  withLocalDeclD `s₀ (Lean.mkConst ``MachineData) fun s₀ => do
    let parts ← conjuncts (P.beta #[s₀])
    let isStart (c : Expr) : Option Expr := match c.eq? with
      | some (_, a, b) => if a == s₀ && !b.containsFVar s₀.fvarId! then some b else none
      | none => none
    let some e := parts.findSome? isStart
      | notRun "the precondition does not fix the start state (no conjunct `s₀ = …`)"
    return (e, (parts.filter (isStart · != some e)).toArray.map (·.replaceFVar s₀ e))

meta def evalBool (e : Expr) : MetaM Bool := unsafe evalExpr Bool (Lean.mkConst ``Bool) e

/-- The `Fuzz.check` term of the test of a `vcgen` call with the invariant alternatives `alts`,
on a goal with the parts of `vcgenGoal?`, in the goal's context. -/
meta def vcgenCheck (alts : Array Syntax) (p : Expr) (start : Start) (Q E : Expr) :
    ExceptT String TermElabM Expr := do
  unless alts.size == 2 && alts.all (·.getKind == ``Lean.Parser.Tactic.invariantDotAlt) do
    notRun "the invariants are not `· I · V`"
  if ← evalBool (mkApp (Lean.mkConst ``Fuzz.callsOutside) p) then
    notRun "the program calls code outside it"
  let md := Lean.mkConst ``MachineData
  let invTy ← withLocalDecl `s₀ .implicit md fun s₀ => do
    mkForallFVars #[s₀] (← mkArrow (Lean.mkConst ``String) (← mkArrow md (mkSort 0)))
  let inv ← Term.elabTermEnsuringType alts[0]![1] (some invTy)
  let var ← Term.elabTermEnsuringType alts[1]![1]
    (some (← mkArrow (Lean.mkConst ``String) (← mkArrow md (Lean.mkConst ``Nat))))
  Term.synthesizeSyntheticMVarsNoPostponing
  let inv ← expandLets inv
  let var ← expandLets var
  let Q ← expandLets Q
  let E ← expandLets E
  let (start, preHyps) ← match start with
    | .pre P => liftE (startOf (← expandLets P))
    | .state s => pure (← expandLets s, #[])
  let mut hyps := #[]
  let mut vars := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← expandLets d.type
    if ← isProp ty then
      -- a hypothesis about a local instance (`hp : FunDecls.at … = some …` over `[FunDecls]`) says
      -- how the program sits in the host, not what a state is: no sample can decide it
      let mentionsInstance ← (collectFVars {} ty).fvarIds.anyM fun f => return (← isClass? (← f.getType)).isSome
      unless mentionsInstance do hyps := hyps.push (s!"the hypothesis {← ppExpr d.toExpr}", ty)
    else if !d.isLet && (← isClass? ty).isNone then vars := vars.push d.toExpr
  hyps := hyps ++ preHyps.map ("the precondition", ·)
  let parts ← (#[start, inv, var, Q, E] ++ hyps.map (·.2)).mapM instantiateMVars
  let used := parts.foldl collectFVars {}
  let data := vars.filter (used.fvarSet.contains ·.fvarId!)
  let T ← tupleType data
  let gen ← liftE (autoGen data (hyps.map (·.2)))
  liftE (mkCheck p data T gen hyps start inv var (some E) (some Q) vcgenRuns vcgenSeed vcgenFuel)

/-- The result of the test `e` (a closed `Fuzz.check` term), from the cache or from a new run. The
run is a task of its own, so that its heartbeats do not count in the proof's. -/
meta def runCached (e : Expr) : MetaM String := do
  if let some r := (← cache.get)[e.hash]? then return r
  trace[Fuzz] "a new run"
  let f ← unsafe evalExpr (Unit → String) (← mkArrow (Lean.mkConst ``Unit) (Lean.mkConst ``String))
    (.lam `u (Lean.mkConst ``Unit) e .default)
  let r ← IO.ofExcept (← IO.wait (← IO.asTask (IO.lazyPure f)))
  cache.modify (·.insert e.hash r)
  return r

/-- The program of a goal, in a form that the interpreter can run in the file of the proof.
- The projections of the function fragments are reduced: after `rw [FunDecls.body_eq hp]` the
  program is `{ prog := Fn.f, embeds := inst }.prog`, where `inst` is a local instance, and an
  expression with a free variable cannot be evaluated.
- A constant program is unfolded: the proof file imports the code module of a function without
  `meta`, and the interpreter refuses to run a constant that is not `meta`-accessible. -/
meta def reduceProgram (p : Expr) : MetaM Expr :=
  Meta.transform p
    (pre := fun e => do
      if e.isConst && (← inferType e).isConstOf ``Program then
        if let some e' ← unfoldDefinition? e then return .visit e'
      return .continue)
    (post := fun e => return .done (← whnfR e))

/-- The message of the test of the `vcgen` call `stx` on the goal `g`: none for a goal that is not
a triple or `WP.wp` of a program, or a program without a back edge. -/
meta def vcgenMessage (stx : Syntax) (g : MVarId) : TacticM (Option String) := g.withContext do
  let some (p, start, Q, E) := vcgenGoal? (← instantiateMVars (← g.getType)) | return none
  let p ← reduceProgram p
  unless ← evalBool (mkApp (Lean.mkConst ``Fuzz.hasBackEdge) p) do return none
  match ← (vcgenCheck stx[5][0][1].getArgs p start Q E).run with
  | .ok e => return some s!"fuzz: {← runCached e}"
  | .error reason => return some s!"fuzz: not run: {reason}"

@[tactic Lean.Parser.Tactic.vcgen, no_fallback] meta def fuzzVCGen : Tactic := fun stx => do
  -- the option by its name: the constant of `register_option` is not `meta`
  unless (← getOptions).getBool `fuzz.vcgen true do throwUnsupportedSyntax
  let inner := withOptions (·.setBool `fuzz.vcgen false) (evalTactic stx)
  let goals ← getUnsolvedGoals
  let some g := goals.head? | inner
  -- `Tactic.tryCatch` does not backtrack: the messages and goals of `vcgen` stay
  let err? ← Tactic.tryCatch (do inner; return none) fun e => return some e
  let isOpen := err?.isSome || (← getUnsolvedGoals).any (!goals.tail.contains ·)
  if isOpen then
    let s ← Tactic.saveState
    -- an exception of the test (a runtime one too: heartbeats) is a reason, never an error
    let msg? ← tryCatchRuntimeEx (vcgenMessage stx g) fun e => do
      return some s!"fuzz: not run: {← e.toMessageData.toString}"
    s.restore (restoreInfo := true)
    if let some m := msg? then logInfoAt stx m
  if let some e := err? then throw e

end Fuzz

end
