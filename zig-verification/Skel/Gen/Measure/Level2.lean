import Kraken.X64.PrintATT
import Lift.Level2.Code
import Skel.Gen.Asm
import Skel.Gen.Split
import Skel.Gen.Sym

/-! G1-05c. Which instruction forms of the level 2 benchmark (`Lift/Level2/Code.lean`) does the symbolic table of
`Skel/Gen/Sym.lean` lack? This file is a measurement. No other module imports it.

Run: `nix develop -c lake env lean Skel/Gen/Measure/Level2.lean`.

Pass 1 runs the generator on each function: `sites`, `labels`, `split`, and `symBlock` on each raw block. `symBlock`
stops at the first error of a block, so pass 1 gives one error per block.

Pass 2 tests each instruction alone. The test block holds that instruction only. A conditional jump gets a 64-bit `cmp`
before it. A conditional move gets a `cmp` of its own width before it. The `cmp` makes the flags known, so a missing
flag context is not reported as a missing form. The `cmp` is not counted as an instruction. -/

namespace Skel.Gen.Measure

open Skel.Gen

/-- The 17 functions of the level 2 program, in source order. -/
def functions : List String :=
  [ "l2Flags", "l2Bits", "l2Arith", "l2Narrow", "l2Field", "l2PtrStore", "l2IdxPush", "l2IdxPop", "l2TwoLoops",
    "l2Nest", "l2Exit3", "l2Frame", "l2Args8", "l2StackCaller", "l2Wrap", "l2CallLoop", "l2Alias" ]

def code : _root_.Executable := Lift.Level2.Code.code

/-! ## Names and errors -/

/-- The block name of the assembly label `l`: the rule of `labelName` in `Skel/Gen/Sym.lean` (a copy, because that
one is private). -/
def blockNameOf (l : String) : String :=
  let s := (if l.startsWith "." then (l.drop 1).copy else l).map fun c =>
    if c.isAlphanum || c == '_' then c else '_'
  if ["entry", "step", "fn", "Lbl", "St", "run"].contains s then s ++ "_" else s

def fallbackName : Ident := (Ident.parse "solo").getD ⟨"_", by decide⟩

def errTag : GenError → String
  | .noFunction _ => "noFunction"
  | .shape .. => "shape"
  | .unsupported .. => "unsupported"
  | .flags _ => "flags"
  | .frame .. => "frame"
  | .callee _ => "callee"
  | .derive .. => "derive"

def errOffset : GenError → Option Nat
  | .shape o _ | .unsupported o _ | .frame o _ | .flags o | .derive o _ => some o
  | .noFunction _ | .callee _ => none

def errCause : GenError → String
  | .shape _ what | .unsupported _ what | .frame _ what | .derive _ what => what
  | .flags _ => "a flag read that no rule covers"
  | .noFunction n => s!"no function {n}"
  | .callee n => s!"a call to {n}, which has no interface"

/-- The assembly text of the instruction at the offset `o` of `ss`. -/
def textAt (ss : List Site) (o : Nat) : String :=
  match ss.find? (fun s => s.offset == o) with
  | some s => Kraken.X64.ATT.instr s.instr
  | none => "(no instruction)"

/-- One error, with the tag, the offset, the text of the instruction and the cause. -/
def errText (ss : List Site) (e : GenError) : String :=
  match errOffset e with
  | some o => s!"{errTag e} at +{o} [{textAt ss o}]: {errCause e}"
  | none => s!"{errTag e}: {errCause e}"

def isOkR {α : Type} : Except GenError α → Bool
  | .ok _ => true
  | .error _ => false

/-! ## Pass 1: the generator on each function -/

/-- The symbolic result of each raw block of `fn`, as the generator computes it (the steps of `Skel/Test/GenSym.lean`). -/
def blocksOf (fn : String) : Except GenError (List (RawBlock × Except GenError Block)) := do
  let ss ← sites code fn
  let ls ← labels code fn
  let raws ← split ss ls
  let index := raws.map fun b => (b.name, b.offset)
  pure (raws.map fun b => (b, symBlock index b))

def printPass1 (fn : String) : IO Unit := do
  IO.println s!"### {fn}"
  match sites code fn with
  | .error e => IO.println s!"sites: error {errText [] e}"
  | .ok ss =>
    IO.println s!"sites: ok, {ss.length} instructions"
    match blocksOf fn with
    | .error e => IO.println s!"split: error {errText ss e}"
    | .ok bs =>
      IO.println s!"split: ok, {bs.length} blocks"
      for (raw, r) in bs do
        match r with
        | .ok _ => IO.println s!"  block {raw.name.s} (+{raw.offset}): ok"
        | .error e => IO.println s!"  block {raw.name.s} (+{raw.offset}): {errText ss e}"

/-! ## Pass 2: each instruction alone -/

/-- The form of an instruction: its assembly mnemonic (with the width suffix), the kinds of its operands, and its
operation width. The kinds are `reg`, `mem`, `imm`, `label` and `ind` (an indirect target). -/
def splitTop (s : String) : List String :=
  let (ps, cur, _) := s.toList.foldl stepTop ([], "", 0)
  ps ++ [cur]
where
  stepTop (acc : List String × String × Nat) (c : Char) : List String × String × Nat :=
    let (ps, cur, d) := acc
    if c == ',' && d == 0 then (ps ++ [cur], "", d)
    else if c == '(' then (ps, cur.push c, d + 1)
    else if c == ')' then (ps, cur.push c, d - 1)
    else (ps, cur.push c, d)

def operandKind (o : String) : String :=
  if o.startsWith "$" then "imm"
  else if o.startsWith "*" then "ind"
  else if o.contains '(' then "mem"
  else if o.startsWith "%" then "reg"
  else "label"

def widthName : Width → String
  | .W8 => "W8"
  | .W16 => "W16"
  | .W32 => "W32"
  | .W64 => "W64"

def formKey (i : Instr) : String :=
  match i with
  | .regular _ w _ =>
    let t := Kraken.X64.ATT.instr i
    let mn := (t.takeWhile (· != ' ')).toString
    let args := (t.dropWhile (· != ' ')).toString.trimAscii.toString
    let operands := (splitTop args).map (fun x => x.trimAscii.toString) |>.filter (· != "")
    let joined := ",".intercalate (operands.map operandKind)
    s!"{mn} [{joined}] {widthName w}"
  | .avx .. => "avx"

/-- The `cmp` that makes the flags of the test block known: `cmp %rdi, %rsi` at the width `w`. -/
def cmpAt (w : Width) : Instr :=
  .regular .W64 w (.cmp (.reg (.low .rsi w)) (.regOrMem (.reg (.low .rdi w))))

/-- The instructions before `i` in its test block. -/
def prefixOf : Instr → List Instr
  | .regular _ _ (.jcc _ _) => [cmpAt .W64]
  | .regular _ w (.cmovcc _ _ _) => if w == .W32 || w == .W64 then [cmpAt w] else []
  | _ => []

/-- The label of a direct jump or conditional jump. -/
def jumpLabel : Instr → Option String
  | .regular _ _ (.jcc _ l) => some l
  | .regular _ _ (.jmp (.rel (.sub (.label l) .after_current_instruction))) => some l
  | _ => none

/-- The symbolic result of one instruction, alone: its test block, then the next block at offset 7. A jump names
the block of its label at offset 7 too, so that the label is found. -/
def soloResult (i : Instr) : Except GenError Block :=
  let body : List Site := (prefixOf i).map (fun j => (⟨0, j⟩ : Site)) ++ [⟨3, i⟩]
  let index : List (Ident × Nat) :=
    match jumpLabel i with
    | some l => [((Ident.parse (blockNameOf l)).getD fallbackName, 7)]
    | none => []
  symBlock index ⟨fallbackName, 0, body, some 7⟩

structure Solo where
  fn : String
  offset : Nat
  text : String
  form : String
  /-- `ok`, or the tag of the error. -/
  tag : String
  cause : String

def soloOf (fn : String) (s : Site) : Solo :=
  let base : Solo :=
    { fn := fn, offset := s.offset, text := Kraken.X64.ATT.instr s.instr, form := formKey s.instr, tag := "ok",
      cause := "" }
  match soloResult s.instr with
  | .ok _ => base
  | .error e => { base with tag := errTag e, cause := errCause e }

def solosOf (fn : String) : List Solo :=
  match sites code fn with
  | .ok ss => ss.map (soloOf fn)
  | .error _ => []

def allSolos : List Solo := functions.flatMap solosOf

def accepted (xs : List Solo) : List Solo := xs.filter (·.tag == "ok")

def missing (xs : List Solo) : List Solo := xs.filter (·.tag != "ok")

/-! ## Printing -/

def printPass2 (fn : String) : IO Unit := do
  let xs := solosOf fn
  IO.println s!"{fn}: {(accepted xs).length} of {xs.length} instructions accepted"
  for s in missing xs do
    IO.println s!"  +{s.offset} [{s.text}] {s.tag}: {s.cause}"

structure FormRow where
  form : String
  tag : String
  count : Nat
  fns : List String

def formRow (k : String) : FormRow :=
  let xs := missing allSolos |>.filter (·.form == k)
  { form := k, tag := (xs.head?.map (·.tag)).getD "", count := xs.length, fns := (xs.map (·.fn)).eraseDups }

/-- The family of a missing form, by its operation and its operation width (the key of `formKey`). -/
def familyOf (form : String) : String :=
  let parts := form.splitOn " "
  let mn := parts.headD ""
  let w := parts.getLastD ""
  if mn.startsWith "j" && mn != "jmp" then "jcc other than e, be, ae"
  else if mn.startsWith "cmov" then "cmovcc other than l"
  else if mn.startsWith "set" then "setcc"
  else if mn.startsWith "sbb" || mn.startsWith "adc" then "sbb and adc"
  else if mn.startsWith "imul" || mn.startsWith "mul" || mn.startsWith "div" || mn.startsWith "idiv" then
    "imul, mul and div"
  else if mn.startsWith "movz" || mn.startsWith "movs" then "sign and zero extension"
  else if mn.startsWith "sh" then "shifts"
  else if w == "W8" || w == "W16" then
    (if mn.startsWith "mov" then "8-bit and 16-bit moves" else "8-bit and 16-bit arithmetic, compare and test")
  else if w == "W32" then "32-bit operations"
  else "64-bit logic and unary operations"

def printFormTable : IO Unit := do
  let forms := (missing allSolos).map (·.form) |>.eraseDups
  let rows := (forms.map formRow).mergeSort (fun a b => a.count ≥ b.count)
  IO.println "| Form (mnemonic, operand kinds, width) | Error | Family | Instructions | Functions |"
  IO.println "|---|---|---|---|---|"
  for r in rows do
    IO.println s!"| `{r.form}` | {r.tag} | {familyOf r.form} | {r.count} | {", ".intercalate r.fns} |"

def printFamilyTable : IO Unit := do
  let miss := missing allSolos
  let fams := (miss.map (fun s => familyOf s.form)).eraseDups
  let rows := fams.map fun f =>
    let xs := miss.filter (fun s => familyOf s.form == f)
    (f, xs.length, (xs.map (·.form)).eraseDups.length)
  IO.println "| Family | Instructions | Distinct forms |"
  IO.println "|---|---|---|"
  for (f, n, k) in rows.mergeSort (fun a b => a.2.1 ≥ b.2.1) do
    IO.println s!"| {f} | {n} | {k} |"

/-- A memory operand with an index register, as `(%rdi,%rcx,8)`. -/
def hasIndexed (t : String) : Bool :=
  ((t.splitOn "(").drop 1).any fun piece => ((piece.takeWhile (· != ')')).toString.contains ',')

/-- A stack frame access: `(%rsp)`, or the implicit stack access of `push`, `pop`, `call` or `ret`. -/
def hasStack (t : String) : Bool :=
  let mn := (t.takeWhile (· != ' ')).toString
  (t.splitOn "(%rsp").length > 1 || ["push", "pop", "call", "ret"].any (fun p => mn.startsWith p)

def printCrossCut : IO Unit := do
  let props : List (String × (Solo → Bool)) :=
    [ ("indexed address", fun s => hasIndexed s.text),
      ("any memory operand", fun s => s.text.contains '('),
      ("stack frame access", fun s => hasStack s.text) ]
  IO.println "| Operand property | Instructions | Missing |"
  IO.println "|---|---|---|"
  for (name, p) in props do
    IO.println s!"| {name} | {(allSolos.filter p).length} | {((missing allSolos).filter p).length} |"

def printNearest : IO Unit := do
  let rows := functions.map fun fn => (fn, (solosOf fn).length, (missing (solosOf fn)).length)
  for (fn, n, m) in (rows.mergeSort (fun a b => a.2.2 ≤ b.2.2)).take 5 do
    IO.println s!"{fn}: {n - m} of {n} instructions accepted, {m} missing"

def printPass1Totals : IO Unit := do
  let splitOk := functions.filter fun fn => isOkR (blocksOf fn)
  let allOk := functions.filter fun fn =>
    match blocksOf fn with
    | .ok bs => bs.all (fun p => isOkR p.2)
    | .error _ => false
  let blocks := functions.foldl (fun (acc : Nat × Nat) fn =>
    match blocksOf fn with
    | .ok bs => (acc.1 + (bs.filter (fun p => isOkR p.2)).length, acc.2 + bs.length)
    | .error _ => acc) (0, 0)
  IO.println s!"functions with split ok: {splitOk.length} of {functions.length}"
  IO.println s!"functions with all blocks ok: {allOk.length} of {functions.length}"
  IO.println s!"blocks ok of all blocks (split ok functions): {blocks.1} of {blocks.2}"

/-- The shape and frame errors of pass 1 (each block: its first error) and of pass 2 (each instruction alone). -/
def printShapeFrame : IO Unit := do
  let p1 := functions.flatMap fun fn =>
    match sites code fn with
    | .error _ => []
    | .ok ss =>
      match blocksOf fn with
      | .error e => [s!"pass 1, {fn}, split: {errText ss e}"]
      | .ok bs => bs.filterMap fun (raw, r) =>
        match r with
        | .error e =>
          if errTag e == "shape" || errTag e == "frame" then some s!"pass 1, {fn}, block {raw.name.s}: {errText ss e}"
          else none
        | .ok _ => none
  let p2 := (missing allSolos).filter (fun s => s.tag == "shape" || s.tag == "frame")
    |>.map fun s => s!"pass 2, {s.fn}, +{s.offset} [{s.text}]: {s.tag}: {s.cause}"
  let lines := p1 ++ p2
  if lines.isEmpty then IO.println "none (no shape or frame error in pass 1 or pass 2)"
  for l in lines do
    IO.println l

def main : IO Unit := do
  IO.println s!"names of the functions in the program: {functions.filter (fun n => Lift.Level2.Code.program.labels.contains n) |>.length} of {functions.length}"
  IO.println "# Pass 1: the generator on each function"
  for fn in functions do
    printPass1 fn
  IO.println "# Pass 1 totals"
  printPass1Totals
  IO.println "# Pass 2: each instruction alone"
  for fn in functions do
    printPass2 fn
  IO.println "# Summary of pass 2 (missing forms, by count)"
  printFormTable
  IO.println "# Families of the missing forms"
  printFamilyTable
  IO.println "# Operand properties (instructions of all functions)"
  printCrossCut
  IO.println "# Nearest to full acceptance"
  printNearest
  IO.println "# Shape and frame errors"
  printShapeFrame
  IO.println s!"instructions accepted: {(accepted allSolos).length} of {allSolos.length}"

#eval main

end Skel.Gen.Measure
