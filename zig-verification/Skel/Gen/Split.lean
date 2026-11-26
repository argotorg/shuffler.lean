import Skel.Cfg
import Skel.Gen.Types

/-! The split of the sites of one function into raw blocks (`docs/one-way-lift-g1-plan-20261118.md`, section 2.3 and
2.4, rules 1 and 2; task G1-04). A block starts at the entry, at each label of an instruction, at each jump target, and
at the instruction after a jump, a conditional jump, a call, a return or a `ud2`. The labels are an argument, because a
`Site` has no label. -/

namespace Skel.Gen

/-- The labels of the function `entry` of `code`, each with its offset from the entry. The function ends before the
first end label after its label (the rule of `sites`). An unknown name, or a name with no end label after it, is
`noFunction`. -/
def labels (code : Executable) (entry : String) : Except GenError (List (String × Nat)) := do
  let addressed := Kraken.Executable.withAddresses code
  match addressed.dropWhile (·.directive.label? != some entry) with
  | [] => throw (.noFunction entry)
  | start :: rest =>
    let fn ← (Skel.Cfg.sliceFunction (addressed.map (·.directive)) entry).mapError fun _ => GenError.noFunction entry
    pure <| ((start :: rest).take fn.length).filterMap fun a =>
      a.directive.label?.map fun l => (l, (a.addr - start.addr).toBitVec.toNat)

/-- The name of a block with the assembly label `l` (rule 2, as `blockNameOf`): the label without a leading `.`, each
character that is not an ASCII letter, digit or `_` replaced by `_`, and a word that the generated code uses escaped by
a final `_`. -/
private def nameOfLabel (l : String) : String :=
  let s := (if l.startsWith "." then (l.drop 1).copy else l).map fun c =>
    if c.isAlphanum || c == '_' then c else '_'
  if ["entry", "step", "fn", "Lbl", "St", "run"].contains s then s ++ "_" else s

/-- The name of the block at `offset`: `entry` at offset 0, else the name of the first label at that offset, else
`o<offset>`. A name that is not an identifier is `shape`. -/
private def blockName (ls : List (String × Nat)) (offset : Nat) : Except GenError Ident :=
  let fromLabel := (ls.find? (fun p => p.2 == offset)).map fun p => nameOfLabel p.1
  let s := if offset == 0 then "entry" else fromLabel.getD s!"o{offset}"
  match Ident.parse s with
  | some i => pure i
  | none => throw (.shape offset s!"the name {s} is not an identifier")

/-- The instruction ends a block (rule 1): a jump, a conditional jump, a call, a return or a `ud2`. -/
private def endsBlock : Instr → Bool
  | .regular _ _ (.jcc _ _) | .regular _ _ (.jmp _) | .regular _ _ (.call _) => true
  | .regular _ _ .ret | .regular _ _ .ud2 => true
  | _ => false

/-- The instruction does not pass control to the next instruction: a `jmp`, a `ret` and a `ud2` do not. -/
private def fallsThrough : Instr → Bool
  | .regular _ _ (.jmp _) | .regular _ _ .ret | .regular _ _ .ud2 => false
  | _ => true

/-- The offset that the site `s` jumps to, when `s` is a jump (`none` for a site that is not a jump). A direct jump names
its label as the parser writes it, `label l - after_current_instruction`; any other target of `jmp` is `shape`. A label
that is not in the function, or an offset that is not an instruction start, is `shape`. -/
private def jumpOffset (ls : List (String × Nat)) (offsets : List Nat) (s : Site) : Except GenError (Option Nat) := do
  let target : Option String ← match s.instr with
    | .regular _ _ (.jcc _ l) => pure (some l)
    | .regular _ _ (.jmp (.rel (.sub (.label l) .after_current_instruction))) => pure (some l)
    | .regular _ _ (.jmp _) => throw (.shape s.offset "jump target is not a label")
    | _ => pure none
  match target with
  | none => pure none
  | some l =>
    match ls.find? (fun p => p.1 == l) with
    | none => throw (.shape s.offset s!"jump to {l}, which is outside the function")
    | some (_, off) =>
      if offsets.contains off then pure (some off)
      else throw (.shape s.offset s!"jump to offset {off}, which is not an instruction start")

/-- The sites grouped into blocks, each with its offset. A site starts a block when `isStart` holds for its offset, and
the first site always starts one. -/
private def group (isStart : Nat → Bool) (fn : List Site) : List (Nat × List Site) :=
  (fn.foldl (init := ([] : List (Nat × List Site))) fun acc s =>
    match acc with
    | (o, b) :: bs => if isStart s.offset then (s.offset, [s]) :: acc else (o, s :: b) :: bs
    | [] => [(s.offset, [s])]).reverse.map fun (o, b) => (o, b.reverse)

/-- The raw blocks of the sites `fn` of one function, with its labels `ls`, in order of offset. A jump to a label outside
the function, or to an offset that is not an instruction start, is `shape`. A name that is not unique is `shape`. The
empty list of sites gives no block. -/
def split (fn : List Site) (ls : List (String × Nat)) : Except GenError (List RawBlock) := do
  let offsets := fn.map (·.offset)
  let targets ← fn.mapM (jumpOffset ls offsets)
  let labelStarts := (ls.map (·.2)).filter (fun o => offsets.contains o)
  let afterEnd := ((fn.zip fn.tail).filter (fun p => endsBlock p.1.instr)).map (·.2.offset)
  let starts := offsets.head?.toList ++ labelStarts ++ targets.filterMap id ++ afterEnd
  let blocks := group (fun o => starts.contains o) fn
  let nexts : List (Option Nat) := (blocks.map (·.1)).tail.map some ++ [none]
  let raws ← (blocks.zip nexts).mapM fun ((o, ss), nxt) => do
    let name ← blockName ls o
    let falls := (ss.getLast?.map fun s => fallsThrough s.instr).getD true
    pure (⟨name, o, ss, if falls then nxt else none⟩ : RawBlock)
  match raws.find? (fun b => (raws.filter (fun c => c.name.s == b.name.s)).length ≥ 2) with
  | some b => throw (.shape b.offset s!"two blocks are named {b.name.s}")
  | none => pure raws

end Skel.Gen
