import Skel.Gen.Stmt
import Skel.Gen.Model
import Skel.Gen.Frame
import Skel.Gen.Vars
import Skel.Gen.Sym
import Skel.Gen.Split
import Skel.Gen.Asm
import Skel.Types

/-! The generator of a function (`docs/one-way-lift-g1-plan-20261118.md`, sections 2.3 and 2.4; task G1-10). `generate`
runs the stages from the instructions of a function to its `Generated`. `rows` gives the obligations of a summary.

Rows (rule 10): a block row for each block that has an exit which is not a trap, in block order, with the type of its
statement; then `decompiles_l2` (class `block`, origin `unit`, statement `Decompiles <step> l2`), with the block rows as
its deps. The statement of a row is a type: `Render` adds the head and the proof.

The blocks come from a `BlockSource` (N11): the derived terms (`blocksOf`) or the table of `symBlock` (`tableBlocksOf`). The
toy runs use the derived terms (N14). The address of the return-address store of a call is the value of `rsp` after the call
(`Skel/Gen/Derive/Read.lean`): the stack proof takes the two as one term. The tests compare the two sources where the table
gives a block.

`det` holds the proof text of each block row (`blockDet`, the split proof of N12) and the proof text of `decompiles_l2`
(`decompilesDet`): in the memory form with a guard one lemma for each case before the theorem (MULTI-CALLEE3), else `by`, a
line break and `decompilesProof`. A function with a memory, a stack room or a call gets
the `fail` text of `decompilesProof` as its `det` text; `generate` is then `ok` (the form of O3). The rooms of the callees
are those of `Callee.room`; a call to a function that is not in `Target.callees` gives `GenError.callee` (`checkBlocks`). A
function can call more than one callee (MULTI-CALLEE): each call uses the interface of its callee. -/

namespace Skel.Gen

/-- The blocks of the function `entry` of `code` from the derived parts `d` (N11): the names and offsets of `split`, and
the part of each offset (`Skel/Gen/Derive/Blocks.lean`). The first block with no part is its error: a block with no
derived term, walk or read, and a block of a function that `d` does not have, are `GenError.derive`. -/
def blocksOf (code : Executable) (d : Derived) (entry : String) : Except GenError (List Block) := do
  let raws ← split (← sites code entry) (← labels code entry)
  let parts := (d.lookup entry).getD []
  raws.mapM fun b => do
    let some r := parts.lookup b.offset | throw (.derive b.offset s!"no derived block of {entry}")
    let p ← r
    pure ⟨b.name, b.offset, p.accesses, p.regs, p.term, p.flags⟩

/-- The blocks of the function `entry` of `code` from the table of `symBlock` (G1-05). -/
def tableBlocksOf (code : Executable) (entry : String) : Except GenError (List Block) := do
  let ss ← sites code entry
  let ls ← labels code entry
  let raws ← split ss ls
  let index := raws.map fun b => (b.name, b.offset)
  raws.mapM (symBlock index)

/-- The source of the blocks of `generate` (N11). -/
inductive BlockSource where
  /-- The table of `symBlock` (G1-05): the source of the toy runs. -/
  | table
  /-- The derived parts of the functions (`Skel/Gen/Derive/Blocks.lean`). -/
  | derived (d : Derived)

/-- The blocks of the function `entry` of `code` from the source `src`. -/
def blocksFrom (code : Executable) (src : BlockSource) (entry : String) : Except GenError (List Block) :=
  match src with
  | .table => tableBlocksOf code entry
  | .derived d => blocksOf code d entry

/-- The exits of a block. -/
private def exitsOf (b : Block) : List Exit :=
  match b.term with
  | .exit e => [e]
  | .branch _ y n => [y, n]

/-- The check of the blocks of a function, before the model:
* no block jumps to the entry (offset 0): `At .entry` is the equality `s = s₀`, which a second visit of the entry does not
  satisfy;
* each callee has an interface in `t.callees` (MULTI-CALLEE: a call block uses the interface of its callee). The error
  names the first callee with no interface.
* a call block stores the word of each stack argument of the callee (`argStore`, ARGS8); else `frame`. -/
def checkBlocks (t : Target) (bs : List Block) : Except GenError Unit := do
  match bs.find? fun b => (exitsOf b).any fun | .goto 0 => true | _ => false with
  | some b => throw (.shape b.offset "a jump to the entry")
  | none => pure ()
  let called := calledOf bs
  match called.find? fun f => !t.callees.any (·.name == f) with
  | some f => throw (.callee f)
  | none => pure ()
  match t.callees.find? fun c => 0 < c.room && !c.mem with
  | some c => throw (.frame 0 s!"the callee {c.name} has a stack room but no memory result")
  | none => pure ()
  -- a call passes each stack argument of the callee from a store of the call block to its word (ARGS8, `argStore`)
  bs.forM fun b => (exitsOf b).forM fun
    | .call f _ => do
      let n := ((t.callees.find? (·.name == f)).map (·.stackArgs)).getD 0
      (List.range n).forM fun k =>
        if (argStore b k).isSome then pure ()
        else throw (.frame b.offset s!"the call to {f} passes the stack argument {k}, and the block does not store its word")
    | _ => pure ()

/-- The check of the calls of a callee with memory (PIL-CALL, MULTI-CALLEE2): the bytes that the caller keeps across a call are
counted from the `rsp` of the callee (`Model.keptBytes`, from the depth of the continuation), and the model of the callee has one
restriction for all its calls. So the continuations of the calls of one callee with memory have one depth; else the error names
the callee. Calls from several blocks at one depth are allowed. -/
def checkMemCalls (t : Target) (bs : List Block) (ff : FrameFacts) : Except GenError Unit := do
  let depths (f : String) : List Int := (bs.flatMap fun b => (exitsOf b).filterMap fun
    | .call g k => if g == f then some ((ff.delta.lookup k).getD 0) else none
    | _ => none).eraseDups
  match (calledOf bs).find? fun f => (t.callees.find? (·.name == f)).any (·.mem) && (depths f).length > 1 with
  | some f => throw (.callee f)
  | none => pure ()

/-- The callee interfaces of the function `entry` of `code`, from the code (PIL-CALL): one for each call target of its
blocks, in the order of the first call. `name f` gives the entry PC and the model of the function at the label `f`; a
label that it does not give (no function of the unit) is `GenError.callee`. The inputs, the stack room and the memory are
those of the generated callee: the inputs of its model, the room of its frame facts, and whether its state has memory.
`fuel` bounds the depth of the calls; at 0 a function has no callee. -/
def calleesFrom (code : Executable) (src : BlockSource) (name : String → Option (String × String)) :
    Nat → String → Except GenError (List Callee)
  | 0, _ => pure []
  | fuel + 1, entry => do
    let bs ← blocksFrom code src entry
    (calledOf bs).mapM fun f => do
      let some (pc, model) := name f | throw (.callee f)
      let sub ← calleesFrom code src name fuel f
      let cbs ← blocksFrom code src f
      let ff ← frameFacts (sub.map fun c => (c.name, c.room)) cbs
      let v := modelVars cbs sub ff
      pure ⟨f, model, v.inputs, pc, ff.room, v.mem, stackArgCount ff cbs, some (heapWritesOf cbs sub)⟩

/-- The id of `decompiles_l2` of the function `fn`. -/
private def decompilesId (fn : String) : ObId := { function := fn, name := "decompiles_l2" }

/-- Whether a block has a row (rule 10): it has an exit that is not a trap. -/
private def hasRow (b : Block) : Bool :=
  match b.term with
  | .exit .trap => false
  | .branch _ .trap .trap => false
  | _ => true

/-- The type of the statement of the block `b`: the text of `blockStatement` after its head `theorem <name> : `, and
before its proof `:= by`. A block with no statement is the error of `blockStatement`. -/
private def blockType (t : Target) (s : Summary) (b : Block) : Except GenError String := do
  let head := "theorem " ++ b.name.s ++ " : "
  let text ← blockStatement t s b
  let body := String.ofList (text.toList.drop head.length)
  pure ((body.splitOn " := by").headD body)

/-- The rows of the summary `s` for the target `t` (rule 10): a block row for each block with a row, in block order, then
`decompiles_l2` with the block rows as its deps. A block with a row and no statement is a generation error. -/
def rows (t : Target) (s : Summary) : Except GenError (List Obligation) := do
  let blockRows : List Obligation ← (s.blocks.filter hasRow).mapM fun b => do
    let statement ← blockType t s b
    let row : Obligation :=
      { id := { function := s.fn, name := "block." ++ b.name.s }, cls := .block, origin := .block b.name.s,
        statement := statement, deps := [], claim := .none }
    pure row
  let decomp : Obligation :=
    { id := decompilesId s.fn, cls := .block, origin := .unit, statement := s!"Decompiles {t.step} l2",
      deps := blockRows.map (·.id), claim := .none }
  pure (blockRows ++ [decomp])

/-- The `det` text of a block row: the split block proof (N12). The ladder tries `lift_block` next (`Rungs.detTexts`). -/
def blockDet : String := "by intros; lift_block_split"

/-- The summary of the function `entry` of `code` and its frame text, after the checks of the blocks (`checkBlocks`,
`checkMemCalls`), as `generate` makes them. -/
def summaryOf (t : Target) (f : MemForm) (code : Executable) (src : BlockSource) (entry : String) :
    Except GenError (Summary × FrameText) := do
  let bs ← blocksFrom code src entry
  checkBlocks t bs
  let rooms := t.callees.map fun c => (c.name, c.room)
  let ff ← frameFacts rooms bs
  checkMemCalls t bs ff
  let s : Summary := ⟨entry, bs, modelVars bs t.callees ff, ff, some (heapWritesOf bs t.callees)⟩
  let memCall := bs.any fun b => (exitsOf b).any fun
    | .call g _ => (t.callees.find? (·.name == g)).any (·.mem)
    | _ => false
  pure (s, ← frameText f rooms s memCall)

/-- The generated function `entry` of `code`, with the blocks of the source `src` (N11), for the target `t`, the form of
memory `f`, and the hints `_h` (none in G1): the model text, the rows, no refute text, and the `det` texts of the block
rows (`blockDet`) and of `decompiles_l2` (`decompilesDet`). -/
def generate (t : Target) (_h : Hints) (f : MemForm) (code : Executable) (src : BlockSource) (entry : String) :
    Except GenError Generated := do
  let (s, fr) ← summaryOf t f code src entry
  let obligations ← rows t s
  let blockDets := (obligations.filter (·.origin matches .block _)).map fun o => (o.id, blockDet)
  let rowTy (label : String) : Option String :=
    (obligations.find? (·.origin == .block label)).map (·.statement)
  let det : List (ObId × String) := blockDets ++ [(decompilesId entry, decompilesDet t s fr rowTy)]
  pure { modelText := modelText t s fr, obligations := obligations, det := det, refuteText := fun _ _ => none }

end Skel.Gen
