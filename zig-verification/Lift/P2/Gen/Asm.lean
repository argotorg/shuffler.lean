/-
The analysis of the assembly for the generator of P2 (`Lift/P2/Gen.lean`), on the AST of the lifter: the Kraken
`Program` of one function (`Kraken.X64.Syntax`), the same program that `#lift2` lifts.

* `Cfg`: the labelled blocks and the labelled successors of each (a block ends at its `jmp`, `ret` or `ud2`;
  the instructions after a `jcc` are in the same block, as in the lifted block), the loop heads (back edges of the
  dominator tree), the blocks that call.
* `Frame`: the bytes below the return slot that the function touches (pushes, `sub`/`lea` of `rsp`, the red zone),
  the stack pointer at each label, and for each callee-saved register where the function saved it and whether it
  may differ from its entry value.

Everything is relative to the return slot `f` (the stack pointer at the entry): the stack pointer of an instruction
is `f + delta`, an access `disp(%rsp)` is at `f + delta + disp`. What the analysis cannot bound is `Except.error`
with a reason: a `leave`, the stack pointer used as a value, a dynamic stack address, the address of the frame, an
access above `f`, a stack pointer that differs at a join.
-/
import Lift.V2.Lifter

namespace Lift.P2.Gen
open Lift.V2 Kraken.X64

abbrev R := Except String

def calleeSaved : List Reg64 := [.rbx, .rbp, .r12, .r13, .r14, .r15]

/-- `s` has `sub` as a substring. -/
def hasSub (s sub : String) : Bool := (s.splitOn sub).length > 1

/-! ### The operands of an operation -/

/-- An operand of an instruction. A memory operand has the number of bytes that the instruction accesses. -/
inductive Opd where
  | reg (r : Reg64)
  | mem (a : AddrExpr) (bytes : Nat)
  | imm
  deriving Inhabited

private def regOpd {w : Width} (r : Reg w) : Opd := .reg (Reg.base r)
private def rmOpd {w : Width} : RegOrMem w → Opd
  | .reg r => regOpd r
  | .mem a => .mem a w.bytes
private def opOpd {w : Width} : Operand w → Opd
  | .regOrMem x => rmOpd x
  | .imm _ => .imm
private def dstReg {w : Width} : RegOrMem w → List Reg64
  | .reg r => [Reg.base r]
  | .mem _ => []

/-- The operands of an operation, in the order of the assembler text, and the registers that it writes
(the destination operand, and the registers that it writes without naming them). -/
def opdsOf {w : Width} : Operation w → List Opd × List Reg64
  | .mov d s => ([rmOpd d, opOpd s], dstReg d)
  | .movsx (w' := w') d s => ([rmOpd d, rmOpd (w := w') s], dstReg d)
  | .movzx (w' := w') d s => ([rmOpd d, rmOpd (w := w') s], dstReg d)
  | .push s => ([opOpd s], [])
  | .pop d => ([rmOpd d], dstReg d)
  | .setcc _ d => ([rmOpd d], dstReg d)
  | .cmovcc _ r s => ([regOpd r, rmOpd s], [Reg.base r])
  | .lea r a => ([regOpd r, .mem a 0], [Reg.base r])
  | .add d s | .adc d s | .sub d s | .sbb d s | .and d s | .or d s | .xor d s => ([rmOpd d, opOpd s], dstReg d)
  | .adcx r s | .adox r s => ([regOpd r, rmOpd s], [Reg.base r])
  | .inc d | .dec d | .neg d => ([rmOpd d], dstReg d)
  | .not d => ([rmOpd d], dstReg d)
  | .cmp a b => ([rmOpd a, opOpd b], [])
  | .test a b => ([rmOpd a, opOpd b], [])
  | .xadd _ d r => ([rmOpd d, regOpd r], dstReg d ++ [Reg.base r])
  | .cmpxchg _ d _ => ([rmOpd d], .rax :: dstReg d)
  | .mul s | .imul1 s => ([rmOpd s], [.rax, .rdx])
  | .mulx hi lo s => ([regOpd hi, regOpd lo, rmOpd s], [Reg.base hi, Reg.base lo])
  | .imul d s1 s2 => (((d.map rmOpd).toList) ++ [rmOpd s1, opOpd s2], ((d.map dstReg).getD []))
  | .div s | .idiv s => ([rmOpd s], [.rax, .rdx])
  | .cwtd | .cltd | .cqto => ([], [.rdx])
  | .cbtw | .cwtl | .cltq => ([], [.rax])
  | .shl d _ | .shr d _ | .sar d _ | .rol d _ | .ror d _ | .rcl d _ | .rcr d _ => ([rmOpd d], dstReg d)
  | .shld d r _ | .shrd d r _ => ([rmOpd d, regOpd r], dstReg d)
  | .bswap r => ([regOpd r], [Reg.base r])
  | .bsr r s | .repBsf r s => ([regOpd r, rmOpd s], [Reg.base r])
  | .btc d b => ([rmOpd d, opOpd b], dstReg d)
  | .prefetcht0 a => ([.mem a 0], [])
  | .jcc .. | .jmp _ | .call _ | .ret | .leave | .nop _ | .nopalign .. | .ud2 => ([], [])

/-- The memory operand that the operation writes, with its width in bytes. -/
def memStoreOf {w : Width} : Operation w → Option (AddrExpr × Nat)
  | .mov (.mem a) _ | .setcc _ (.mem a) | .add (.mem a) _ | .adc (.mem a) _ | .sub (.mem a) _ | .sbb (.mem a) _
  | .and (.mem a) _ | .or (.mem a) _ | .xor (.mem a) _ | .inc (.mem a) | .dec (.mem a) | .neg (.mem a)
  | .not (.mem a) | .shl (.mem a) _ | .shr (.mem a) _ | .sar (.mem a) _ | .rol (.mem a) _ | .ror (.mem a) _
  | .rcl (.mem a) _ | .rcr (.mem a) _ | .shld (.mem a) _ _ | .shrd (.mem a) _ _ | .btc (.mem a) _
  | .xadd _ (.mem a) _ | .cmpxchg _ (.mem a) _ | .pop (.mem a) => some (a, w.bytes)
  | _ => none

/-! ### The control-flow graph -/

/-- A labelled block: its label in the assembly, its name in the lifted code (`entry`, `L3`) and its instructions. -/
structure ABlock where
  label : Label
  name : String
  ins : List Instr
  deriving Inhabited

/-- The blocks of a program, in order; the first is the entry. -/
def blocksOf (p : Program) : R (Array ABlock) := do
  let bs ← match splitBlocks p with
    | .ok bs => pure bs
    | .error e => throw s!"{e.cat}: {e.detail}"
  let some (entry, _) := bs.head? | throw "empty program"
  return (bs.map fun (l, is) => { label := l, name := blockNameOf entry l, ins := is : ABlock }).toArray

/-- Names of functions that do not return. -/
def noReturn (l : Label) : Bool :=
  isExceptionName l || hasSub l "__assert_fail" || hasSub l "abort" || hasSub l "__throw_" || hasSub l "terminate"

/-- The instructions of a block that end it: `jmp`, `ret`, `ud2`, a call that does not return. -/
def instrEnds : Instr → Bool
  | .regular _ _ .ret | .regular _ _ .ud2 | .regular _ _ (.jmp _) => true
  | .regular _ _ (.call t) => (relLabel? t).any noReturn
  | _ => false

/-- The labels that a block may go to: the targets of its jumps in the function, then the next block if it falls through. -/
def succsOf (own : List Label) (next : Option Label) (is : List Instr) : List Label :=
  let rec go : List Instr → List Label
    | [] => next.toList
    | i :: rest =>
      let tgt := match i with
        | .regular _ _ (.jcc _ t) => if own.contains t then [t] else []
        | .regular _ _ (.jmp t) => ((relLabel? t).filter own.contains).toList
        | _ => []
      if instrEnds i then tgt else tgt ++ go rest
  go is

/-- The control-flow graph: the blocks and, for each block, the indexes of its successors. -/
structure Cfg where
  blocks : Array ABlock
  succ : Array (List Nat)

def Cfg.ofProgram (p : Program) : R Cfg := do
  let blocks ← blocksOf p
  let own := blocks.toList.map (·.label)
  let succ := blocks.mapIdx fun i b =>
    let next := (blocks[i + 1]?).map (·.label)
    ((succsOf own next b.ins).filterMap fun l => blocks.findIdx? (·.label == l)).eraseDups
  return { blocks, succ }

def Cfg.nameOf (g : Cfg) (i : Nat) : String := (g.blocks[i]?.map (·.name)).getD "?"

/-- The blocks reachable from the entry. -/
def Cfg.reach (g : Cfg) : List Nat := Id.run do
  let mut seen : List Nat := []
  let mut todo := [0]
  for _ in [0:g.blocks.size * g.blocks.size + 1] do
    match todo with
    | [] => break
    | x :: rest =>
      todo := rest
      unless seen.contains x do
        seen := x :: seen
        todo := (g.succ[x]?.getD []) ++ todo
  return seen

/-- The dominators of each reachable block (a fixpoint). -/
def Cfg.dom (g : Cfg) : Array (List Nat) := Id.run do
  let reach := g.reach
  let preds (x : Nat) : List Nat := reach.filter fun y => (g.succ[y]?.getD []).contains x
  let mut dom : Array (List Nat) := (Array.range g.blocks.size).map fun x => if x == 0 then [0] else reach
  for _ in [0:g.blocks.size * g.blocks.size + 5] do
    let mut changed := false
    for x in reach do
      if x == 0 then continue
      let ps := preds x
      let nd :=
        match ps with
        | [] => [x]
        | p :: qs => (qs.foldl (fun acc q => acc.filter (dom[q]!).contains) dom[p]!).eraseDups.filter (· != x) ++ [x]
      if (nd.toArray.qsort (· < ·)) != (dom[x]!.toArray.qsort (· < ·)) then
        dom := dom.set! x nd
        changed := true
    unless changed do break
  return dom

/-- The loop heads: the targets of the back edges (`x → y` where `y` dominates `x`), in the order of the code. -/
def Cfg.heads (g : Cfg) : List Nat :=
  let dom := g.dom
  let reach := g.reach
  let ys := reach.flatMap fun x => (g.succ[x]?.getD []).filter fun y => (dom[x]?.getD []).contains y
  (ys.eraseDups.toArray.qsort (· < ·)).toList

/-- The longest segment from `start`, in blocks: it ends before a block of `cuts` or at a block without successor. -/
def Cfg.depth (g : Cfg) (cuts : List Nat) (start : Nat) : R Nat := do
  let mut memo : Array (Option Nat) := Array.replicate g.blocks.size none
  -- a post-order walk with an explicit stack of the blocks on the path
  let rec go (fuel : Nat) (path : List Nat) (b : Nat) : StateT (Array (Option Nat)) R Nat := do
    match fuel with
    | 0 => throw s!"a cycle without a cut point at {g.nameOf b}"
    | fuel + 1 =>
      if path.contains b then throw s!"a cycle without a cut point at {g.nameOf b}"
      match (← get)[b]? with
      | some (some d) => return d
      | _ =>
        let mut best := 0
        for s in (g.succ[b]?.getD []).filter (!cuts.contains ·) do
          best := max best (← go fuel (b :: path) s)
        modify (·.set! b (some (1 + best)))
        return 1 + best
  let (d, _) ← (go (g.blocks.size + 1) [] start).run memo
  return d

/-! ### Calls -/

/-- The direct calls of a block, in order. -/
def callTargets (is : List Instr) : List (Label × Bool) :=
  -- (target, in the code after the first branch of the block)
  let rec go (after : Bool) : List Instr → List (Label × Bool)
    | [] => []
    | i :: rest =>
      let here := match i with
        | .regular _ _ (.call t) => [((relLabel? t).getD "?", after)]
        | _ => []
      let isBranch := match i with
        | .regular _ _ (.jcc ..) | .regular _ _ (.jmp _) | .regular _ _ .ret | .regular _ _ .ud2 => true
        | _ => instrEnds i
      here ++ go (after || isBranch) rest
  go false is

/-- The blocks that call before their first branch (the names only): they are cut points. -/
def Cfg.callingBlocks (g : Cfg) : List String :=
  g.blocks.toList.filterMap fun b => if (callTargets b.ins).any (!·.2) then some b.name else none

/-- The blocks that call, with the symbol of the callee. A call after the first branch of its block, or two calls in a
block, are not supported. -/
def Cfg.callBlocks (g : Cfg) : R (List (String × Label)) := do
  let mut out := []
  for b in g.blocks do
    let cs := callTargets b.ins
    if cs.any (·.2) then throw s!"a call in the code after a branch (block {b.name})"
    if cs.length > 1 then throw s!"two calls in block {b.name}"
    if let [(t, _)] := cs then out := out ++ [(b.name, t)]
  return out

/-! ### The frame -/

/-- What the function does with a callee-saved register: the offset of the slot that holds its entry value (if it has
been saved) and whether the register may differ from its entry value. -/
structure Saved where
  slot : Option Int := none
  modified : Bool := false
  deriving BEq, Repr

abbrev SavedState := List (Reg64 × Saved)

def SavedState.init : SavedState := calleeSaved.map (·, {})

def SavedState.get (s : SavedState) (r : Reg64) : Saved := (s.lookup r).getD {}
def SavedState.set (s : SavedState) (r : Reg64) (v : Saved) : SavedState :=
  s.map fun (q, x) => if q == r then (q, v) else (q, x)

/-- The join at a block with two predecessors: the slot when both agree, modified when either is. -/
def SavedState.join (a b : SavedState) : SavedState :=
  calleeSaved.map fun r =>
    let x := a.get r; let y := b.get r
    (r, { slot := if x.slot == y.slot then x.slot else none, modified := x.modified || y.modified })

structure LabelFrame where
  delta : Int
  state : SavedState
  deriving Repr

structure Frame where
  /-- The size of the owned region: `[f - n, f)`. -/
  n : Nat
  labels : List (String × LabelFrame)
  deriving Repr

def Frame.label? (f : Frame) (l : String) : Option LabelFrame := f.labels.lookup l

/-- The change of the stack pointer, the registers written and the stack accesses `(offset from the stack pointer before the
instruction, bytes)` of one instruction. -/
structure Effect where
  delta : Int := 0
  writes : List Reg64 := []
  acc : List (Int × Nat) := []

private def rspBase? (a : AddrExpr) : Option (Option Reg64 × Int) :=
  match a.base, a.disp with
  | some (.reg .rsp), .int64 d => some (a.idx.map (·.reg), d.toInt)
  | _, _ => none

private def isRspBase (a : AddrExpr) : Bool := match a.base with | some (.reg .rsp) => true | _ => false

/-- A stack slot `disp(%rsp)` without index: its displacement. -/
def slotDisp? (a : AddrExpr) : Option Int :=
  match rspBase? a with
  | some (none, d) => some d
  | _ => none

private def instrText (i : Instr) : String := match i with | .regular _ _ op => (s!"{repr op}".take 60).toString | .avx .. => "avx"

/-- `subq $v, %rsp`, `addq $v, %rsp`, `leaq d(%rsp), %rsp`: the change of the stack pointer. -/
def rspAdjust {w : Width} (op : Operation w) : Option Int :=
  match w, op with
  | .W64, .sub (.reg (.low .rsp .W64)) (.imm (.int64 v)) => some (-v.toInt)
  | .W64, .add (.reg (.low .rsp .W64)) (.imm (.int64 v)) => some v.toInt
  | .W64, .lea (.low .rsp .W64) a => slotDisp? a
  | _, _ => none

/-- The effect of an instruction; a call keeps the stack pointer (the call step covers the rest). -/
def effect (i : Instr) : R Effect := do
  let .regular _ _ op := i | return {}
  match op with
  | .call _ => return {}
  | .leave => throw "leave"
  | .push s =>
    if let .regOrMem (.mem a) := s then
      if isRspBase a then throw s!"push of a stack operand: {instrText i}"
    return { delta := -8, acc := [(-8, 8)] }
  | .pop d => return { delta := 8, acc := [(0, 8)], writes := dstReg d }
  | _ =>
  if let some v := rspAdjust op then return { delta := v }
  let (opds, writes) := opdsOf op
  let mut acc := []
  for o in opds do
    match o with
    | .imm => pure ()
    | .reg .rsp => throw s!"use of the stack pointer: {instrText i}"
    | .reg _ => pure ()
    | .mem a bytes =>
      if let some (idx, d) := rspBase? a then
        if idx.isSome then throw s!"dynamic stack address: {instrText i}"
        if bytes == 0 && (match op with | .lea .. => true | _ => false) then throw s!"address of the frame: {instrText i}"
        acc := acc ++ [(d, if bytes == 0 then 8 else bytes)]
      else if isRspBase a then throw s!"stack address with a symbol: {instrText i}"
      else if a.idx.any (·.reg == .rsp) then throw s!"stack pointer as index: {instrText i}"
  return { writes, acc }

/-- One instruction on the saved state of the callee-saved registers, at the stack depth `d` before it. -/
def step (d : Int) (st : SavedState) (i : Instr) (e : Effect) : SavedState :=
  match i with
  | .regular _ _ (.push (.regOrMem (.reg (.low r .W64)))) =>
    if calleeSaved.contains r then
      if !(st.get r).modified then st.set r { slot := some (d - 8), modified := false } else st
    else st
  | .regular _ _ (.pop (.reg (.low r .W64))) =>
    if calleeSaved.contains r then
      let s := st.get r
      st.set r { slot := s.slot, modified := s.slot != some d }
    else st
  | .regular _ _ (.mov (.mem a) (.regOrMem (.reg (.low r .W64)))) =>
    match slotDisp? a with
    | some k =>
      if calleeSaved.contains r then
        let s := st.get r
        if !s.modified && s.slot.isNone then st.set r { slot := some (d + k), modified := false } else st
      else e.writes.foldl (fun st w => if calleeSaved.contains w then st.set w { (st.get w) with modified := true } else st) st
    | none => e.writes.foldl (fun st w => if calleeSaved.contains w then st.set w { (st.get w) with modified := true } else st) st
  | .regular _ _ (.mov (.reg (.low r .W64)) (.regOrMem (.mem a))) =>
    match slotDisp? a with
    | some k =>
      if calleeSaved.contains r then
        let s := st.get r
        st.set r { slot := s.slot, modified := s.slot != some (d + k) }
      else st
    | none => e.writes.foldl (fun st w => if calleeSaved.contains w then st.set w { (st.get w) with modified := true } else st) st
  | _ => e.writes.foldl (fun st w => if calleeSaved.contains w then st.set w { (st.get w) with modified := true } else st) st

/-- One block from its start: the depth and state at its end, the edges `(target block, depth, state)` of its
jumps, the largest `-a` of its stack accesses. -/
def runBlock (g : Cfg) (b : Nat) (d0 : Int) (st0 : SavedState) :
    R (Int × SavedState × List (Nat × Int × SavedState) × Nat × Bool) := do
  let blk := g.blocks[b]!
  let own := g.blocks.toList.map (·.label)
  let mut d := d0
  let mut st := st0
  let mut edges := []
  let mut bytes := 0
  let mut ended := false
  for i in blk.ins do
    if ended then break
    let e ← effect i
    for (off, size) in e.acc do
      let a := d + off
      if a ≥ 0 || a + (size : Int) > 0 then
        throw s!"stack access outside the owned region: {instrText i} (offset {a})"
      bytes := max bytes (-a).toNat
    st := step d st i e
    d := d + e.delta
    bytes := max bytes (-d).toNat
    let tgt? : Option Label := match i with
      | .regular _ _ (.jcc _ t) => some t
      | .regular _ _ (.jmp t) => relLabel? t
      | _ => none
    if let some t := tgt? then
      if own.contains t then
        if let some j := g.blocks.findIdx? (·.label == t) then edges := edges ++ [(j, d, st)]
    if instrEnds i then ended := true
  if !ended then
    if b + 1 < g.blocks.size then edges := edges ++ [(b + 1, d, st)]
  return (d, st, edges, bytes, ended)

/-- The frame of the function: a fixpoint over the blocks that the entry reaches. -/
def Frame.analyse (g : Cfg) : R Frame := do
  let n := g.blocks.size
  let mut starts : Array (Option (Int × SavedState)) := Array.replicate n none
  starts := starts.set! 0 (some (0, SavedState.init))
  let mut work := [0]
  let mut fuel := 100 * n * n + 100
  while !work.isEmpty && fuel > 0 do
    fuel := fuel - 1
    let b :: rest := work | break
    work := rest
    let some (d0, st0) := starts[b]! | continue
    let (_, _, edges, _, _) ← runBlock g b d0 st0
    for (s, d, st) in edges do
      match starts[s]! with
      | none =>
        starts := starts.set! s (some (d, st))
        work := s :: work
      | some (d', st') =>
        if d' != d then throw s!"the stack pointer differs at a join (block {g.nameOf s})"
        let j := SavedState.join st' st
        if j != st' then
          starts := starts.set! s (some (d', j))
          work := s :: work
  let mut bytes := 0
  let mut labels := []
  for b in [0:n] do
    let some (d0, st0) := starts[b]! | continue
    let (d, _, _, k, _) ← runBlock g b d0 st0
    bytes := max bytes (max k (-d).toNat)
    bytes := max bytes (-d0).toNat
    labels := labels ++ [(g.nameOf b, { delta := d0, state := st0 : LabelFrame })]
  return { n := bytes, labels }

/-- Does the code use the stack: an instruction with the stack pointer, a push, a pop or a `leave`? -/
def usesStack (g : Cfg) : Bool :=
  g.blocks.any fun b => b.ins.any fun i => match i with
    | .regular _ _ (.push _) | .regular _ _ (.pop _) | .regular _ _ .leave => true
    | .regular _ _ op => (opdsOf op).1.any fun | .reg .rsp => true | .mem a _ => isRspBase a || a.idx.any (·.reg == .rsp) | _ => false
    | _ => false

/-! ### The segments between cut points -/

/-- What a segment needs of the frame relation (`P2/scripts/segclass.py`): `plain` (loads, register code and stack accesses),
`ptrstore` (an 8-byte store to the heap), `subword` (a store of 1, 2 or 4 bytes to the heap), `call`. -/
inductive SegClass | plain | ptrstore | subword | call
  deriving BEq, Repr

/-- The class of the segment that starts at block `start` and goes to the blocks of `cuts` or to a return. -/
def Cfg.segClass (g : Cfg) (cuts : List Nat) (start : Nat) : SegClass := Id.run do
  let mut seen : List Nat := []
  let mut todo := [start]
  let mut call := false
  let mut sub := false
  let mut ptr := false
  for _ in [0:g.blocks.size * 2 + 2] do
    match todo with
    | [] => break
    | b :: rest =>
      todo := rest
      unless seen.contains b do
        seen := b :: seen
        for i in g.blocks[b]!.ins do
          match i with
          | .regular _ _ (.call _) => call := true
          | .regular _ _ op =>
            match memStoreOf op with
            | some (a, bytes) =>
              if !isRspBase a then
                if bytes == 8 then ptr := true else sub := true
            | none => pure ()
          | .avx .. => pure ()
        todo := ((g.succ[b]?.getD []).filter (!cuts.contains ·)) ++ todo
  return if call then .call else if sub then .subword else if ptr then .ptrstore else .plain

end Lift.P2.Gen
