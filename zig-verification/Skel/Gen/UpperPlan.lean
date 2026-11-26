import Skel.Gen.Upper
import Skel.Gen.Shape
import Skel.Gen.Hint
import Skel.Gen.Model
import Skel.Gen.HeadTerm

/-! The plan computation of the upper generator (`docs/one-way-lift-g3-plan-20261118.md`, sections 4.2 to 4.7, 5.2 and
5.3; task G3-06). `upperPlan` is pure and total: it gives the plan of a function, or the first error.

Two rules differ from the text of the plan:
- a loop head is the target of a back edge: a block that jumps to it, and that it dominates. The reachability rule of 4.6
  also takes the blocks of the cycle (`toyFind` would get `LBB2_1`, `o10` and `o16`);
- the result kind (4.4): the value part comes from the hint record, not from the statement (`#stmt_shape` prints `post` as a
  name), and the heap part comes from the stores of the code (`Vars.mem`) and the mutable pointers of the hint.

The fixed head analysis follows straight entry paths and known earlier heads (`knownHead`). A push and its pop on the way
give the pushed value (`straightRegs`). A head whose fixed state needs a branch, a later load, a carried value, or an
unsupported expression is generalized: every state register is explicit and carried. Region VCs establish its entry relation. -/

namespace Skel.Gen

/-! ## The blocks as a graph (4.6) -/

/-- The offsets that an exit jumps to. A return and a trap go nowhere. A call goes to its continuation, as in `Vars`. -/
def exitTargets : Exit → List Nat
  | .goto t => [t]
  | .call _ c => [c]
  | .ret | .trap => []

/-- The offsets that a block jumps to. -/
def successors (b : Block) : List Nat :=
  match b.term with
  | .exit e => exitTargets e
  | .branch _ y n => exitTargets y ++ exitTargets n

/-- The block at the offset `o`, if there is one. -/
def blockAt (bs : List Block) (o : Nat) : Option Block := bs.find? (·.offset == o)

/-- The offsets reached from `start` without entering the offset `avoid`. The search takes at most `2 * bs.length + 1`
steps: each offset is marked once, and a marked offset with a block adds at most two offsets to the stack. -/
def reachFrom (bs : List Block) (avoid : Option Nat) (start : Nat) : List Nat :=
  go (2 * bs.length + 1) [start] []
where
  go : Nat → List Nat → List Nat → List Nat
  | 0, _, seen => seen
  | _ + 1, [], seen => seen
  | fuel + 1, o :: stack, seen =>
    if seen.contains o || avoid == some o then go fuel stack seen
    else go fuel (stack ++ ((blockAt bs o).map successors).getD []) (o :: seen)

/-- `b` jumps to the offset `h`, and `h` dominates `b`: each path from the entry (offset 0) to `b` passes `h`. Such an
edge is a back edge, and `h` is a loop head. -/
def isBackEdge (bs : List Block) (h : Nat) (b : Block) : Bool :=
  (successors b).contains h && (reachFrom bs none 0).contains b.offset && !(reachFrom bs (some h) 0).contains b.offset

/-- The loop heads, in the order of `bs`: the blocks that are the target of a back edge (4.6). -/
def loopHeads (bs : List Block) : List Block :=
  bs.filter fun h => bs.any (isBackEdge bs h.offset)

/-- The offsets of the blocks on a cycle through the offset `h`: the blocks reached from `h` that reach `h` (5.3). -/
def cycleOf (bs : List Block) (h : Nat) : List Nat :=
  (reachFrom bs none h).filter fun o => (blockAt bs o).isSome && (reachFrom bs none o).contains h

/-! ## The head state (4.2, 4.6) -/

mutual
/-- A value with each register replaced by its value in `env`. -/
def substVal (env : Reg64 → Val) : Val → Val
  | .reg r => env r
  | .lit n => .lit n
  | .load k => .load k
  | .retAddr o => .retAddr o
  | .add a b => .add (substVal env a) (substVal env b)
  | .sub a b => .sub (substVal env a) (substVal env b)
  | .mul a b => .mul (substVal env a) (substVal env b)
  | .shr a k => .shr (substVal env a) k
  | .zext32 a => .zext32 (substVal env a)
  | .and a b => .and (substVal env a) (substVal env b)
  | .or a b => .or (substVal env a) (substVal env b)
  | .xor a b => .xor (substVal env a) (substVal env b)
  | .not a => .not (substVal env a)
  | .neg a => .neg (substVal env a)
  | .shl a k => .shl (substVal env a) k
  | .extract lo len a h => .extract lo len (substVal env a) h
  | .zext w a => .zext w (substVal env a)
  | .sext w a => .sext w (substVal env a)
  | .replaceLow w a b => .replaceLow w (substVal env a) (substVal env b)
  | .setcc c => .setcc (substCond env c)
  | .ite c a b => .ite (substCond env c) (substVal env a) (substVal env b)

/-- A condition with each register replaced by its value in `env`. `env` has no flag values: a flag input stays the
flag of the block start. -/
def substCond (env : Reg64 → Val) : Cond → Cond
  | .eq a b => .eq (substVal env a) (substVal env b)
  | .ule a b => .ule (substVal env a) (substVal env b)
  | .ult a b => .ult (substVal env a) (substVal env b)
  | .slt a b => .slt (substVal env a) (substVal env b)
  | .slt32 a b => .slt32 (substVal env a) (substVal env b)
  | .not c => .not (substCond env c)
  | .iff p q => .iff (substCond env p) (substCond env q)
  | .flag f => .flag f
end

/-- The register values after the block `b`, in terms of the entry. A register that `b` writes takes its new value; the
other registers keep theirs. -/
def stepEnv (env : Reg64 → Val) (b : Block) : Reg64 → Val :=
  fun r => match b.regs.find? (·.1 == r) with
    | some (_, v) => substVal env v
    | none => env r

/-- The value of the pop `k` of the block `b`: the value of the latest store of `b` before it to the same stack word (a push
and its pop, `pushq $-1; popq %rax`), as the L2⁺ model reads it (`pushedVal`, rule 4.3.4). The addresses of one block have
the same base `rsp`, so the depth from the block start decides the word. -/
def poppedVal (b : Block) (k : Nat) : Option Val :=
  let c : Ctx := ⟨⟨[], [], false⟩, "", b.accesses, 0⟩
  let i := b.accesses.findIdx fun | .load k' _ _ => k' == k | .store .. => false
  match b.accesses[i]? with
  | some (.load _ addr _) =>
    if addr.usesRsp then (depthOf 0 addr).bind (pushedVal c (b.accesses.take i)) else none
  | _ => none

mutual
/-- The value has no load. -/
def loadFree : Val → Bool
  | .load _ => false
  | .reg _ | .lit _ | .retAddr _ => true
  | .add a b | .sub a b | .mul a b | .and a b | .or a b | .xor a b | .replaceLow _ a b => loadFree a && loadFree b
  | .shr a _ | .zext32 a | .not a | .neg a | .shl a _ | .extract _ _ a _ | .zext _ a | .sext _ a => loadFree a
  | .setcc c => loadFreeCond c
  | .ite c a b => loadFreeCond c && loadFree a && loadFree b

/-- The condition has no load. -/
def loadFreeCond : Cond → Bool
  | .eq a b | .ule a b | .ult a b | .slt a b | .slt32 a b => loadFree a && loadFree b
  | .not c => loadFreeCond c
  | .iff p q => loadFreeCond p && loadFreeCond q
  | .flag _ => true
end

/-- The register updates of a block on a straight path to a head: the list of the block when it has no access; when each
access is a stack word, a register that a pop sets takes the pushed value (`poppedVal`). An access of the memory, a pop
with no push in the block, or a value with a load that is no pop (a load of this block, which `headVal` would read as a load
of the entry block), gives none. -/
def straightRegs (b : Block) : Option (List (Reg64 × Val)) :=
  if b.accesses.all (fun | .load _ a _ | .store _ a _ _ => a.usesRsp) then do
    let regs ← b.regs.mapM fun (r, v) => match v with
      | .load k => (poppedVal b k).map (r, ·)
      | v => some (r, v)
    if regs.all (loadFree ·.2) then some regs else none
  else none

/-- The register values at the offset `o`, from the entry, along `goto` exits only, until the head `h`. A straight path
visits at most `bs.length` blocks; `fuel` bounds the walk. An access other than a push and its pop (`straightRegs`), a
branch, a call or a return on the way is an error, as is a missing block. -/
def walkFrom (bs : List Block) (h : Block) : Nat → Nat → (Reg64 → Val) → Except GenError (Reg64 → Val)
  | 0, _, _ => .error (.shape h.offset s!"no straight path from the entry to {h.name.s}")
  | fuel + 1, o, env =>
    if o == h.offset then .ok env
    else match blockAt bs o with
      | none => .error (.shape h.offset s!"no block at offset {o} on the way to {h.name.s}")
      | some b =>
        -- the entry block can load (PIL-HEAP): its loads are values of the entry (`headVal`); a later block can only push and
        -- pop (L2-LOOPS: `straightRegs` gives a pop its pushed value)
        match (if b.offset == 0 then some b.regs else straightRegs b) with
        | none => .error (.shape h.offset s!"{b.name.s} has an access on the way to {h.name.s}")
        | some regs =>
          match b.term with
          | .exit (.goto t) => walkFrom bs h fuel t (stepEnv env { b with regs := regs })
          | _ => .error (.shape h.offset s!"{b.name.s} has a branch, call or return on the way to {h.name.s}")

/-- The value is an operation of the arithmetic of `UInt64` on registers other than `rsp` and constants (no load). -/
private def arith : Val → Bool
  | .reg r => r != .rsp
  | .lit _ => true
  | .add a b | .sub a b | .mul a b | .and a b | .or a b | .xor a b => arith a && arith b
  | .not a | .neg a => arith a
  | _ => false

/-- The address is a register plus or minus constants. -/
private def regPlusConst : Val → Bool
  | .reg _ => true
  | .add a (.lit _) | .sub a (.lit _) => regPlusConst a
  | _ => false

mutual
/-- The registers that a value reads. -/
def readsOfVal : Val → List Reg64
  | .reg r => [r]
  | .lit _ | .load _ | .retAddr _ => []
  | .add a b | .sub a b | .mul a b => readsOfVal a ++ readsOfVal b
  | .and a b | .or a b | .xor a b | .replaceLow _ a b => readsOfVal a ++ readsOfVal b
  | .shr a _ | .zext32 a | .not a | .neg a | .shl a _ | .extract _ _ a _ | .zext _ a | .sext _ a => readsOfVal a
  | .setcc c => readsOfCond c
  | .ite c a b => readsOfCond c ++ readsOfVal a ++ readsOfVal b

/-- The registers that a condition reads. -/
def readsOfCond : Cond → List Reg64
  | .eq a b | .ule a b | .ult a b | .slt a b | .slt32 a b => readsOfVal a ++ readsOfVal b
  | .not c => readsOfCond c
  | .iff p q => readsOfCond p ++ readsOfCond q
  | .flag _ => []
end

/-- The head value of the state register `r` (4.6), from its value `v` at the head: an input register, a literal, `0` for a
state register that is no input (`init`, 4.2), `carried` for a register of `carried` (the registers that a loop before the head
writes, L2-LOOPS), or a term of the inputs (`term`: arithmetic of input registers and constants, PIL-HEAP and L2-LOOPS). A load
`k` of the entry block (`entry`, PIL-HEAP) is a load of the heap through a register (`HeadVal.load`), or a pop of the latest
push of the entry block to its word (`pushedVal`), whose value is then the head value. Any other value is an error. The fuel
bounds the pops of pushed loads (one per access). -/
def headVal (inputs state carried : List Reg64) (entry : List Access) (h : Block) (r : Reg64) :
    Nat → Val → Except GenError HeadVal
  | _, .lit n => .ok (.lit n)
  | _, .reg s =>
    if carried.contains s then .ok .carried
    else if inputs.contains s then .ok (.input s)
    else if state.contains s then .ok (.lit 0)
    else .error (.shape h.offset s!"the head {h.name.s} reads {regName s}, which is no field")
  | fuel + 1, .load k =>
    let i := (entry.findIdx? fun | .load k' .. => k' == k | .store .. => false).getD entry.length
    match entry[i]? with
    | some (.load _ addr w) =>
      if !addr.usesRsp then
        if !regPlusConst addr then
          .error (.shape h.offset s!"the head {h.name.s} sets {regName r} to a load at an address that is not a register plus a constant")
        else
          let c : Ctx := ⟨⟨inputs, [], false⟩, "", entry, 0⟩
          .ok (.load (bvText c addr).1 w)
      else match depthOf 0 addr with
        | some d =>
          match pushedVal ⟨⟨inputs, [], false⟩, "", entry, 0⟩ (entry.take i) d with
          | some v => if w == .W64 then headVal inputs state carried entry h r fuel v
            else .error (.shape h.offset s!"the head {h.name.s} sets {regName r} to a stack load below 8 bytes")
          | none => .error (.shape h.offset s!"the head {h.name.s} sets {regName r} to a stack load that no push of the entry gives")
        | none => .error (.shape h.offset s!"the head {h.name.s} sets {regName r} to a stack load")
    | _ => .error (.shape h.offset s!"the head {h.name.s} sets {regName r} to the load {k}, which the entry block does not have")
  | _, v =>
    if (readsOfVal v).any carried.contains then
      .error (.shape h.offset s!"the head {h.name.s} sets {regName r} to a value of a register that a loop before it writes")
    else if arith v && (readsOfVal v).all inputs.contains then .ok (.term (u64Text ⟨⟨inputs, [], false⟩, "", entry, 0⟩ v).1)
    -- MAP-HEAD: a term of the inputs and the loads of the entry block (`headTerm`; the `r15` of `mapInPlace`)
    else match headTerm inputs entry v with
      | .ok t => .ok (.term t)
      | .error why => .error (.shape h.offset s!"the head {h.name.s} sets {regName r} to a value that is not a register, a literal or a term of the inputs, and no load of the entry block ({why})")

/-- The registers that the blocks at the offsets `offs` write. -/
def writtenIn (bs : List Block) (offs : List Nat) : List Reg64 :=
  (bs.filter fun b => offs.contains b.offset).flatMap fun b => b.regs.map (·.1)

/-- A head that is known: its block, its register values at the head (in terms of the entry, as `walkFrom` gives them), and
the registers that are `carried` at it. -/
structure KnownHead where
  (block : Block) (env : Reg64 → Val) (carried : List Reg64)

/-- The starts of a walk to the head `h` from the known head `g` (L2-LOOPS): for a head after the loop of `g` (a sequence),
the targets of the exits of the cycle of `g` that leave it; for a head on the cycle of `g` (an inner loop), the targets of `g`
on its cycle. -/
def startsFrom (bs : List Block) (g : Block) (h : Block) : List Nat :=
  let cyc := cycleOf bs g.offset
  if cyc.contains h.offset then (successors g).filter cyc.contains
  else ((bs.filter fun b => cyc.contains b.offset).flatMap successors).filter (!cyc.contains ·)

/-- The register values at the head `h` from the known head `g`, and the carried registers: the registers that the cycle of
`g` writes, and those carried at `g`, are carried (`Val.reg r` stands for the carried value of `r`); the others have their value
at `g`. A value at `g` of another register that is carried, or no straight path from a start (`startsFrom`), is an error. -/
def walkAfter (s : Summary) (g : KnownHead) (h : Block) : Except GenError ((Reg64 → Val) × List Reg64) := do
  let carried := (writtenIn s.blocks (cycleOf s.blocks g.block.offset) ++ g.carried).eraseDups
  let env0 : Reg64 → Val := fun r => if carried.contains r then .reg r else g.env r
  if let some r := s.vars.state.find? fun r => !carried.contains r && (readsOfVal (g.env r)).any carried.contains then
    throw (.shape h.offset s!"the head {h.name.s}: {regName r} at {g.block.name.s} reads a register that its loop writes")
  let walks := (startsFrom s.blocks g.block h).map fun o => walkFrom s.blocks h (s.blocks.length + 1) o env0
  match walks.find? (·.toBool) with
  | some (.ok env) => pure (env, carried)
  | _ => throw (.shape h.offset s!"no straight path from {g.block.name.s} to {h.name.s}")

/-- The state of the head `h` from its register values and carried registers. A load in a value is a load of the entry
block (`walkFrom`, `straightRegs`). -/
def stateOf (s : Summary) (h : Block) (env : Reg64 → Val) (carried : List Reg64) :
    Except GenError (List (Reg64 × HeadVal)) :=
  let entry := ((s.blocks.find? (·.offset == 0)).map (·.accesses)).getD []
  s.vars.state.mapM fun r => do
    return (r, ← headVal s.vars.inputs s.vars.state carried entry h r (entry.length + 1) (env r))

/-- The known head of the block `h` (4.6): from the entry on a straight path, else after a known head `g` (`walkAfter`,
L2-LOOPS). The error is the one of the walk from the entry when no known head gives a walk. -/
def knownHead (s : Summary) (known : List KnownHead) (h : Block) : Except GenError KnownHead :=
  match walkFrom s.blocks h (s.blocks.length + 1) 0 Val.reg with
  | .ok env => .ok ⟨h, env, []⟩
  | .error e =>
    match (known.map fun g => walkAfter s g h).find? (·.toBool) with
    | some (.ok (env, carried)) => .ok ⟨h, env, carried⟩
    | _ => .error e

/-- The head state of the block `h` from the entry: one value for each state register, in the order of the state (4.6). -/
def headState (s : Summary) (h : Block) : Except GenError (List (Reg64 × HeadVal)) := do
  let k ← knownHead s [] h
  stateOf s h k.env k.carried

/-- A head with arbitrary state. Each state register is explicit; region VCs supply its entry relation. -/
private def generalizedHead (s : Summary) (h : Block) : Head :=
  { name := h.name, state := s.vars.state.map (fun r => (r, .carried)),
    cycle := (cycleOf s.blocks h.offset).length, generalized := true }

/-- A fixed head when the entry gives each value without a carried field. Otherwise retain an arbitrary head state.
An arbitrary head does not provide an environment for later fixed heads. -/
private def resolveHead (s : Summary) (known : List KnownHead) (h : Block) : Option KnownHead × Head :=
  match knownHead s known h with
  | .ok k =>
    match stateOf s h k.env k.carried with
    | .ok st =>
      if st.any (·.2 == .carried) then (none, generalizedHead s h)
      else (some k, { name := h.name, state := st, cycle := (cycleOf s.blocks h.offset).length })
    | .error _ => (none, generalizedHead s h)
  | .error _ => (none, generalizedHead s h)

/-- The heads of the blocks `hs`, in order. Fixed entry values retain the original loop-row form.
A branch, a later load, a carried value, or an unsupported fixed expression gives a generalized head. -/
def headsOf (s : Summary) (hs : List Block) : Except GenError (List Head) :=
  let (_, heads) := hs.foldl (init := (([] : List KnownHead), ([] : List Head))) fun (known, heads) h =>
    let (k, hd) := resolveHead s known h
    (known ++ k.toList, heads ++ [hd])
  .ok heads

/-- The head of the block `h` from the entry, with generalized state when fixed values are unavailable. -/
def headOf (s : Summary) (h : Block) : Except GenError Head := do
  return (resolveHead s [] h).2

/-! ## The classes of the state registers (5.2) -/


/-- The registers that a terminator reads. -/
def readsOfTerm : Term → List Reg64
  | .exit _ => []
  | .branch c _ _ => readsOfCond c

/-- The base registers of an address: the registers that it adds, outside any product. -/
def baseRegs : Val → List Reg64
  | .reg r => [r]
  | .add a b => baseRegs a ++ baseRegs b
  | .zext32 a => baseRegs a
  | _ => []

/-- The scaled registers of an address: the registers under a product. -/
def scaledRegs : Val → List Reg64
  | .mul a b => readsOfVal a ++ readsOfVal b
  | .add a b => scaledRegs a ++ scaledRegs b
  | .zext32 a | .shr a _ => scaledRegs a
  | _ => []

/-- The address of an access. -/
def addrOf : Access → Val
  | .load _ a _ => a
  | .store _ a _ _ => a

/-- The class of the state register `r` (5.2): a pointer when it is the base of an access address, else a counter when it
is a scaled index or a branch operand, else an accumulator. A register of two classes has the first one. -/
def classOf (bs : List Block) (r : Reg64) : FieldClass :=
  let addrs := bs.flatMap fun b => b.accesses.map addrOf
  let bases := addrs.flatMap baseRegs
  let counters := addrs.flatMap scaledRegs ++ bs.flatMap fun b => readsOfTerm b.term
  if bases.contains r then .pointer
  else if counters.contains r then .counter
  else .accumulator

/-! ## The chain ghosts (4.7) -/

/-- The address of the load with the index `k` in the block `b`. -/
def loadAddr (b : Block) (k : Nat) : Option Val :=
  (b.accesses.find? fun a => match a with
    | .load k' _ _ => k' == k
    | .store .. => false).map addrOf

/-- The chain offset of an address from the register `r`: the address is `r` (offset 0) or `r + c` (offset `c`). -/
def chainOffset (r : Reg64) : Val → Option Nat
  | .reg s => if s == r then some 0 else none
  | .add (.reg s) (.lit c) => if s == r then some c.toNat else none
  | _ => none

/-- The chain ghost of a register write of the block `b`: a state register `r` that the block sets to a load from `r + c`. -/
def ghostOf (state : List Reg64) (b : Block) : Reg64 × Val → Option Ghost
  | (r, .load k) => do
    guard (state.contains r)
    let a ← loadAddr b k
    let c ← chainOffset r a
    return ⟨r, c⟩
  | _ => none

/-- The ghosts with each one named once. Two offsets for one register are an error: the ghost is named `rest_<reg>`. -/
def checkGhosts (gs : List Ghost) : Except GenError (List Ghost) :=
  let named := gs.eraseDups
  match named.find? (fun g => named.any fun h => h.reg == g.reg && h.off != g.off) with
  | some g => .error (.shape 0 s!"two chain offsets for {regName g.reg}")
  | none => .ok named

/-! ## The statement (4.2, 4.4, 4.5) -/

/-- The type of a fixed statement parameter. Known address forms retain their sampler classification. -/
def binderTy (t : String) : Option BinderTy :=
  match t.trimAscii.toString with
  | "BitVec 64" => some .addr
  | "List (BitVec 64)" => some .addrs
  | t => BinderTy.source <$> Src.parse t

/-- A binder of the statement as a parameter of `l3` (4.5). -/
def binderOf (b : ShapeBinder) : Except GenError Binder :=
  match binderTy b.type.s with
  | some t => .ok ⟨b.name, t⟩
  | none => .error (.shape 0 s!"binder {b.name.s} has a blank type")

/-- The result kind (4.4), from the hint record and the store fact `mem` of the code (`Vars.mem`: a block stores through a
register). An integer, a `bool`, an enum, or an error union with a void payload (the error code: 0 is `ok`) is a value result
(4.9: a `u64` or `void` result); an error union with a payload is not, since its payload is a second result. A function that
writes the memory is a heap, since the draft (4.9) writes the memory as `Mem.has … true`. It writes when it stores (`mem`:
`SpillSet.add` stores through a const pointer to a record) or when a pointer parameter is mutable (the writes of a callee are
not in `mem`: `MappingBuilder.mapInPlace` calls `map`). A record field alone is no write: a mutable field behind a const
pointer gives no heap (`MappingBuilder.closestCopy`, `Emission.shallowestCopyPosition`). Neither gives no kind. The record is
untrusted: a wrong kind gives a failed row, not an accepted theorem. -/
def resultKindOf (mem : Bool) (h : HintRecord) : Except GenError ResultKind :=
  let value := match h.ret.bind (fun i => h.types[i]?) with
    | some (.int _ _) | some .bool | some (.enum _ _) => true
    | some (.errUnion payload _ _ _) => h.types[payload]? == some (.other 0)
    | _ => false
  let heap := mem || h.params.any fun p => match h.types[p.ty]? with
    | some (.ptr _ _ (some true) _) => true
    | _ => false
  match value, heap with
  | true, true => .ok .both
  | true, false => .ok .value
  | false, true => .ok .heap
  | false, false => .error (.shape 0 "no result kind: the hint has no integer, bool, enum or error code result and no mutable pointer")

/-! ## The L3 value of a value result -/

/-- The L3 value of a value result (`ValueTy`), from the width `ret` of the statement (`fn.ret`) and the result type of the
hint. The width is the one of the statement: the hint must give the same number of bits (8 for a `bool`, the width of the code
for an error union), else the result is an error. An enum uses the bits of its ABI tag; the statement's post gives their meaning.
A result with no value type in the hint (a heap) has the
width of the statement; no text reads it. -/
def valueTyOf (h : HintRecord) (ret : Width) : Except GenError ValueTy :=
  let differ (what : String) (bits : Nat) : GenError :=
    .shape 0 s!"fn.ret is {ret.bits} bits, the hint result ({what}) has {bits} bits"
  match h.ret.bind (fun i => h.types[i]?) with
  | some .bool => if ret == .W8 then .ok .bool else .error (differ "bool" 8)
  | some (.errUnion _ code _ _) => if code == ret then .ok (.bits ret) else .error (differ "error code" code.bits)
  | some (.int bits _) => if bits == ret.bits then .ok (.bits ret) else .error (differ "integer" bits)
  | some (.enum tag _) =>
    if tag != ret then .error (differ "enum tag" tag.bits)
    else .ok (.bits ret)
  | _ => .ok (.bits ret)

/-! ## The hint against the statement and the code (R-F) -/

/-- The registers of the arguments of a call, in order (the C ABI). -/
private def abiArgRegs : List Reg64 := [.rdi, .rsi, .rdx, .rcx, .r8, .r9]

/-- A pointer parameter of the hint: the parameter, its mutability (`none` when the hint does not say), and whether it
addresses scalars (an integer, a `bool` or an enum), so that no other pointer is behind it. -/
private structure PtrParam where
  (param : HParam) (mutable : Option Bool) (flat : Bool)

/-- The pointer parameters of the hint. -/
private def ptrParams (h : HintRecord) : List PtrParam :=
  h.params.filterMap fun q => match h.types[q.ty]? with
    | some (HTy.ptr _ to m _) =>
      let flat := match h.types[to]? with
        | some (.int ..) | some .bool | some (.enum ..) => true
        | _ => false
      some ⟨q, m, flat⟩
    | _ => none

/-- The mutability of the pointers of the hint against the code. A function writes the memory (`mem`) exactly when it stores
through a register (`Vars`). A mutable pointer needs a store. A store needs a mutable pointer when each pointer parameter is
read-only and addresses scalars: a read-only pointer to a record can hold a pointer to a writable object (`SpillSet.add`). A
pointer with no mutability in the hint says nothing. The statement gives no permission field (`objs` is a term), so the
code is the trusted side. -/
def checkMutability (mem : Bool) (h : HintRecord) : Except GenError Unit :=
  let ptrs := ptrParams h
  match ptrs.find? (·.mutable == some true) with
  | some p =>
    if mem then .ok () else .error (.shape 0 s!"hint parameter {p.param.name} is mutable, the code does not write the memory")
  | none =>
    match ptrs.head? with
    | some p =>
      if mem && ptrs.all (fun q => q.flat && q.mutable == some false) then
        .error (.shape 0 s!"hint parameter {p.param.name} is not mutable, the code writes the memory")
      else .ok ()
    | none => .ok ()

/-- Whether the argument `a` of the statement is a natural number: the form `nat` (`BitVec.ofNat 64 t`, `Skel/Lean/Shape.lean`
reads it from the structure of the term). The words of the text of the term decide nothing: `x.keyLength` and `x.size_hint` are
not counts, and an address binder such as `p` is not. -/
private def isNat (a : ArgShape) : Bool :=
  match a.form with | .nat _ => true | .bv => false

/-- The count of the parameter `q` against the statement. Each factor is a parameter `k` of the count: `Count.param k` has
one factor, `Count.mul k l` two. A factor names a parameter that exists, has an argument register, and whose argument in
the statement is a natural number (`isNat`), not the pointer or the key. The other counts are not checked here. -/
def checkCount (sh : StmtShape) (h : HintRecord) (q : HParam) : Except GenError Unit :=
  let factor (k : Nat) : Except GenError Unit := do
    let bad (why : String) : GenError := .shape 0 s!"parameter {q.name}: {why}"
    let some c := h.params[k]? | throw (bad s!"the count is parameter {k}, the hint has no parameter {k}")
    let some r := c.regs.head? | throw (bad s!"the count is parameter {c.name}, which has no argument register")
    let some i := abiArgRegs.idxOf? r | throw (bad s!"the count is parameter {c.name}, which is in {regName r}, no argument register")
    match sh.args[i]? with
    | none => pure ()  -- a missing argument is the error of `upperPlan` (the arguments and the inputs differ)
    | some a => unless isNat a do
      throw (bad s!"the count is parameter {c.name}, whose argument {a.term.s} is not a natural number")
  match q.count with
  | .param k => factor k
  | .mul k l => do
    factor k
    factor l
  | _ => pure ()

/-- The hint against the statement and the code: the mutability of the pointers, and the count of each parameter. -/
def checkHint (mem : Bool) (sh : StmtShape) (h : HintRecord) : Except GenError Unit := do
  checkMutability mem h
  h.params.forM (checkCount sh h)

/-- The heads of the plan `p` that have a fixed loop row. Generalized heads use region VCs. -/
def rowHeads (p : UpperPlan) : List Head := p.heads.filter fun h => !h.generalized && !h.state.any (·.2 == .carried)

/-! ## The check of a plan -/

/-- The first fault of the head `h` of the plan `p`: a state register with no single value, a value for a register that is
no state register, or an input value that is no input. -/
def headFault (p : UpperPlan) (h : Head) : Option String :=
  match p.state.find? (fun e => (h.state.filter (·.1 == e.1)).length != 1) with
  | some e => some s!"head {h.name.s} has no single value for {regName e.1}"
  | none =>
    if h.state.length != p.state.length then
      some s!"head {h.name.s} has a value for a register that is no state register"
    else if h.generalized && h.state.any (·.2 != .carried) then
      some s!"generalized head {h.name.s} has a fixed state value"
    else
      h.state.findSome? (fun e => match e.2 with
        | .input r => if p.inputs.contains r then none else some s!"head {h.name.s} takes {regName r} as an input, which is not an input"
        | .lit _ | .load .. | .term _ | .carried => none)

/-- The check of a plan: each head has one value for each state register, each input value names an input,
and a generalized head has only carried values. -/
def checkPlan (p : UpperPlan) : Except GenError UpperPlan :=
  match p.heads.findSome? (headFault p) with
  | some msg => .error (.shape 0 msg)
  | none => .ok p

/-! ## The plan -/

/-- Why a stack room has no proof text for `refines_l2p` and `above_l2p` (L3-U5), or `none` when it has one. The proofs cover
a room with a value result and no memory in the state, and a room with memory in the state (PIL-CALL3): the L2 model writes the
pushes into the memory and reads the pops from it (the memory form), and the proofs step through these accesses
(`Lift/Sem/StackPush.lean`); a pop of a word that another block pushed is an error of the proof text (`UpperProof.lean`). The
model and relation texts have a room with memory: their frame clauses exclude the room (`¬ SysV.Below`), and no object meets
the room (`Fn.Entry.apart`). -/
def roomRefusal (room : Nat) (mem : Bool) (kind : ResultKind) : Option String :=
  if room == 0 || mem then none
  else if kind != .value then some s!"a stack room of {room} bytes in a function with a heap result: the upper texts cover a room with a value result and no memory"
  else none

/-! ## The inputs that are arguments (SHAPE-ARGS)

An input whose entry value reaches only bits that no read needs is no argument: `movw $1, %ax` and `setne %al` keep the high bits
of `rax`, and the statement reads the low `fn.ret` bits of `rax`. The rule, for an input `r`:
* `prune` removes from a value each part whose bits a read of its low `d` bits does not need (the old value of `replaceLow w`
  when `d ≤ w`, the high bits of an operand of a narrow read), and gives the width of each read of `r` that is left;
* a write of `r` to itself that keeps its high bits (`replaceLow w … (reg r) …`, `keepWrite`) keeps the bits from `K` up, the
  largest width of the chain; its `reg r` is no read, and the blocks `M` have `0` in its place;
* `r` is free when the blocks read it (`vars`, or a call), `M` reads no entry value of it, no call reads its entry bits, and each
  read of `r` in a block whose start entry bits can reach (`entryBitsAt`: a path from the entry
  with no full write of `r`) needs at most the low `W` bits, where `W` is the smallest `K` (64 when `r` has no such write); a
  return needs the low `fn.ret` bits of `rax`.
Then `r` in the code and in `M` agree on the low `W` bits after the first write, and on all bits after a full write, and the other
registers and the memory agree, so no read and no result sees the entry value of `r`. For ABI argument registers, a known
callee reads the registers of its interface; an unknown callee can read each argument register of the C ABI. Non-ABI model
inputs stay free at calls, as in the callee's own argument plan. A summary whose `vars` the blocks do not give has
each input as an argument. A free input stays an input of the model
(`SimArr` and `l3.rep` leave it free); the arguments are the other inputs, without the callee-saved registers. -/

mutual
/-- The value `v` with each part that its low `d` bits do not need removed, and the width of each read of `r` in it. A read of
no bit is the literal 0. -/
def prune (r : Reg64) (d : Nat) (v : Val) : Val × List Nat :=
  if d == 0 then (.lit 0, []) else
  match v with
  | .reg s => (v, if s == r then [d] else [])
  | .lit _ | .load _ | .retAddr _ => (v, [])
  | .replaceLow w old new =>
    if w == .b32 then
      let (n, ns) := prune r (min d 32) new
      (.zext .b32 n, ns)
    else if d ≤ w.bits then
      let (n, ns) := prune r d new
      (.zext w n, ns)
    else
      let (o, os) := prune r d old
      let (n, ns) := prune r w.bits new
      (.replaceLow w o n, os ++ ns)
  | .zext w a => let (x, xs) := prune r (min d w.bits) a; (.zext w x, xs)
  | .sext w a => let (x, xs) := prune r w.bits a; (.sext w x, xs)
  | .zext32 a => let (x, xs) := prune r (min d 32) a; (.zext32 x, xs)
  | .extract lo len a h => let (x, xs) := prune r (min 64 (lo + min len d)) a; (.extract lo len x h, xs)
  | .shl a k => let (x, xs) := prune r (d - k.val) a; (.shl x k, xs)
  | .shr a k => let (x, xs) := prune r (min 64 (d + k.val)) a; (.shr x k, xs)
  | .not a => let (x, xs) := prune r d a; (.not x, xs)
  | .neg a => let (x, xs) := prune r d a; (.neg x, xs)
  | .add a b => let (x, xs) := prune r d a; let (y, ys) := prune r d b; (.add x y, xs ++ ys)
  | .sub a b => let (x, xs) := prune r d a; let (y, ys) := prune r d b; (.sub x y, xs ++ ys)
  | .mul a b => let (x, xs) := prune r d a; let (y, ys) := prune r d b; (.mul x y, xs ++ ys)
  | .and a b => let (x, xs) := prune r d a; let (y, ys) := prune r d b; (.and x y, xs ++ ys)
  | .or a b => let (x, xs) := prune r d a; let (y, ys) := prune r d b; (.or x y, xs ++ ys)
  | .xor a b => let (x, xs) := prune r d a; let (y, ys) := prune r d b; (.xor x y, xs ++ ys)
  | .setcc c => let (x, xs) := pruneCond r c; (.setcc x, xs)
  | .ite c a b =>
    let (z, zs) := pruneCond r c
    let (x, xs) := prune r d a
    let (y, ys) := prune r d b
    (.ite z x y, zs ++ xs ++ ys)

/-- `prune` of the operands of a condition: all 64 bits, the low 32 bits for `slt32`. -/
def pruneCond (r : Reg64) (c : Cond) : Cond × List Nat :=
  match c with
  | .eq a b => let (x, xs) := prune r 64 a; let (y, ys) := prune r 64 b; (.eq x y, xs ++ ys)
  | .ule a b => let (x, xs) := prune r 64 a; let (y, ys) := prune r 64 b; (.ule x y, xs ++ ys)
  | .ult a b => let (x, xs) := prune r 64 a; let (y, ys) := prune r 64 b; (.ult x y, xs ++ ys)
  | .slt a b => let (x, xs) := prune r 64 a; let (y, ys) := prune r 64 b; (.slt x y, xs ++ ys)
  | .slt32 a b => let (x, xs) := prune r 32 a; let (y, ys) := prune r 32 b; (.slt32 x y, xs ++ ys)
  | .not p => let (x, xs) := pruneCond r p; (.not x, xs)
  | .iff p q => let (x, xs) := pruneCond r p; let (y, ys) := pruneCond r q; (.iff x y, xs ++ ys)
  | .flag f => (.flag f, [])
end

/-- A write of `r` to itself that keeps its high bits: a chain of `replaceLow` of 8 or 16 bits that ends in `reg r`. The value
with `0` for `reg r`, the width `K` from which the entry bits stay, and the widths of the reads of `r` in the new values. -/
def keepWrite (r : Reg64) : Val → Option (Val × Nat × List Nat)
  | .reg s => if s == r then some (.lit 0, 0, []) else none
  | .replaceLow w old new =>
    if w == .b32 then none else do
      let (o, k, os) ← keepWrite r old
      let (n, ns) := prune r w.bits new
      pure (.replaceLow w o n, max k w.bits, os ++ ns)
  | _ => none

/-- The pruned register write `(q, v)` of a block, for the input `r`: the value, the width `K` of a `keepWrite` of `r`, and the
widths of the reads of `r`. The value of a write is read in all 64 bits. -/
def pruneWrite (r : Reg64) (p : Reg64 × Val) : (Reg64 × Val) × Option Nat × List Nat :=
  match (if p.1 == r then keepWrite r p.2 else none) with
  | some (v, k, ws) => ((p.1, v), some k, ws)
  | none => let (v, ws) := prune r 64 p.2; ((p.1, v), none, ws)

/-- The pruned block `b` for the input `r`, the widths `K` of its `keepWrite`s, and the widths of its reads of `r`: in the
addresses (64 bits), in the stored values (the width of the store), in the writes, in the condition and in the live flags, and
`ret` bits of `rax` at a return when the block does not write `rax` or keeps its bits from `K > ret` up. -/
def pruneBlock (r : Reg64) (ret : Nat) (b : Block) : Block × List Nat × List Nat :=
  let accs := b.accesses.map fun
    | .load k a w => let (x, xs) := prune r 64 a; (Access.load k x w, xs)
    | .store k a w v => let (x, xs) := prune r 64 a; let (y, ys) := prune r w.bits v; (Access.store k x w y, xs ++ ys)
  let writes := b.regs.map (pruneWrite r)
  let (term, ts) : Term × List Nat := match b.term with
    | .branch c y n => let (x, xs) := pruneCond r c; (.branch x y n, xs)
    | t => (t, [])
  let fs := b.flags.flatMap fun (_, c) => (pruneCond r c).2
  let result :=
    if r == .rax && (exitsOfTerm b.term).any (· matches .ret) then
      match (b.regs.zip writes).find? (·.1.1 == .rax) with
      | none => [ret]
      | some (_, (_, some k, _)) => if ret ≤ k then [] else [ret]
      | some (_, (_, none, _)) => []
    else []
  ({ b with accesses := accs.map (·.1), regs := writes.map (·.1), term },
   writes.filterMap (·.2.1),
   accs.flatMap (·.2) ++ writes.flatMap (·.2.2) ++ ts ++ fs ++ result)

/-- The block `b` writes all bits of `r`: a write of `r` that is no `keepWrite`. -/
def fullWrite (r : Reg64) (b : Block) : Bool :=
  b.regs.any fun (q, v) => q == r && (keepWrite r v).isNone

/-- The offsets of the blocks at whose start `r` can hold entry bits: the blocks that a path from the entry reaches with no
`fullWrite` of `r` before them. The search marks each offset once, as `reachFrom`. -/
def entryBitsAt (bs : List Block) (r : Reg64) : List Nat :=
  go (2 * bs.length + 1) [0] []
where
  go : Nat → List Nat → List Nat → List Nat
  | 0, _, seen => seen
  | _ + 1, [], seen => seen
  | fuel + 1, o :: stack, seen =>
    if seen.contains o then go fuel stack seen
    else match blockAt bs o with
      | some b => go fuel (if fullWrite r b then stack else stack ++ successors b) (o :: seen)
      | none => go fuel stack (o :: seen)

/-- A call reads the ABI argument register `r` while its entry bits can reach it. Model-only inputs of a callee are not ABI
arguments. A full write in the call block removes entry bits. -/
private def callUsesEntry (bs : List Block) (callees : List Callee) (r : Reg64) : Bool :=
  let kept := entryBitsAt bs r
  abiArgRegs.contains r && bs.any fun b => kept.contains b.offset && !fullWrite r b && (exitsOfTerm b.term).any fun
    | .call name _ => match callees.find? (·.name == name) with
      | some c => c.inputs.contains r
      | none => abiArgRegs.contains r
    | _ => false

/-- The input `r` is free when neither a block nor a call observes its entry bits. -/
def freeInput (bs : List Block) (ret : Nat) (r : Reg64) (callees : List Callee := []) : Bool :=
  let ps := bs.map (pruneBlock r ret)
  let w := (ps.flatMap (·.2.1)).foldl min 64
  let kept := entryBitsAt bs r
  let calls := bs.any fun b => (exitsOfTerm b.term).any (· matches .call ..)
  !callUsesEntry bs callees r && ((vars bs).inputs.contains r || calls) && !(vars (ps.map (·.1))).inputs.contains r &&
    (bs.zip ps).all fun (b, p) => !kept.contains b.offset || p.2.2.all (· ≤ w)

private inductive StackByteStep where
  | read | killed | next


mutual
private def usesLoad (k : Nat) : Val → Bool
  | .load j => k == j
  | .reg _ | .lit _ | .retAddr _ => false
  | .add a b | .sub a b | .mul a b | .and a b | .or a b | .xor a b | .replaceLow _ a b => usesLoad k a || usesLoad k b
  | .shr a _ | .zext32 a | .not a | .neg a | .shl a _ | .extract _ _ a _ | .zext _ a | .sext _ a => usesLoad k a
  | .setcc c => condUsesLoad k c
  | .ite c a b => condUsesLoad k c || usesLoad k a || usesLoad k b

private def condUsesLoad (k : Nat) : Cond → Bool
  | .eq a b | .ule a b | .ult a b | .slt a b | .slt32 a b => usesLoad k a || usesLoad k b
  | .not c => condUsesLoad k c
  | .iff p q => condUsesLoad k p || condUsesLoad k q
  | .flag _ => false
end

/-- A load is used in an access, a branch, a flag, or a register that an exit needs. -/
private def loadUsed (needed : List Reg64) (b : Block) (k : Nat) : Bool :=
  b.accesses.any (fun
    | .load _ addr _ => usesLoad k addr
    | .store _ addr _ value => usesLoad k addr || usesLoad k value) ||
  b.regs.any (fun (r, v) => needed.contains r && usesLoad k v) ||
  b.flags.any (fun (_, c) => condUsesLoad k c) ||
  match b.term with | .branch c _ _ => condUsesLoad k c | _ => false

/-- The access meets one byte of a private stack store. Unknown stack addresses give no answer. -/
private def stackByteAt (s : Summary) (b : Block) (byte : Int) (addr : Val) (w : Width) : Option Bool := do
  if !addr.usesRsp then return false
  let d ← s.frame.delta.lookup b.offset
  let q ← depthOf d addr
  pure (q - (w.bits / 8 : Nat) < byte && byte ≤ q)

/-- Scan in execution order. An overwrite ends the lifetime of the stored byte. -/
private def scanStackByte (s : Summary) (live : List (Nat × List Reg64)) (b : Block) (byte : Int) : List Access → StackByteStep
  | [] => .next
  | .load k addr w :: rest =>
    if (stackByteAt s b byte addr w).getD true && loadUsed ((live.lookup b.offset).getD regOrder) b k then .read
    else scanStackByte s live b byte rest
  | .store _ addr w _ :: rest =>
    if (stackByteAt s b byte addr w).getD false then .killed else scanStackByte s live b byte rest

/-- A callee with an unknown interface or stack arguments can read the caller's stack. -/
private def callReadsStack (callees : List Callee) (b : Block) : Bool :=
  (exitsOfTerm b.term).any fun
    | .call name _ => match callees.find? (·.name == name) with
      | none => true
      | some c => c.stackArgs > 0
    | _ => false

/-- Some path reads this byte before it is overwritten. Each block is visited once for this byte. -/
private def stackByteUsed (s : Summary) (callees : List Callee) (live : List (Nat × List Reg64)) (byte : Int) (b : Block)
    (after : List Access) : Bool :=
  match scanStackByte s live b byte after with
  | .read => true
  | .killed => false
  | .next => callReadsStack callees b || go (2 * s.blocks.length + 1) (successors b) []
where
  go : Nat → List Nat → List Nat → Bool
    | _, [], _ => false
    | 0, _, _ => true
    | fuel + 1, off :: rest, seen =>
      if seen.contains off then go fuel rest seen
      else match blockAt s.blocks off with
      | none => true
      | some next =>
        match scanStackByte s live next byte next.accesses with
        | .read => true
        | .killed => go fuel rest (off :: seen)
        | .next => callReadsStack callees next || go fuel (rest ++ successors next) (off :: seen)

/-- The blocks for argument analysis, with zero for private stack stores whose bytes no path uses before an overwrite.
Unknown stack addresses and unknown callees retain the input. Models retain every store and every input. -/
def argumentBlocks (s : Summary) (callees : List Callee := []) : List Block :=
  let live := liveOutputs s.blocks callees
  s.blocks.map fun b =>
    { b with accesses := b.accesses.zipIdx |>.map fun (a, i) => match a with
      | .store k addr w v =>
        let unused := do
          let d ← s.frame.delta.lookup b.offset
          let q ← depthOf d addr
          pure (addr.usesRsp && (w.bits / 8 : Nat) ≤ q && q ≤ s.frame.room &&
            !(List.range (w.bits / 8)).any fun j =>
              stackByteUsed s callees live (q - j) b (b.accesses.drop (i + 1)))
        .store k addr w (if unused.getD false then .lit 0 else v)
      | a => a }

/-- The inputs of the summary that are arguments of the statement: the inputs that are no callee-saved register and not free
(`freeInput`). -/
def argInputsOf (s : Summary) (ret : Nat) (callees : List Callee := []) : List Reg64 :=
  let bs := argumentBlocks s callees
  let old := (vars s.blocks).inputs
  let live := (vars bs).inputs
  s.vars.inputs.filter fun r =>
    let unused := old.contains r && !live.contains r && !callUsesEntry bs callees r
    !calleeSaved.contains r && !unused && !freeInput bs ret r callees

/-- A private byte must be carried when a load cannot use a block-local store or a saved entry register.
Narrow stack accesses also use the byte state. -/
def needsPrivateStack (s : Summary) : Bool :=
  let slots := entrySlots s
  let entryRepeats := s.blocks.any fun b => (successors b).contains 0
  let localWord (c : Ctx) (prior : List Access) (depth : Int) : Option Bool :=
    prior.reverse.findSome? fun
      | .store _ addr w _ =>
        if !addr.usesRsp then none
        else match depthOf c.depth addr with
          | none => some false
          | some q =>
            if q - (w.bits / 8 : Nat) < depth && depth - 8 < q then
              some (q == depth && w == .W64)
            else none
      | _ => none
  let overwritten (depth : Int) : Bool := s.blocks.any fun b =>
    (b.offset != 0 || entryRepeats) && b.accesses.any fun
      | .store _ addr w _ =>
        addr.usesRsp && (do
          let d ← s.frame.delta.lookup b.offset
          let q ← depthOf d addr
          pure (q - (w.bits / 8 : Nat) < depth && depth - 8 < q)).getD true
      | _ => false
  s.blocks.any fun b =>
    let c : Ctx := ⟨s.vars, "", b.accesses, (s.frame.delta.lookup b.offset).getD 0⟩
    (b.accesses.foldl (fun (needed, prior) a =>
      let required := match a with
        | .store _ addr w _ => addr.usesRsp && w != .W64
        | .load _ addr w =>
          addr.usesRsp && (depthOf c.depth addr).any fun d =>
            0 < d && (w != .W64 || match localWord c prior d with
              | some whole => !whole
              | none => b.offset == 0 || !slots.any (·.1 == d) || overwritten d)
      (needed || required, prior ++ [a])) (false, [])).1

/-- The upper plan of a function (G3-06), from the summary `s`, the statement shape `sh` and the hint record `h`. Each field
follows its rule of section 4 or 5. The room of the statement (`fn.room`) is the room of the code (`s.frame.room`): the plan has
it (`UpperPlan.room`); `roomRefusal` gives the room that has no proof text. The result width (`fn.ret`) is in the plan
(`UpperPlan.val`, `valueTyOf`). The statement has one argument for each input of the summary that is an argument
(`argInputsOf`). The hint must agree with the code and the statement (`checkHint`). -/
def upperPlan (s : Summary) (sh : StmtShape) (h : HintRecord) (callees : List Callee := []) : Except GenError UpperPlan := do
  unless sh.fn.room == s.frame.room do
    throw (.shape 0 s!"fn.room is {sh.fn.room} bytes, the code uses {s.frame.room} bytes of stack room: the room of the statement and the room of the code differ")
  checkHint s.heapWrites sh h
  let kind ← resultKindOf s.heapWrites h
  -- A projected post gives the typed run result and encodes its ABI field. The generated relation checks that field at fn.ret.
  let val ← if sh.resultFn.isSome && sh.runResultType.isSome then pure (.bits sh.fn.ret)
    else valueTyOf h sh.fn.ret
  let params ← sh.binders.mapM binderOf
  let args := argInputsOf s sh.fn.ret.bits callees
  let stackArgs := stackArgCount s.frame s.blocks
  unless sh.call.stack.all (fun a => a.width == .W64) do
    throw (.shape 0 "Call8 stack arguments must have width 64")
  -- Call8 stores its stack arguments separately. Unread supplied words need no model field.
  let matchesArgs := match sh.call with
    | .call8 .. | .call8B .. => sh.args.length ≤ abiArgRegs.length &&
        args.all (fun r => (abiArgRegs.idxOf? r).any (· < sh.args.length)) &&
        stackArgs ≤ sh.call.stack.length
    | _ => sh.args.length == args.length + stackArgs
  unless matchesArgs do
    throw (.shape 0 s!"the statement has {sh.args.length} list arguments and {sh.call.stack.length} separate stack arguments, the code has {args.length} register inputs and {stackArgs} stack arguments that can reach the result ({", ".intercalate (args.map regName)}; no callee-saved register, and no register whose entry value reaches only bits that no read needs)")
  let hs := loopHeads s.blocks
  let heads ← headsOf s hs
  let privateStack := needsPrivateStack s
  let heads := if privateStack || !(stateFlags s.blocks).isEmpty then heads.map fun hd =>
      { hd with generalized := true, state := s.vars.state.map fun r => (r, .carried) }
    else heads
  let loopOffs := hs.flatMap fun hd => cycleOf s.blocks hd.offset
  let loopBlocks := s.blocks.filter fun b => loopOffs.contains b.offset
  let regional := heads.length > 1 || heads.any (·.generalized)
  let ghosts ← if regional then pure []
    else checkGhosts (loopBlocks.flatMap fun b => b.regs.filterMap (ghostOf s.vars.state b))
  checkPlan
    { fn := s.fn, inputs := s.vars.inputs, mem := s.vars.mem,
      state := s.vars.state.map fun r => (r, classOf s.blocks r),
      kind, val, params, heads, ghosts, room := s.frame.room, call := sh.call, flags := stateFlags s.blocks,
      hide := 0 < s.frame.room && !s.vars.mem && pinsInputMem s, privateStack, stackArgs }

end Skel.Gen
