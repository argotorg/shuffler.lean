import Skel.Gen.Types

/-! The frame emitter in the store-chain form (`docs/one-way-lift-g1-plan-20261118.md`, section 5, task G1-07; decision
D8; the call-return rule `frame_call` of `docs/research/outer-mem-experiment-20261118.md`, section 7).

`frameFacts` walks the blocks from the entry and gives the bytes of `rsp` below the entry value at each block start and
the stack room. `frameText` gives the text that depends on the form of the memory: the conjunct of `rep`, the `Frame`
definition, the `rsp` of `At`, the memory conjunct of `post`, the store guard, and the memory steps of each block. A
function has one of three forms of memory:

* `none`: no stack use, no memory in the state. `post` says `t.data.dmem = s.data.dmem`.
* `mem`: a store through a register, so `St` has a memory. `post` says `t.data.dmem = r.2`; the stores to the stack are
  stores of that memory, and a store through a register has a guard against the private area of the stack.
* `frame`: all stores are stack stores, and there is a stack room. The memory is not in the state: `At` has the
  conjunct `Frame policy s₀ u.data.dmem`, and `post` says `SysV.Outside s room t.data.dmem`. A call site is closed by
  `frame_call`.

The frame rules: the depth of the stack (bytes below the entry `rsp`) is a multiple of 8 and not negative at the end of
each block, the same at each join, and 8 less than the depth at the end of a call block when the callee returns; at a
`ret` the depth is -8. A stack word is a word of 8 bytes at a depth that is a multiple of 8. A narrow slot (4, 2 or 1 bytes,
G1-16) is at a depth that is a multiple of its width and at least its width; it needs the room up to the word that holds
it, and it is not a saved register. A store at or above the return word, `rsp` as a value, and `rsp` in an address other
than `rsp` plus a constant are `frame`. Above the return word a load is a stack argument, a word of 8 bytes at `rsp + 8 (k + 1)`
of the entry (`stackArg`, ARGS8), or else `frame`. -/

namespace Skel.Gen

/-! ## Values and accesses -/

mutual
/-- The value uses the register `rsp`. -/
def Val.usesRsp : Val → Bool
  | .reg r => r == .rsp
  | .lit _ => false
  | .load _ => false
  | .retAddr _ => false
  | .add a b => a.usesRsp || b.usesRsp
  | .sub a b => a.usesRsp || b.usesRsp
  | .mul a b => a.usesRsp || b.usesRsp
  | .shr a _ => a.usesRsp
  | .zext32 a => a.usesRsp
  | .and a b | .or a b | .xor a b => a.usesRsp || b.usesRsp
  | .not a | .neg a | .shl a _ | .extract _ _ a _ | .zext _ a | .sext _ a => a.usesRsp
  | .replaceLow _ a b => a.usesRsp || b.usesRsp
  | .setcc c => c.usesRsp
  | .ite c a b => c.usesRsp || a.usesRsp || b.usesRsp

/-- The condition uses the register `rsp`. -/
def Cond.usesRsp : Cond → Bool
  | .eq a b => a.usesRsp || b.usesRsp
  | .ule a b => a.usesRsp || b.usesRsp
  | .ult a b => a.usesRsp || b.usesRsp
  | .slt a b => a.usesRsp || b.usesRsp
  | .slt32 a b => a.usesRsp || b.usesRsp
  | .not c => c.usesRsp
  | .iff p q => p.usesRsp || q.usesRsp
  | .flag _ => false
end

/-- A constant of 64 bits as a signed number. -/
private def signedOf (n : UInt64) : Int :=
  if n.toNat < 2 ^ 63 then n.toNat else (n.toNat : Int) - 2 ^ 64

/-- The value as `rsp` plus a constant: the constant, in bytes. -/
private def stackOffset : Val → Option Int
  | .reg .rsp => some 0
  | .add a (.lit n) => (stackOffset a).map (· + signedOf n)
  | .sub a (.lit n) => (stackOffset a).map (· - signedOf n)
  | _ => none

/-- The lower-case name of a 64-bit register (a copy of `regName` of `Lift/V2/Lifter.lean`: the generator does not import
that file). -/
private def regName : Reg64 → String
  | .rax => "rax" | .rbx => "rbx" | .rcx => "rcx" | .rdx => "rdx"
  | .rsi => "rsi" | .rdi => "rdi" | .rsp => "rsp" | .rbp => "rbp"
  | .r8 => "r8" | .r9 => "r9" | .r10 => "r10" | .r11 => "r11"
  | .r12 => "r12" | .r13 => "r13" | .r14 => "r14" | .r15 => "r15"

/-- A number in subscript digits: `12` is `₁₂`. -/
private def subscript (n : Nat) : String :=
  (toString n).map fun c => "₀₁₂₃₄₅₆₇₈₉".toList.getD (c.toNat - '0'.toNat) c

/-- The hole for the hypothesis of the `k`-th access (from 0) of a block lemma: `?h₁` for `k = 0`. -/
private def hole (k : Nat) : String := s!"?h{subscript (k + 1)}"

/-- What one access gives: the bytes of stack room that it needs (0 for an access to the heap, the return word, or above),
and, for a store to a stack word, its depth and the register that it stores when the value is the entry value of a
register. -/
private structure AccessFacts where
  need : Nat
  stored : Option (Nat × Option Reg64)

/-- The facts of the access `acc` of the block `b`, which starts at the depth `d0`. -/
private def accessFacts (b : Block) (d0 : Nat) (acc : Access) : Except GenError AccessFacts := do
  let (addr, w, stored) : Val × Width × Option Val := match acc with
    | .load _ a w => (a, w, none)
    | .store _ a w v => (a, w, some v)
  if let some v := stored then
    if v.usesRsp then throw (.frame b.offset "a store of a value that uses rsp")
  if !addr.usesRsp then
    pure ⟨0, none⟩
  else
    let some o := stackOffset addr
      | throw (.frame b.offset "an address that uses rsp in another form than rsp plus a constant")
    let k : Int := (d0 : Int) - o
    if 0 < k then
      if w != .W64 then
        -- a narrow slot: its bytes are below the entry `rsp`, at a depth that is a multiple of its width
        if k < w.bytes then throw (.frame b.offset s!"a stack access of {w.bytes} bytes at the depth {k} meets the return word")
        if k % w.bytes != 0 then
          throw (.frame b.offset s!"a stack access of {w.bytes} bytes at the depth {k}, which is not a multiple of {w.bytes}")
        -- the room is a number of words: the word of the slot is the word that holds its first byte
        pure ⟨(k.toNat + 7) / 8 * 8, none⟩
      else
        if k % 8 != 0 then throw (.frame b.offset s!"a stack word at the depth {k}, which is not a multiple of 8")
        let reg : Option Reg64 := match stored with
          | some (.reg r) => some r
          | _ => none
        pure ⟨k.toNat, stored.map fun _ => (k.toNat, reg)⟩
    else
      if stored.isSome then throw (.frame b.offset "a store at or above the return word")
      -- above the return word, only a stack argument: a word of 8 bytes at `rsp + 8 (k + 1)` of the entry (ARGS8)
      if k < 0 && !(w == .W64 && k % 8 == 0) then
        throw (.frame b.offset s!"a stack load of {w.bytes} bytes at the depth {k}: above the return word only a word of 8 bytes at a multiple of 8 is a stack argument")
      pure ⟨0, none⟩

/-- The facts of the block `b` that starts at the depth `d0`: the depths of its successors, and the bytes of room that it
needs (its accesses, the depth that it reaches, and the room of a callee below a call). -/
private def analyse (rooms : List (String × Nat)) (b : Block) (d0 : Nat) :
    Except GenError (List (Nat × Nat) × Nat) := do
  b.regs.forM fun (r, v) =>
    if r != .rsp && v.usesRsp then throw (.frame b.offset "rsp is the value of a register") else pure ()
  let endOff : Int ← match b.regs.find? (·.1 == .rsp) with
    | none => pure 0
    | some (_, v) =>
      match stackOffset v with
      | some o => pure o
      | none => throw (.frame b.offset "rsp is not rsp plus a constant at the end of the block")
  let peak ← b.accesses.foldlM (fun m a => do pure (max m (← accessFacts b d0 a).need)) 0
  let dEnd : Int := (d0 : Int) - endOff
  let depth : Except GenError Nat :=
    if 0 ≤ dEnd ∧ dEnd % 8 = 0 then pure dEnd.toNat
    else throw (.frame b.offset s!"the depth {dEnd} at the end of the block is not a multiple of 8 above 0")
  let next : Exit → Except GenError (List (Nat × Nat) × Nat)
    | .goto t => do let n ← depth; pure ([(t, n)], n)
    | .ret => if dEnd == -8 then pure ([], 0)
      else throw (.frame b.offset s!"the depth {dEnd} at a return is not -8")
    | .trap => pure ([], 0)
    | .call callee cont => do
      let n ← depth
      let some r := (rooms.find? (·.1 == callee)).map (·.2) | throw (.callee callee)
      if r % 8 != 0 then throw (.frame b.offset s!"the room {r} of {callee} is not a multiple of 8")
      if n < 8 then throw (.frame b.offset "a call with no return word")
      pure ([(cont, n - 8)], n + r)
  match b.term with
  | .exit e => do
    let (s, p) ← next e
    pure (s, max peak p)
  | .branch c y n => do
    if c.usesRsp then throw (.frame b.offset "rsp is in the condition of a branch")
    let (s1, p1) ← next y
    let (s2, p2) ← next n
    pure (s1 ++ s2, max peak (max p1 p2))

/-- The walk over the blocks: the arrivals `(offset, depth)` still to do, the depths found, and the room so far. Each block
is analysed once, so the fuel of `2 n + 2` arrivals is enough. A second arrival at a block with another depth is `frame`. -/
private def walk (rooms : List (String × Nat)) (bs : List Block) :
    Nat → List (Nat × Nat) → List (Nat × Nat) → Nat → Except GenError (List (Nat × Nat) × Nat)
  | 0, _, _, _ => throw (.frame 0 "the walk over the blocks does not end")
  | _, [], seen, room => pure (seen, room)
  | fuel + 1, (o, d) :: rest, seen, room =>
    match seen.find? (·.1 == o) with
    | some (_, d') =>
      if d' == d then walk rooms bs fuel rest seen room
      else throw (.frame o s!"the block is reached at the depths {d'} and {d}")
    | none => do
      let some b := bs.find? (·.offset == o) | throw (.frame o "a jump to an offset that is no block")
      let (succs, peak) ← analyse rooms b d
      walk rooms bs fuel (rest ++ succs) ((o, d) :: seen) (max room peak)

/-- The stack argument that the access reads, in a block at the depth `d0` (ARGS8): `some k` for a load of 8 bytes at
`rsp + 8 (k + 1)` of the entry, the word `k` (from 0) above the return word. In System V it is the argument `7 + k` of the
integer class. -/
def stackArg (d0 : Nat) : Access → Option Nat
  | .load _ addr .W64 =>
    if !addr.usesRsp then none
    else (stackOffset addr).bind fun o =>
      let k : Int := (d0 : Int) - o
      if k < 0 && k % 8 == 0 then some ((-k).toNat / 8 - 1) else none
  | _ => none

/-- The frame facts of a function: the depth of `rsp` at the start of each block that the entry reaches, and the room (the
deepest word, the depth of each block end, and the callee rooms below the calls). `rooms` gives the room of each callee;
a callee that is not in it is `callee`. A block list with no block has room 0. -/
def frameFacts (rooms : List (String × Nat)) (bs : List Block) : Except GenError FrameFacts :=
  match bs with
  | [] => pure ⟨[], 0⟩
  | b0 :: _ => do
    let (seen, room) ← walk rooms bs (2 * bs.length + 2) [(b0.offset, 0)] [] 0
    pure ⟨bs.filterMap fun b => (seen.find? (·.1 == b.offset)).map fun p => (b.offset, p.2), room⟩

/-- The number of stack arguments of the blocks `bs` with the frame facts `ff` (ARGS8): one more than the largest
`stackArg` of a load of a block that the entry reaches, or 0. The model has the fields `stk0 …` of this number, and a
caller passes this number of words. -/
def stackArgCount (ff : FrameFacts) (bs : List Block) : Nat :=
  bs.foldl (init := 0) fun n b =>
    match ff.delta.lookup b.offset with
    | none => n
    | some d0 => b.accesses.foldl (init := n) fun n a => max n (((stackArg d0 a).map (· + 1)).getD 0)

/-- The value that a call at the end of the block `b` passes in the stack argument `k` of the callee (ARGS8): the word at
`rsp + 8 (k + 1)` of the callee is the word at the offset `e + 8 (k + 1)` from the `rsp` of the block start, where `e` is
the offset of `rsp` at the end of the block. The last store of the block that meets a byte of the word decides: a store of
8 bytes to the word gives its value; any other store, or no store, gives `none`. -/
def argStore (b : Block) (k : Nat) : Option Val := do
  let e ← match b.regs.find? (·.1 == .rsp) with
    | none => some 0
    | some (_, v) => stackOffset v
  let at_ : Int := e + 8 * (k + 1)
  let last ← b.accesses.reverse.findSome? fun
    | .store _ addr w v =>
      match (if addr.usesRsp then stackOffset addr else none) with
      | some o => if at_ < o + w.bytes && o < at_ + 8 then some (o, w, v) else none
      | none => none
    | .load .. => none
  let (o, w, v) := last
  if o == at_ && w == .W64 then some v else none

/-! ## Slots (L2-STACK2) -/

/-- Does a store of `w` bytes at the depth `k'` meet the word of 8 bytes at the depth `k`? The store has the bytes from
`sp - k'` to `sp - k' + w - 1`, the word the bytes from `sp - k` to `sp - k + 7`. -/
def meetsWord (k' : Int) (w : Width) (k : Nat) : Bool := (k : Int) - 8 < k' && k' < (k : Int) + w.bytes

/-- The stack words that hold the entry value of a register after the accesses `accs` of a block that starts at the depth
`d0`, from the words `start` at its start. For each word, the last store to it decides: a store of 8 bytes of a register
`r` (not `rsp`) at a depth above 0, where `entry r` says that `r` has its entry value at the block start, makes the word
`(k, r)`; each other store to the stack that meets a byte of a word removes the word. -/
def slotsAfter (entry : Reg64 → Bool) (d0 : Nat) (start : List (Nat × Reg64)) (accs : List Access) :
    List (Nat × Reg64) :=
  accs.foldl (init := start) fun sl a =>
    match a with
    | .load .. => sl
    | .store _ addr w v =>
      match (if addr.usesRsp then stackOffset addr else none) with
      | none => sl
      | some o =>
        let k' := (d0 : Int) - o
        let kept := sl.filter fun (k, _) => !meetsWord k' w k
        match v, w with
        | .reg r, .W64 => if 0 < k' && r != .rsp && entry r then kept ++ [(k'.toNat, r)] else kept
        | _, _ => kept

/-- The saved registers: the words that hold the entry value of a register at the end of the entry block, each with its
depth (`slotsAfter`; the last store to a word decides). -/
def savedSlots (b : Block) : Except GenError (List (Nat × Reg64)) :=
  pure (slotsAfter (fun _ => true) 0 [] b.accesses)

/-! ## The frame definition -/

/-- A description of a frame: the room and the saved registers, each with its depth. The room and the depths are multiples
of 8, a depth is at least 8 and at most the room, and two slots have not the same depth or the same register. -/
def FrameLayout.valid (room : Nat) (slots : List (Nat × Reg64)) : Bool :=
  room % 8 == 0 &&
  slots.all (fun (k, r) => 8 ≤ k && k ≤ room && k % 8 == 0 && r != .rsp) &&
  (slots.map (·.1)).eraseDups.length == slots.length &&
  (slots.map (·.2)).eraseDups.length == slots.length

/-- A valid frame description. -/
structure FrameLayout where
  room : Nat
  slots : List (Nat × Reg64)
  ok : FrameLayout.valid room slots = true

/-- The layout of `slots` in `room`, when valid. -/
def FrameLayout.parse (room : Nat) (slots : List (Nat × Reg64)) : Option FrameLayout :=
  if h : FrameLayout.valid room slots = true then some ⟨room, slots, h⟩ else none

/-- The slots in the order of their depths. -/
private def FrameLayout.sorted (l : FrameLayout) : List (Nat × Reg64) := l.slots.mergeSort fun a b => a.1 ≤ b.1

/-- Are there words in the room? The frame says that the words from 8 to the room are mapped (G1-16: the `post` of the frame
form says it of the same words, so the return case is the conjunct itself). -/
private def FrameLayout.mapped (l : FrameLayout) : Bool := 8 ≤ l.room

/-- The names of the conjuncts of the frame, as the pattern of an `obtain`: a name for each saved register (`r15s`),
`out` for the bytes outside the room, and `mp` for the mapped words. -/
def FrameLayout.names (l : FrameLayout) : List String :=
  l.sorted.map (fun (_, r) => regName r ++ "s") ++ ["out"] ++ (if l.mapped then ["mp"] else [])

/-- The holes for the conjuncts of the frame, in the order of `names`: `?r15s`, `?out`, `?map`. -/
def FrameLayout.holes (l : FrameLayout) : List String :=
  l.sorted.map (fun (_, r) => "?" ++ regName r ++ "s") ++ ["?out"] ++ (if l.mapped then ["?map"] else [])

/-- The definition `Frame`: for a memory `m`, each saved register is at its slot, the bytes outside the room are those of
`s₀`, and the words of the room (from 8 to the room) are mapped. -/
def FrameLayout.frameDef (l : FrameLayout) : String :=
  let slotLines := l.sorted.map fun (k, r) =>
    s!"readRam policy m (s₀.data.regs.rsp.toBitVec - {k}) .W64 = .ok s₀.data.regs.{regName r}.toBitVec"
  let tail := [s!"SysV.Outside s₀ {l.room} m"] ++
    (if l.mapped then [s!"SysV.Mapped s₀.data.regs.rsp.toBitVec 8 {l.room} m"] else [])
  "def Frame (policy : CpuPolicy) (s₀ : MachineState) (m : DataMem) : Prop :=\n  " ++
    " ∧\n  ".intercalate (slotLines ++ tail)

/-! ## The text -/

/-- The text of a call site in the frame form, after the call: the names of the memory conjuncts of the callee post
(`out, mp`, primed when the frame of the caller is in the context, or `hm` for a callee with room 0, whose post is an
equation of the memories), the extra simp lemma for that equation, the holes of the conjuncts of the frame, and the hole
of the store of the return word. -/
structure CallMem where
  retHole : String
  calleePost : String
  simpExtra : String
  frameHoles : List String

/-- The memory steps of one block. `holes` has a hole `?h₁ …` for the hypothesis of each access of the block lemma, in
program order. `tactic` is the line after the `refine'` of the block: `any_goals frame_mem`, or `any_goals frame_call`
at a call in the frame form; it is `none` for a block with no access. `call` is set for a call in the frame form. -/
structure MemSteps where
  holes : List String
  tactic : Option String
  call : Option CallMem

/-- The parts of a call site that depend on the model and not on the frame: the block lemma, the hypothesis of the code
range, the name of the machine data, the lemma of the return address and the return `pc`, the argument facts of the callee
`rep`, the result and state of the callee post, the equations of its `Exit` after `hpc`, the facts of its result, the
lines after the rewrite of `hpc`, the name of `At`, and the parts of the goal before the conjuncts of the frame. -/
structure CallParts where
  blockLemma : String
  exec : String
  data : String
  retLemma : String
  retPc : String
  argFacts : List String
  res : String
  regEqs : List String
  resFacts : List String
  afterReturn : List String
  atName : String
  atParts : List String

/-- The text of the call site of section 7 of the FM-call report, with the frame parts from `m` and the other parts from
`p`. `none` when the block is not a call in the frame form. No line depends on a room size, a slot or the callee. -/
def MemSteps.callSite (m : MemSteps) (p : CallParts) : Option String :=
  m.call.map fun c =>
    let join (xs : List String) : String := ", ".intercalate xs
    "\n".intercalate (
      [ s!"refine' {p.blockLemma} {p.exec} {p.data} {" ".intercalate m.holes} fun f =>",
        s!"  have hret := {p.retLemma} {p.data} {c.retHole} f",
        s!"  ⟨⟨⟨rfl, {p.exec}, ?perm, {p.retPc}, hret⟩, {join (p.argFacts ++ ["?room"])}⟩, ?post⟩",
        "any_goals frame_call",
        "case post =>",
        s!"  rintro {p.res} ⟨⟨{join ("hpc" :: p.regEqs)}⟩, {join (p.resFacts ++ [c.calleePost])}⟩",
        "  rw [hret, Option.some.injEq] at hpc" ] ++
      p.afterReturn.map ("  " ++ ·) ++
      [ s!"  simp only [{p.atName}, Frame{c.simpExtra}]",
        s!"  refine ⟨{join (p.atParts ++ c.frameHoles)}⟩",
        "  any_goals frame_call" ])

/-- The text that depends on the form of the memory (the function `frameText` makes it). The functions that take a name take
the name of the input in `rep` or of the state in a block.

* `repConjs a`: the conjuncts of `rep` for the input `a`, in order: `a.sp = s.data.regs.rsp.toBitVec` when the guard
  needs `sp`, and `SysV.StackRoom policy s <room>`. Empty for room 0 with no memory.
* `frameDef`: the definition `Frame`, in the frame form. `frameIntro`: the names of its conjuncts. `atConj u`: the last
  conjunct of `At` for the state `u`.
* `rspAt off`: `rsp` at the block at `off`, as `s₀.data.regs.rsp - <depth>`; `none` for an offset that no path reaches.
* `post`, `calleePost`: the memory conjunct of `post` (the two are the same text). In the frame form it also keeps the
  words of the room mapped, so that a caller can call the function (G1-16: every function of the frame form can be a
  callee).
* `guardDefs`, `storeGuard x addr w`: the definitions of the private area and the guard `Clear x.input.sp (addr)` of a store
  of the width `w` through a register (the memory form, at any room: at room 0 the private area is the return word). The
  guard of a store of `w` bytes covers `w` bytes (`clearText`, N13).
* `memSteps off`: the memory steps of the block at `off`. -/
structure FrameText where
  repConjs : String → List String
  frameDef : Option String
  frameIntro : List String
  atConj : String → Option String
  rspAt : Nat → Option String
  post : String
  calleePost : String
  guardDefs : Option String
  storeGuard : String → String → Width → Option String
  memSteps : Nat → Option MemSteps

/-- The form of the memory of a function. -/
private inductive Mode where | none | mem | frame
  deriving DecidableEq

/-- The definitions of the private area for a room of `room` bytes (the room, and the return word at `sp`). `Clear sp a n`:
the `n` bytes from `a` are outside the private area; `n` is 8 when it is not given (a store of 8 bytes). -/
private def guardDefsText (room : Nat) : String :=
  s!"abbrev Private (sp b : BitVec 64) : Prop := (b - (sp - {room})).toNat < {room + 8}\n\n" ++
  "abbrev Clear (sp a : BitVec 64) (n : Nat := 8) : Prop := ∀ i, i < n → ¬ Private sp (a + BitVec.ofNat 64 i)"

/-- The guard of a store of the width `w` at `addr` for the model state `x`: `Clear x.input.sp (addr)`, with the number of
bytes of `w` when it is not 8 (N13: a store of 1 byte has no 8 bytes to clear). -/
def clearText (x addr : String) (w : Width) : String :=
  s!"Clear {x}.input.sp ({addr})" ++ (if w == .W64 then "" else s!" {w.bytes}")

/-- Does the access store through an address that does not use `rsp`? -/
private def heapStore : Access → Bool
  | .store _ a _ _ => !a.usesRsp
  | .load _ _ _ => false

/-- The memory steps of the block `b` in the mode `mode`. -/
private def stepsOf (rooms : List (String × Nat)) (mode : Mode) (layout : Option FrameLayout) (b : Block) :
    Except GenError MemSteps := do
  let holes := (List.range b.accesses.length).map hole
  let plain : MemSteps := ⟨holes, if holes.isEmpty then none else some "any_goals frame_mem", none⟩
  match b.term, mode, layout with
  | .exit (.call callee _), .frame, some l => do
    let some r := (rooms.find? (·.1 == callee)).map (·.2) | throw (.callee callee)
    let some last := holes.getLast? | throw (.frame b.offset "a call with no store of the return word")
    let (out, mp) := if b.offset == 0 then ("out", "mp") else ("out'", "mp'")
    pure ⟨holes, some "any_goals frame_call",
      some ⟨last, if r == 0 then "hm" else s!"{out}, {mp}", if r == 0 then ", hm" else "", l.holes⟩⟩
  | _, _, _ => pure plain

/-- The text of the frame for the form `f`, the callee rooms `rooms` and the summary `s`. The form `sep` is not generated
(decision D8). A block with a depth in `s.frame` that needs more room than `s.frame.room` (a callee room that does not
fit, or an access below the room) is `frame`. A summary whose `vars.mem` is not whether some block stores through a register
is `frame`: a memory in the state and the frame form do not mix. The exception is a summary with `vars.mem` and no such store
when `memCall` (a block calls a callee with memory, PIL-CALL): it has the memory form. -/
def frameText (f : MemForm) (rooms : List (String × Nat)) (s : Summary) (memCall : Bool := false) :
    Except GenError FrameText := do
  if f == .sep then throw (.frame 0 "the separation form is not generated (decision D8)")
  let room := s.frame.room
  s.blocks.forM fun b =>
    match s.frame.delta.find? (·.1 == b.offset) with
    | none => pure ()
    | some (_, d0) => do
      let (_, need) ← analyse rooms b d0
      if room < need then
        throw (.frame b.offset s!"the block needs {need} bytes of room, and the room is {room}")
  let heap := s.blocks.any fun b => b.accesses.any heapStore
  if heap != s.vars.mem && !(s.vars.mem && (memCall || 0 < room)) then
    throw (.frame 0 "the memory of the state and the stores through a register do not agree")
  let mode : Mode := if s.vars.mem then .mem else if 0 < room then .frame else .none
  let slots ← match s.blocks.head? with
    | some b0 => savedSlots b0
    | none => pure []
  let layout ← match mode with
    | .frame =>
      match FrameLayout.parse room slots with
      | some l => pure (some l)
      | none => throw (.frame 0 "the saved registers and the room do not make a frame")
    | _ => pure none
  let steps ← s.blocks.mapM fun b => do pure (b.offset, ← stepsOf rooms mode layout b)
  let guarded := mode == .mem
  let post := match mode with
    | .none => "t.data.dmem = s.data.dmem"
    | .mem => "t.data.dmem = r.2"
    | .frame => s!"SysV.Outside s {room} t.data.dmem ∧ SysV.Mapped s.data.regs.rsp.toBitVec 8 {room} t.data.dmem"
  pure
    { repConjs := fun a =>
        (if guarded then [s!"{a}.sp = s.data.regs.rsp.toBitVec"] else []) ++
        (if 0 < room then [s!"SysV.StackRoom policy s {room}"] else [])
      frameDef := layout.map (·.frameDef)
      frameIntro := (layout.map (·.names)).getD []
      atConj := fun u => layout.map fun _ => s!"Frame policy s₀ {u}.data.dmem"
      rspAt := fun off => (s.frame.delta.find? (·.1 == off)).map fun (_, d) =>
        if d == 0 then "s₀.data.regs.rsp" else s!"s₀.data.regs.rsp - {d}"
      post := post
      calleePost := post
      guardDefs := if guarded then some (guardDefsText room) else none
      storeGuard := fun x addr w => if guarded then some (clearText x addr w) else none
      memSteps := fun off => (steps.find? (·.1 == off)).map (·.2) }

end Skel.Gen
