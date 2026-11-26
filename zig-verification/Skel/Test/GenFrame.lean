import Skel.TempDir
import Skel.Gen.Frame
import Skel.Gen.Sym
import Skel.Gen.Split
import Skel.Gen.Asm
import Skel.Source
import Skel.Io
import Skel.Cfg
import Lift.Spike.Code
import Lift.Toys.Code

/-! The tests of `Skel/Gen/Frame.lean` (suite `genframe`): `lake exe skel-test --only genframe`. Each check is a value
that must hold. A check that does not hold prints one `FAIL` line. The golden checks run the real `sites`, `labels`,
`split` and `symBlock` on the functions of `Lift.Spike.Code` and `Lift.Toys.Code`, and compare the emitted text with the
hand chains `Lift/Spike/OuterMem.lean`, `Lift/Spike/Sum.lean` and `Lift/Spike/Job.lean` (read at run time). The real Lean
checks write a file that imports `Lift.Spike.OuterMem`, put the emitted text of a call site in the proof of
`entry_code` and `half1_code`, and run `lake env lean`; they take a few seconds. The property is over random frame
descriptions from the seed. With `--only genframe` the suite also prints one `info` line for each function. -/

namespace GenFrameTests

open Skel.Gen

/-! ## Builders -/

/-- An identifier. The fallback is never used: every name here is valid. -/
def ident (s : String) : Ident := (Ident.parse s).getD ⟨"_", by decide⟩

def blk (name : String) (off : Nat) (accs : List Access) (regs : List (Reg64 × Val)) (term : Term) : Block :=
  ⟨ident name, off, accs, regs, term, []⟩

def lit (n : Nat) : Val := .lit (UInt64.ofNat n)

def rsp : Val := .reg .rsp

/-- `rsp - n` and `rsp + n` at the start of a block. -/
def below (n : Nat) : Val := .sub rsp (lit n)

def above (n : Nat) : Val := .add rsp (lit n)

def vars (mem : Bool) : Vars := ⟨[], [], mem⟩

/-! ## The programs, through the real stages -/

/-- The symbolic blocks of the function `fn` of `code`: `sites`, `labels`, `split`, `symBlock`. -/
def blocksOf (code : Executable) (fn : String) : Except GenError (List Block) := do
  let ss ← sites code fn
  let ls ← labels code fn
  let raws ← split ss ls
  let index := raws.map fun b => (b.name, b.offset)
  raws.mapM (symBlock index)

def factsOf (code : Executable) (fn : String) (rooms : List (String × Nat)) : Except GenError FrameFacts := do
  frameFacts rooms (← blocksOf code fn)

/-- The summary of `fn` with the frame facts of `frameFacts` and the given `mem`. -/
def summaryOf (code : Executable) (fn : String) (rooms : List (String × Nat)) (mem : Bool) :
    Except GenError Summary := do
  let bs ← blocksOf code fn
  pure ⟨fn, bs, vars mem, ← frameFacts rooms bs, none⟩

def textOf (code : Executable) (fn : String) (rooms : List (String × Nat)) (mem : Bool) :
    Except GenError FrameText := do
  frameText .storeChain rooms (← summaryOf code fn rooms mem)

def spike : Executable := Lift.Spike.Code.code

def toys : Executable := Lift.Toys.Code.code

/-- The rooms of the callees of the two programs. -/
def rooms : List (String × Nat) := [(".Ltoy.toyTwo", 32), (".Ltoy.toyHalf", 0), (".Ltoy.toySum", 0)]

/-! ## Predicates on results -/

def isFrame {α : Type} : Except GenError α → Bool
  | .error (.frame _ _) => true
  | _ => false

def isFrameAt {α : Type} (n : Nat) : Except GenError α → Bool
  | .error (.frame m _) => m == n
  | _ => false

def isCallee {α : Type} (name : String) : Except GenError α → Bool
  | .error (.callee m) => m == name
  | _ => false

def factsAre (delta : List (Nat × Nat)) (room : Nat) : Except GenError FrameFacts → Bool
  | .ok ff => ff.delta == delta && ff.room == room
  | .error _ => false

/-- Does the result hold, with the predicate `p` on its value? -/
def holds {α : Type} (r : Except GenError α) (p : α → Bool) : Bool :=
  match r with
  | .ok a => p a
  | .error _ => false

def has (s sub : String) : Bool := (s.splitOn sub).length > 1

def occ (s sub : String) : Nat := (s.splitOn sub).length - 1

/-- The text of the memory steps of the block at `off`, when there is one. -/
def stepsAt (t : Except GenError FrameText) (off : Nat) : Option MemSteps :=
  match t with
  | .ok ft => ft.memSteps off
  | .error _ => none

/-! ## The call-site parts of the hand proofs of `OuterMem.lean` -/

/-- The parts of the call site of `entry_code` that are not frame. -/
def entryParts : CallParts :=
  { blockLemma := "entry_block", exec := "he.exec", data := "d", retLemma := "entry_retAddr", retPc := "ret1PC",
    argFacts := ["ha", "hb"], res := "z u",
    regEqs := ["hsp", "hbx", "hbp", "h12", "h13", "h14", "h15"], resFacts := ["hz"],
    afterReturn := ["have e : d.regs.rsp - 32 + 8 = d.regs.rsp - 24 := by bv_decide"], atName := "at_",
    atParts := ["⟨he, ha, hb, hc, hd, room⟩", "hpc.symm", "hz", "hbx.trans hd", "h14.trans hc", "h15", "hsp.trans e",
      "⟨hbp, h12, h13⟩"] }

/-- The parts of the call site of `half1_code` that are not frame. -/
def half1Parts : CallParts :=
  { blockLemma := "half1_block", exec := "hrep.1.exec", data := "d", retLemma := "half1_retAddr",
    retPc := "ret2PC", argFacts := ["h14", "hbx"], res := "w v",
    regEqs := ["hsp'", "hbx'", "hbp'", "h12'", "h13'", "h14'", "h15'"], resFacts := ["hw"], afterReturn := [],
    atName := "at_",
    atParts := ["hrep", "hpc.symm", "h15'.trans hax", "hw", "hsp'.trans (by rw [hsp]; bv_decide)",
      "⟨hbp'.trans hbp, h12'.trans h12, h13'.trans h13⟩"] }

/-- The call site of `entry_code`, as the frame emitter must write it (section 7 of the FM-call report). -/
def entryExpected : String :=
  "refine' entry_block he.exec d ?h₁ ?h₂ ?h₃ ?h₄ fun f =>\n" ++
  "  have hret := entry_retAddr d ?h₄ f\n" ++
  "  ⟨⟨⟨rfl, he.exec, ?perm, ret1PC, hret⟩, ha, hb, ?room⟩, ?post⟩\n" ++
  "any_goals frame_call\n" ++
  "case post =>\n" ++
  "  rintro z u ⟨⟨hpc, hsp, hbx, hbp, h12, h13, h14, h15⟩, hz, out, mp⟩\n" ++
  "  rw [hret, Option.some.injEq] at hpc\n" ++
  "  have e : d.regs.rsp - 32 + 8 = d.regs.rsp - 24 := by bv_decide\n" ++
  "  simp only [at_, Frame]\n" ++
  "  refine ⟨⟨he, ha, hb, hc, hd, room⟩, hpc.symm, hz, hbx.trans hd, h14.trans hc, h15, hsp.trans e, " ++
    "⟨hbp, h12, h13⟩, ?r15s, ?r14s, ?rbxs, ?out, ?map⟩\n" ++
  "  any_goals frame_call"

/-- The call site of `half1_code`: the same form; the names of the callee post are primed, because `out` and `mp` of
the frame are in the context. -/
def half1Expected : String :=
  "refine' half1_block hrep.1.exec d ?h₁ fun f =>\n" ++
  "  have hret := half1_retAddr d ?h₁ f\n" ++
  "  ⟨⟨⟨rfl, hrep.1.exec, ?perm, ret2PC, hret⟩, h14, hbx, ?room⟩, ?post⟩\n" ++
  "any_goals frame_call\n" ++
  "case post =>\n" ++
  "  rintro w v ⟨⟨hpc, hsp', hbx', hbp', h12', h13', h14', h15'⟩, hw, out', mp'⟩\n" ++
  "  rw [hret, Option.some.injEq] at hpc\n" ++
  "  simp only [at_, Frame]\n" ++
  "  refine ⟨hrep, hpc.symm, h15'.trans hax, hw, hsp'.trans (by rw [hsp]; bv_decide), " ++
    "⟨hbp'.trans hbp, h12'.trans h12, h13'.trans h13⟩, ?r15s, ?r14s, ?rbxs, ?out, ?map⟩\n" ++
  "  any_goals frame_call"

def callSiteAt (t : Except GenError FrameText) (off : Nat) (p : CallParts) : Option String :=
  (stepsAt t off).bind fun m => m.callSite p

/-! ## Random frame descriptions -/

def nextWord (s : UInt64) : UInt64 × UInt64 :=
  let s' := s * 6364136223846793005 + 1442695040888963407
  (s', s' ^^^ (s' >>> 29))

def allRegs : List Reg64 :=
  [.rax, .rbx, .rcx, .rdx, .rsi, .rdi, .rsp, .rbp, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

/-- A random description: a room (mostly a multiple of 8) and up to four slots (mostly at multiples of 8). -/
def randomLayout (st : UInt64) : (UInt64 × (Nat × List (Nat × Reg64))) :=
  let (s1, w) := nextWord st
  let room := 8 * (w.toNat % 12) + (if w.toNat / 16 % 7 == 0 then 3 else 0)
  let n := w.toNat / 128 % 5
  let (s2, slots) := (List.range n).foldl
    (fun (acc : UInt64 × List (Nat × Reg64)) _ =>
      let (s, _) := nextWord acc.1
      let k := 8 * (s.toNat % 14) + (if s.toNat / 64 % 9 == 0 then 4 else 0)
      let r := allRegs.getD (s.toNat / 4096 % 16) .rax
      (s, acc.2 ++ [(k, r)])) (s1, [])
  (s2, (room, slots))

def layouts (seed cases : Nat) : List (Nat × List (Nat × Reg64)) :=
  ((List.range cases).foldl
    (fun (acc : UInt64 × List (Nat × List (Nat × Reg64))) _ =>
      let (s, l) := randomLayout acc.1
      (s, l :: acc.2)) (UInt64.ofNat seed * 2654435761 + 12345, [])).2

/-- The name of a register, from its `Repr` (an oracle that is not the code under test). -/
def regStr (r : Reg64) : String := ((toString (repr r)).splitOn ".").getLastD ""

/-- The description is valid, written as a statement on the pairs of slots. -/
def validSpec (room : Nat) (slots : List (Nat × Reg64)) : Bool :=
  room % 8 == 0 &&
  slots.all (fun (k, r) => 8 ≤ k && k ≤ room && k % 8 == 0 && r != .rsp) &&
  (List.range slots.length).all fun i => (List.range slots.length).all fun j =>
    i == j || (match slots[i]?, slots[j]? with
      | some (k, r), some (k', r') => k != k' && r != r'
      | _, _ => false)

/-- The text names each slot once: its offset and its register; the slots come in the order of their offsets. -/
def textOk (l : FrameLayout) (text : String) : Bool :=
  l.slots.all (fun (k, r) =>
    occ text s!"(s₀.data.regs.rsp.toBitVec - {k})" == 1 && occ text s!"s₀.data.regs.{regStr r}.toBitVec" == 1) &&
  occ text "∧" + 1 == l.names.length

/-- Two slots do not overlap: their offsets are at least 8 apart. -/
def apart (l : FrameLayout) : Bool :=
  l.slots.all fun (k, _) => l.slots.all fun (k', _) => k == k' || 8 ≤ (if k < k' then k' - k else k - k')

/-- The offsets in the order of the text. -/
def textOffsets (_l : FrameLayout) (text : String) : List Nat :=
  (text.splitOn "(s₀.data.regs.rsp.toBitVec - ").tail.filterMap fun part => (part.takeWhile Char.isDigit).toNat?

/-! ## The checks -/

/-- The definitions of the private area of a store at room 0: the return word is the private area, at `sp`. -/
def roomZeroGuardDefs : String :=
  "abbrev Private (sp b : BitVec 64) : Prop := (b - (sp - 0)).toNat < 8\n\n" ++
  "abbrev Clear (sp a : BitVec 64) (n : Nat := 8) : Prop := ∀ i, i < n → ¬ Private sp (a + BitVec.ofNat 64 i)"

/-- The `Clear` of the hand chain `Job` with the number of bytes as an argument of default 8 (N13): the generated `Clear`. -/
def withBytes (c : String) : String :=
  c.replace "(sp a : BitVec 64) : Prop := ∀ i, i < 8 →" "(sp a : BitVec 64) (n : Nat := 8) : Prop := ∀ i, i < n →"

/-- The checks that need no file. `ouM`, `sumS`, `jobS` are the texts of the hand chains. -/
def checks (seed cases : Nat) (ouM sumS jobS : String) : List (String × Bool) :=
  let outerT := textOf toys "toyOuter" rooms false
  let twoT := textOf toys "toyTwo" rooms false
  let sumT := textOf spike "toySum" rooms false
  let jobT := textOf spike "toyJob" rooms true
  let fillT := textOf toys "toyFill" [] true
  let handFrame := (declText ouM "Frame").map squash
  let handAt := (declText ouM "at_").map squash
  let handPost := (declText ouM "post").map squash
  let handPostTwo := (declText ouM "postTwo").map squash
  let handSumPost := (declText sumS "post").map squash
  let handJobL2 := (declText jobS "l2").map squash
  let handJobBlocks := (declText jobS "blocks").map squash
  let handPrivate := (declText jobS "Private").map squash
  -- the text of `Clear` runs on into the comment of the next section
  let handClear := (declText jobS "Clear").map fun t => squash ((t.splitOn "/-!").headD t)
  let layoutTests := layouts seed cases
  let accepted := layoutTests.filterMap fun (room, slots) => (FrameLayout.parse room slots).map fun l => l
  -- the pipeline for a raw block that `symBlock` refuses
  let rawRsp : RawBlock := ⟨ident "entry", 0, [⟨0, .regular .W64 .W64 (.mov (.reg (.low .rsp .W64))
    (.regOrMem (.reg (.low .rbx .W64))))⟩], none⟩
  let viaSym : Except GenError FrameFacts := do
    frameFacts [] [← symBlock [] rawRsp]
  let retBlock (d : Nat) (n : Nat) : Block :=
    blk "entry" 0 [.load 0 rsp .W64] [(.rsp, above n)] (.exit .ret) |> fun b => { b with offset := d }
  [ -- toySum: no stack use
    ("toySum: all deltas 0, room 0",
      factsAre [(0, 0), (4, 0), (9, 0), (18, 0)] 0 (factsOf spike "toySum" rooms)),
    ("toySum: no room conjunct, no frame definition, no guard",
      holds sumT fun t => (t.repConjs "a").isEmpty && t.frameDef.isNone && t.guardDefs.isNone &&
        (t.storeGuard "x" "a" .W64).isNone),
    ("toySum: post is the memory conjunct of Sum.post",
      holds sumT (fun t => t.post == "t.data.dmem = s.data.dmem") &&
        (handSumPost.any fun h => has h "t.data.dmem = s.data.dmem")),
    ("toySum: the rsp of each block is the rsp of the call",
      holds sumT fun t => t.rspAt 18 == some "s₀.data.regs.rsp" && t.rspAt 5 == none),
    ("toySum: a block with no memory access has no hole and no tactic",
      (stepsAt sumT 0).any fun m => m.holes.isEmpty && m.tactic.isNone && m.call.isNone),
    ("toySum: o9 has one hole and one frame_mem call",
      (stepsAt sumT 9).any fun m => m.holes == ["?h₁"] && m.tactic == some "any_goals frame_mem" && m.call.isNone),
    -- toyJob: push/pop, a store through a register, a call to a callee with no room; memory in the state
    ("toyJob: deltas, room 16",
      factsAre [(0, 0), (10, 0), (14, 0), (26, 8)] 16 (factsOf spike "toyJob" rooms)),
    ("toyJob: rep has StackRoom 16 as Job.l2, and the sp conjunct",
      holds jobT (fun t => t.repConjs "x" == ["x.sp = s.data.regs.rsp.toBitVec", "SysV.StackRoom policy s 16"]) &&
        (handJobL2.any fun h => has h "SysV.StackRoom policy s 16")),
    ("toyJob: post is the memory conjunct of Job.l2",
      holds jobT (fun t => t.post == "t.data.dmem = r.2") && (handJobL2.any fun h => has h "t.data.dmem = r.2")),
    ("toyJob: the guard text is the guard of Job.blocks",
      holds jobT (fun t => t.storeGuard "x" "x.input.j.toBitVec + 24" .W64 == some "Clear x.input.sp (x.input.j.toBitVec + 24)") &&
        (handJobBlocks.any fun h => has h "Clear x.input.sp (x.input.j.toBitVec + 24)")),
    ("toyJob: the guard definitions are Private and Clear of Job, with the number of bytes of Clear an argument of default 8",
      holds jobT (fun t => match t.guardDefs, handPrivate, handClear with
        | some g, some p, some c => withBytes c != c && squash g == p ++ " " ++ withBytes c.trimAscii.toString
        | _, _, _ => false)),
    ("toyJob: no Frame in the memory form",
      holds jobT fun t => t.frameDef.isNone && (t.atConj "u").isNone),
    ("toyJob: the call block has its holes and one frame_mem call, no call-site text",
      (stepsAt jobT 14).any fun m => m.holes == ["?h₁", "?h₂", "?h₃"] && m.tactic == some "any_goals frame_mem" &&
        m.call.isNone),
    -- toyFill: a store through a register at room 0 is guarded by the return word (the text of the guarded form)
    ("toyFill at room 0: the guard definitions, the store guard and the sp conjunct",
      holds fillT fun t =>
        t.guardDefs.map squash == some (squash roomZeroGuardDefs) && t.storeGuard "x" "a" .W64 == some "Clear x.input.sp (a)" &&
          t.repConjs "x" == ["x.sp = s.data.regs.rsp.toBitVec"]),
    ("a store of w bytes below 8 has the guard Clear of w bytes (N13); a store of 8 bytes has the default",
      holds fillT fun t =>
        t.storeGuard "x" "a" .W8 == some "Clear x.input.sp (a) 1" && t.storeGuard "x" "a" .W16 == some "Clear x.input.sp (a) 2" &&
          t.storeGuard "x" "a" .W32 == some "Clear x.input.sp (a) 4" && t.storeGuard "x" "a" .W64 == some "Clear x.input.sp (a)"),
    -- toyOuter: a function with calls
    ("toyOuter: deltas 0, 24, 24 and room 64",
      factsAre [(0, 0), (16, 24), (30, 24)] 64 (factsOf toys "toyOuter" rooms)),
    ("toyOuter: the frame definition is Frame of OuterMem.lean with the words of the room mapped from 8 (G1-16)",
      holds outerT (fun t => (t.frameDef.map fun d => squash (d.replace "SysV.Mapped" "Mapped")) ==
        handFrame.map (·.replace "Mapped s₀.data.regs.rsp.toBitVec 32 64 m" "Mapped s₀.data.regs.rsp.toBitVec 8 64 m"))),
    ("toyOuter: the frame conjunct of At is the one of OuterMem.lean",
      holds outerT (fun t => t.atConj "u" == some "Frame policy s₀ u.data.dmem") &&
        (handAt.any fun h => has h "Frame policy s₀ u.data.dmem")),
    ("toyOuter: rsp at the blocks after the calls",
      holds outerT (fun t => t.rspAt 16 == some "s₀.data.regs.rsp - 24" && t.rspAt 30 == some "s₀.data.regs.rsp - 24") &&
        (handAt.any fun h => has h "u.data.regs.rsp = s₀.data.regs.rsp - 24")),
    ("toyOuter: rep has StackRoom 64 and no sp conjunct",
      holds outerT fun t => t.repConjs "x" == ["SysV.StackRoom policy s 64"]),
    ("toyOuter: post is the memory conjunct of post of OuterMem.lean and the mapped words of postTwo (G1-16: a function of the frame form can be a callee)",
      holds outerT (fun t => t.post == "SysV.Outside s 64 t.data.dmem ∧ SysV.Mapped s.data.regs.rsp.toBitVec 8 64 t.data.dmem") &&
        (handPost.any fun h => has h "SysV.Outside s 64 t.data.dmem") &&
        (handPostTwo.any fun h => has h "Mapped s.data.regs.rsp.toBitVec 8 32 t.data.dmem")),
    ("toyTwo: the post of a callee is postTwo of OuterMem.lean",
      holds twoT (fun t => t.calleePost == "SysV.Outside s 32 t.data.dmem ∧ SysV.Mapped s.data.regs.rsp.toBitVec 8 32 t.data.dmem") &&
        (handPostTwo.any fun h => has h "SysV.Outside s 32 t.data.dmem ∧ Mapped s.data.regs.rsp.toBitVec 8 32 t.data.dmem")),
    ("toyOuter: the frame intro names are the names of OuterMem.lean",
      holds outerT fun t => t.frameIntro == ["r15s", "r14s", "rbxs", "out", "mp"]),
    ("toyOuter: the call site of the entry block is the text of section 7 of the FM-call report",
      callSiteAt outerT 0 entryParts == some entryExpected),
    ("toyOuter: the call site of the second block has primed names for the callee post",
      callSiteAt outerT 16 half1Parts == some half1Expected),
    ("toyOuter: the block after the calls has four holes and one frame_mem call",
      (stepsAt outerT 30).any fun m => m.holes == ["?h₁", "?h₂", "?h₃", "?h₄"] &&
        m.tactic == some "any_goals frame_mem" && m.call.isNone),
    ("toyOuter: a call site has the return word store as its last hole",
      (stepsAt outerT 0).any fun m => m.call.any fun c => c.retHole == "?h₄" && m.holes.length == 4),
    -- toyTwo calls a callee with no room: the callee post is one equation
    ("toyTwo: deltas 0, 24, 24 and room 32",
      factsAre [(0, 0), (12, 24), (23, 24)] 32 (factsOf toys "toyTwo" rooms)),
    ("toyTwo: a callee with room 0 gives the equation form of the callee post",
      (stepsAt twoT 0).any fun m => m.call.any fun c => c.calleePost == "hm" && c.simpExtra == ", hm"),
    ("toyTwo: the frame definition names the three pushed registers",
      holds twoT fun t => (t.frameDef.map fun d => (occ d ".W64 = .ok") == 3 && has d "regs.rax.toBitVec") == some true),
    -- the room against the CFG analysis of the old chain
    -- `Lift.P2.Gen.Frame.analyse` gives the owned region of the function: the saved registers and the locals. It does not
    -- count the return word of a call or the room of a callee. The room here is `n`, plus 8 and the callee room at a call.
    ("the room of toySum, toyJob, toyOuter and toyTwo is the n of Lift.P2.Gen.Frame.analyse, plus 8 and the callee room for a call",
      [("toySum", spike, Lift.Spike.Code.program, 0, 0), ("toyJob", spike, Lift.Spike.Code.program, 8, 8 + 0),
        ("toyOuter", toys, Lift.Toys.Code.program, 24, 8 + 32), ("toyTwo", toys, Lift.Toys.Code.program, 24, 8 + 0)].all
        fun (fn, code, prog, n, extra) =>
          holds (factsOf code fn rooms) (fun ff => ff.room == n + extra) &&
          (match (Skel.Cfg.sliceFunction prog fn >>= Lift.P2.Gen.Cfg.ofProgram >>= Lift.P2.Gen.Frame.analyse) with
            | .ok f => f.n == n
            | .error _ => false)),
    -- negative cases
    ("a frame of 12 bytes is a frame error at the block",
      isFrameAt 0 (frameFacts [] [blk "entry" 0 [] [(.rsp, below 12)] (.exit (.goto 4)), retBlock 4 8])),
    ("a callee room of 12 is a frame error",
      isFrame (factsOf toys "toyOuter" [(".Ltoy.toyTwo", 12)])),
    ("a callee with no room in the list is the callee error",
      isCallee ".Ltoy.toyTwo" (factsOf toys "toyOuter" [])),
    ("a callee room larger than the free room of the caller is a frame error",
      match summaryOf toys "toyOuter" rooms false with
      | .ok s => isFrameAt 0 (frameText .storeChain rooms { s with frame := { s.frame with room := 40 } })
      | .error _ => false),
    ("the same room is accepted at its exact size (64 for toyOuter)",
      match summaryOf toys "toyOuter" rooms false with
      | .ok s => (frameText .storeChain rooms { s with frame := { s.frame with room := 64 } }).toOption.isSome
      | .error _ => false),
    ("the separation form is not generated",
      match summaryOf toys "toyOuter" rooms false with
      | .ok s => isFrameAt 0 (frameText .sep rooms s)
      | .error _ => false),
    ("a state with memory retains stack accesses in the memory model",
      holds (textOf toys "toyOuter" rooms true) fun t =>
        t.frameDef.isNone && (t.memSteps 0).isSome && has t.post "t.data.dmem = r.2"),
    ("a state with no memory for a function that stores through a register is a frame error",
      isFrame (textOf spike "toyJob" rooms false)),
    ("two stack depths at one join are a frame error at the join",
      isFrameAt 8 (frameFacts []
        [blk "entry" 0 [] [] (.branch (.eq (.reg .rax) (lit 0)) (.goto 4) (.goto 8)),
         blk "L" 4 [.store 0 (below 8) .W64 (lit 1)] [(.rsp, below 8)] (.exit (.goto 8)),
         blk "M" 8 [.load 0 rsp .W64] [(.rsp, above 8)] (.exit .ret)])),
    ("a push in a loop is a frame error at the head of the loop",
      isFrameAt 4 (frameFacts []
        [blk "entry" 0 [] [] (.exit (.goto 4)),
         blk "L" 4 [.store 0 (below 8) .W64 (lit 1)] [(.rsp, below 8)] (.exit (.goto 4))])),
    ("a store at the return word is a frame error",
      isFrameAt 0 (frameFacts [] [blk "entry" 0 [.store 0 rsp .W64 (lit 1), .load 0 rsp .W64] [(.rsp, above 8)] (.exit .ret)])),
    ("a store above the return word is a frame error",
      isFrame (frameFacts [] [blk "entry" 0 [.store 0 (above 8) .W64 (lit 1)] [] (.exit (.goto 4)), retBlock 4 8])),
    ("a store of 8 bytes at a stack offset of 4 is a frame error",
      isFrame (frameFacts [] [blk "entry" 0 [.store 0 (below 4) .W64 (lit 1)] [] (.exit (.goto 4)), retBlock 4 8])),
    ("a store of one byte at the depth 8 is a narrow slot: the room is 8 (G1-16)",
      holds (frameFacts [] [blk "entry" 0 [.store 0 (below 8) .W8 (lit 1)] [] (.exit (.goto 4)), retBlock 4 8])
        (·.room == 8)),
    ("narrow slots: a store and a load of 1, 2 or 4 bytes at each depth j * w (j = 1 to 24): the room is the depth rounded up to a word",
      [Width.W8, .W16, .W32].all fun w => (List.range 24).all fun j =>
        let k := (j + 1) * w.bytes
        holds (frameFacts [] [blk "entry" 0 [.store 0 (below k) w (lit 1), .load 1 (below k) w] [] (.exit (.goto 4)),
          retBlock 4 8]) (·.room == (k + 7) / 8 * 8)),
    ("narrow slots: a slot of w bytes at a depth that is no multiple of w is a frame error at the block (w = 2, 4)",
      [(Width.W16, 3), (.W16, 9), (.W32, 6), (.W32, 10), (.W32, 18)].all fun (w, k) =>
        isFrameAt 0 (frameFacts [] [blk "entry" 0 [.store 0 (below k) w (lit 1)] [] (.exit (.goto 4)), retBlock 4 8])),
    ("narrow slots: a slot of w bytes at a depth below w meets the return word: a frame error (w = 2, 4)",
      [(Width.W16, 1), (.W32, 1), (.W32, 2), (.W32, 3)].all fun (w, k) =>
        isFrameAt 0 (frameFacts [] [blk "entry" 0 [.load 0 (below k) w] [] (.exit (.goto 4)), retBlock 4 8])),
    ("narrow slots: a store of 4 bytes of a register is not a saved register",
      match savedSlots (blk "entry" 0 [.store 0 (below 4) .W32 (.reg .rbx), .store 1 (below 16) .W64 (.reg .r14)] [] (.exit .ret)) with
      | .ok l => l == [(16, .r14)]
      | .error _ => false),
    ("a load of one byte above the return word is a frame error (ARGS8: a stack argument is a word of 8 bytes)",
      isFrame (frameFacts [] [blk "entry" 0 [.load 0 (above 16) .W8, .load 1 rsp .W64] [(.rsp, above 8)] (.exit .ret)])),
    ("a load of 8 bytes at rsp + 16 is accepted (the stack argument 1, ARGS8)",
      (frameFacts [] [blk "entry" 0 [.load 0 (above 16) .W64, .load 1 rsp .W64] [(.rsp, above 8)] (.exit .ret)]).toOption.isSome),
    ("rsp as the value of a register is a frame error",
      isFrameAt 0 (frameFacts [] [blk "entry" 0 [] [(.rbp, rsp)] (.exit (.goto 4)), retBlock 4 8])),
    ("rsp in the value of a store is a frame error",
      isFrame (frameFacts [] [blk "entry" 0 [.store 0 (below 8) .W64 rsp] [(.rsp, below 8)] (.exit (.goto 4)), retBlock 4 8])),
    ("rsp in a branch condition is a frame error",
      isFrame (frameFacts [] [blk "entry" 0 [] [] (.branch (.eq rsp (lit 0)) (.goto 4) (.goto 4)), retBlock 4 8])),
    ("rsp plus an index is a frame error",
      isFrame (frameFacts [] [blk "entry" 0 [.load 0 (.add rsp (.mul (.reg .rcx) (lit 8))) .W64] [] (.exit (.goto 4)), retBlock 4 8])),
    ("a return with the stack not balanced is a frame error",
      isFrame (frameFacts [] [blk "entry" 0 [.load 0 rsp .W64] [(.rsp, above 16)] (.exit .ret)])),
    ("a goto to an offset that is no block is a frame error",
      isFrame (frameFacts [] [blk "entry" 0 [] [] (.exit (.goto 99))])),
    ("a rsp that symBlock refuses (mov rbx, rsp) is the frame error of symBlock, at its offset",
      isFrameAt 0 viaSym),
    -- boundary cases
    ("no block gives room 0 and no delta",
      factsAre [] 0 (frameFacts [] [])),
    ("no block gives the text of a function with no stack",
      holds (frameText .storeChain [] ⟨"f", [], vars false, ⟨[], 0⟩, none⟩) fun t => t.frameDef.isNone && t.post == "t.data.dmem = s.data.dmem"),
    ("a block that no path reaches has no delta",
      factsAre [(0, 0)] 0 (frameFacts [] [retBlock 0 8, blk "dead" 4 [] [] (.exit .trap)])),
    ("a leaf with a push and a pop: room 8, one saved register, no callee",
      match frameFacts [] [blk "entry" 0 [.store 0 (below 8) .W64 (.reg .rbx), .load 0 (below 8) .W64, .load 1 rsp .W64]
          [(.rsp, above 8), (.rbx, .load 0)] (.exit .ret)] with
      | .ok ff => ff.room == 8 && ff.delta == [(0, 0)]
      | .error _ => false),
    ("savedSlots of the entry block of toyOuter",
      holds (blocksOf toys "toyOuter") fun bs =>
        match bs with
        | b :: _ => (match savedSlots b with
            | .ok ss => ss == [(8, .r15), (16, .r14), (24, .rbx)]
            | .error _ => false)
        | [] => false),
    ("two saved registers at one offset: the last store gives the slot (L2-STACK2)",
      holds (savedSlots (blk "entry" 0 [.store 0 (below 8) .W64 (.reg .rbx), .store 1 (below 8) .W64 (.reg .r12)]
        [(.rsp, below 8)] (.exit (.goto 4)))) (· == [(8, .r12)])),
    -- the layouts
    ("FrameLayout.parse refuses an offset that is no multiple of 8, 0, above the room, a double offset, a double register, rsp, a room of 12",
      (FrameLayout.parse 24 [(4, .rbx)]).isNone && (FrameLayout.parse 24 [(0, .rbx)]).isNone && (FrameLayout.parse 24 [(32, .rbx)]).isNone &&
        (FrameLayout.parse 24 [(8, .rbx), (8, .r12)]).isNone && (FrameLayout.parse 24 [(8, .rbx), (16, .rbx)]).isNone &&
        (FrameLayout.parse 24 [(8, .rsp)]).isNone && (FrameLayout.parse 12 []).isNone),
    ("FrameLayout.parse accepts the boundaries: no slot, a slot at the room, a room of 0",
      (FrameLayout.parse 0 []).isSome && (FrameLayout.parse 24 [(24, .rbx)]).isSome && (FrameLayout.parse 8 [(8, .rbx)]).isSome),
    ("random layouts: parse agrees with the statement on the pairs of slots",
      layoutTests.all fun (room, slots) => (FrameLayout.parse room slots).isSome == validSpec room slots),
    ("random layouts: some are accepted and some are refused",
      accepted.length > 0 && accepted.length < layoutTests.length),
    ("random layouts: the text names each slot once, in the order of the offsets, and the slots are 8 apart",
      accepted.all fun l => textOk l l.frameDef && apart l &&
        (let offs := textOffsets l l.frameDef; offs == (l.slots.map (·.1)).mergeSort (· ≤ ·))),
    ("random layouts: the intro names are the slot names, out, and mp when the words below the slots are mapped",
      accepted.all fun l => l.names.length == l.slots.length + 1 + (if (l.slots.map (·.1)).foldl max 0 + 8 ≤ l.room then 1 else 0)) ]

/-! ## The real Lean checks -/

/-- The text, indented by two spaces. -/
def indent (s : String) : String := "\n".intercalate ((s.splitOn "\n").map fun l => "  " ++ l)

def preamble : String :=
  "import Lift.Spike.OuterMem\n\nopen Lift.P2.Total Lift.Sem\nopen Lift.Sem.SysV (Mapped)\n\n" ++
  "namespace Lift.Toys.OuterMem\n\n"

/-- A check file for `entry_code`: the proof is the hand setup and the emitted call site. -/
def entryFile (site : String) : String :=
  preamble ++
  "theorem entry_code' {policy : CpuPolicy} {x : Args} {s₀ : MachineState} (h : rep policy x s₀) :\n" ++
  "    Reaches L1.step policy (fun t => repTwo policy (x.1, x.2.1) t ∧\n" ++
  "      ∀ z u, postTwo (x.1, x.2.1) z t u →\n" ++
  "        at_ policy x s₀ .half1 (z, x.2.2.1, x.2.2.2, 0) u) s₀ := by\n" ++
  "  obtain ⟨he, ha, hb, hc, hd, room⟩ := h\n" ++
  "  obtain ⟨d, pc⟩ := s₀\n" ++
  "  obtain rfl : pc = toyOuterPC := he.pc\n" ++
  indent site ++ "\n\nend Lift.Toys.OuterMem\n\n#print axioms Lift.Toys.OuterMem.entry_code'\n"

/-- A check file for `half1_code`: the hand setup, with the frame names of `intro`, and the emitted call site. -/
def half1File (intro : String) (site : String) : String :=
  preamble ++
  "theorem half1_code' {policy : CpuPolicy} {x : Args} {s₀ u : MachineState} {z c e g : UInt64}\n" ++
  "    (h : at_ policy x s₀ .half1 (z, c, e, g) u) :\n" ++
  "    Reaches L1.step policy (fun t => repTwo policy (c, e) t ∧\n" ++
  "      ∀ w v, postTwo (c, e) w t v → at_ policy x s₀ .half2 (z, w, 0, 0) v) u := by\n" ++
  "  obtain ⟨d, pc⟩ := u\n" ++
  "  dsimp only [at_] at h\n" ++
  s!"  obtain ⟨hrep, rfl, hax, hbx, h14, h15, hsp, ⟨hbp, h12, h13⟩, {intro}⟩ := h\n" ++
  "  have room := hrep.2.2.2.2.2\n" ++
  indent site ++ "\n\nend Lift.Toys.OuterMem\n\n#print axioms Lift.Toys.OuterMem.half1_code'\n"

/-- A check file for a caller of a callee with room 0 (the post is an equation): the statement of `entry_code`
with the callee post `postHalf`. The text is the call site with the callee post `hm`. -/
def entryHalfFile (site : String) : String :=
  preamble ++
  "def repHalf (policy : CpuPolicy) (ab : UInt64 × UInt64) (s : MachineState) : Prop :=\n" ++
  "  SysV.Entry policy toyCountPC toyEndPC toyTwoPC s ∧ s.data.regs.rdi = ab.1 ∧\n" ++
  "    s.data.regs.rsi = ab.2 ∧ SysV.StackRoom policy s 0\n\n" ++
  "def postHalf (_ : UInt64 × UInt64) (y : UInt64) (s t : MachineState) : Prop :=\n" ++
  "  SysV.Exit s t ∧ t.data.regs.rax = y ∧ t.data.dmem = s.data.dmem\n\n" ++
  "theorem entry_code0 {policy : CpuPolicy} {x : Args} {s₀ : MachineState} (h : rep policy x s₀) :\n" ++
  "    Reaches L1.step policy (fun t => repHalf policy (x.1, x.2.1) t ∧\n" ++
  "      ∀ z u, postHalf (x.1, x.2.1) z t u →\n" ++
  "        at_ policy x s₀ .half1 (z, x.2.2.1, x.2.2.2, 0) u) s₀ := by\n" ++
  "  obtain ⟨he, ha, hb, hc, hd, room⟩ := h\n" ++
  "  obtain ⟨d, pc⟩ := s₀\n" ++
  "  obtain rfl : pc = toyOuterPC := he.pc\n" ++
  indent site ++ "\n\nend Lift.Toys.OuterMem\n\n#print axioms Lift.Toys.OuterMem.entry_code0\n"

/-- A check file that the emitted definition of the frame gives the `Frame` of `OuterMem.lean`: the emitted frame maps the
words of the room from 8, the hand frame from 32 (G1-16). -/
def frameDefFile (def' : String) : String :=
  preamble ++ def'.replace "def Frame " "def FrameGen " ++
  "\n\ntheorem frameGen_eq : ∀ policy s₀ m, FrameGen policy s₀ m → Frame policy s₀ m :=\n" ++
  "  fun _ _ _ ⟨a, b, c, d, e⟩ => ⟨a, b, c, d, e.mono (by decide)⟩\n\nend Lift.Toys.OuterMem\n\n" ++
  "#print axioms Lift.Toys.OuterMem.frameGen_eq\n"

private def newDir (tag : String) : IO System.FilePath := do
  let dir ← Skel.tempDir s!"genframe-{tag}"
  return dir

/-- The check of the text of a file: accepted with the gate that admits `bv_decide`. -/
def leanCheck (tag text : String) (thm : String) : IO (Bool × String) := do
  let dir ← newDir tag
  let path := dir / "check.lean"
  IO.FS.writeFile path text
  let (o, _) ← Skel.Io.checkFile .bvDecide path thm 180000
  match o with
  | .accepted _ => pure (true, "")
  | other => pure (false, s!"{repr other}\nfile: {path}")

/-- The real Lean checks, each with its name. -/
def leanChecks : IO (List (String × (Bool × String))) := do
  let outerT := textOf toys "toyOuter" rooms false
  let some entry := callSiteAt outerT 0 entryParts | pure [("entry call site exists", (false, ""))]
  let some half1 := callSiteAt outerT 16 half1Parts | pure [("half1 call site exists", (false, ""))]
  let intro := match outerT with
    | .ok t => ", ".intercalate t.frameIntro
    | .error _ => ""
  let frameDefText := match outerT with
    | .ok t => t.frameDef.getD ""
    | .error _ => ""
  let hmSite := match callSiteAt (textOf toys "toyOuter" [(".Ltoy.toyTwo", 0)] false) 0 entryParts with
    | some s => s
    | none => ""
  let r1 ← leanCheck "entry" (entryFile entry) "Lift.Toys.OuterMem.entry_code'"
  let r2 ← leanCheck "half1" (half1File intro half1) "Lift.Toys.OuterMem.half1_code'"
  let r3 ← leanCheck "framedef" (frameDefFile frameDefText) "Lift.Toys.OuterMem.frameGen_eq"
  let r4 ← leanCheck "hm" (entryHalfFile hmSite) "Lift.Toys.OuterMem.entry_code0"
  pure [("the emitted call site closes entry_code of OuterMem.lean (frame_call), with three standard axioms or bv_decide", r1),
        ("the emitted call site closes half1_code of OuterMem.lean (frame_call, primed names)", r2),
        ("the emitted frame definition gives Frame of OuterMem.lean (Mapped.mono)", r3),
        ("the emitted call site for a callee with room 0 (equation form) closes the entry block", r4)]

/-! ## The report (`--only genframe`) -/

def reportLines : List String :=
  [("spike", spike, "toySum", false), ("spike", spike, "toyJob", true), ("toys", toys, "toyOuter", false),
   ("toys", toys, "toyTwo", false)].map fun (p, c, f, m) =>
    match summaryOf c f rooms m with
    | .ok s => s!"{p} {f}: room {s.frame.room}, delta {s.frame.delta}"
    | .error e => s!"{p} {f}: {toString (repr e)}"

/-- The suite. -/
def run (seed cases : Nat) (only : Option String) : IO Nat := do
  if only.isSome && only != some "genframe" then return 0
  let ouM ← IO.FS.readFile "Lift/Spike/OuterMem.lean"
  let sumS ← IO.FS.readFile "Lift/Spike/Sum.lean"
  let jobS ← IO.FS.readFile "Lift/Spike/Job.lean"
  let mut failed := 0
  for (name, ok) in checks seed cases ouM sumS jobS do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  genframe: {name}"
  for (name, (ok, why)) in (← leanChecks) do
    unless ok do
      failed := failed + 1
      IO.println s!"FAIL  genframe: {name}\n{why}"
  if only == some "genframe" then
    for line in reportLines do
      IO.println s!"info  genframe: {line}"
  return failed

end GenFrameTests
