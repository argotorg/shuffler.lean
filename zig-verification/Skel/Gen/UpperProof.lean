import Skel.Gen.UpperPlan
import Skel.Gen.UpperRel
import Skel.Gen.UpperModel
import Skel.Gen.Model
import Skel.Gen.Frame
import Skel.Render

/-! The proof texts of the rows `refines_l2p` and `above_l2p` (L2 ⇒ L2⁺; `docs/one-way-lift-g3-plan-20261118.md`, section 6;
task G3-10). A text is the tactic block after `:= by` (lines that start at two spaces), a function of the target, the summary
and the plan. The statements of the rows are not made here:

    theorem refines_l2p : Refines SimIn (fun _ _ => Eq) l2p.returns l2.returns                       -- a value
    theorem refines_l2p : Refines SimIn (fun a b r r' => SimOut a b r r'.2) l2p.returns l2.returns    -- a heap
    theorem refines_l2p : Refines SimIn (fun a b r r' => SimOut a b r r') l2p.returns l2.returns      -- both (L3-U3)
    theorem above_l2p : Above l2 l2p

The proofs use the declarations of the generated texts: `blocks`, `blocksP`, `init`, `l2`, `l2p`, `SimIn`, `SimSt`, `SimOut`.

The case of a block (6 shapes: goto, branch, load, store, return, trap) is a function of its accesses and its term:
`simp only [blocksP] at hstep`, then for each access `split at hstep` (the success case goes on; the stuck and the out-of-fuel
cases are `cases hstep`), then the facts of the accesses (`Heap.load_sound`, `Heap.store_frame`), then the exit with the state
of L2 that has the same updates. The names of the hypotheses of the invariant: `hpol` (policy), `hin_<r>` (an input register),
`hh` (the heap holds the memory), `hst_<r>` (a state register), `hmh` and `hmo` (the memory of the state).

Result with a heap (the state has memory). The relation of `Blocks.Returns.sim` is `SimSt` and three more facts: `x.input = a`,
`y.input = b`, and `hown`: each byte that `x.mem` owns is owned by `x.input.heap`. `SimSt` of 4.4 has no such conjunct, and a
store step cannot close without it (risk 10.4 of the plan: it holds, in this form). A store keeps `hown` by
`Heap.Stores.owned`. The rows `refines_l2p` and `above_l2p` do not change.

A store through a register has the guard `Clear y.input.sp addr` in the L2 model (room 0: the private area is the return
word). `SimIn` and `l2p.rep` have the conjunct `harea`: no object of the input heap covers the private area. The guard follows
from `harea`, `hown` and the owned bytes of the store (`owned_of_store`, `covered_of_owned`).

The call form `Fn.CallB` (L3-U8, D40): the model loads with `Heap.loadB` and stores with `Heap.storeB`. `SimIn` has the
conjunct `hperm` (the byte-range permission `Heap.Permits` of the input heap), and with memory the relation of
`Blocks.Returns.sim` has `hpm` (the permission of `x.mem`). A load gives the read by `Heap.loadB_sound`; a store gives the write
by `Heap.storeB_frame`, the owned bytes by `owned_of_storeB` and `Heap.owned_storeB`, and the permission of the new heap by
`Heap.Permits_storeB`. The rows `above_l2p` and `above_l3` carry `hperm` from `l2p.rep` and `l3.rep`.

The result kind `both` (L3-U3) has the texts of a heap result, with the pair: the return proves `SimOut` (the same `rax`
first), and `above_l3` gives the statement's `post` of `l3.post` from the relation of the results of `refines_l3` at the memory
of the return (`UpperRows`).

The stack room (L3-U5, rule 4.3.4). The L2⁺ model drops a push and gives a pop the value that the push stored (`UpperModel.lean`),
as the L2 model does, so the invariant has no stack conjunct. The step of L2⁺ and the step of L2 have a `let` for a pop, which
`simp` and `rfl` unfold. The text of a pop (`StackSrc`) replaces its name `v<k>` in the texts of the block, since the `let`
is gone in the hypothesis `hstep`; a pop of a saved register is `x.input.<r>.toBitVec` and rewrites with `hin_<r>`, and a pop of a
pushed value rewrites with the hypotheses of the registers of that value. `rep` of `l2p` has the room: the hypothesis `hroom`,
the last conjunct, is the room of `l2.rep`.

Not in G3-10 and G3-11, each is an error: a stack room with a heap result or memory in the state; a call; a stack access that
`stackLoads` does not cover; a trap in a branch; a value result with memory; a heap or `both` result with no memory; no block. -/

namespace Skel.Gen

/-! ## Names and small texts -/

/-- The text of `n` spaces and then `l`. -/
private def at' (n : Nat) (l : String) : String := "".pushn ' ' n ++ l

/-- Whether `c` can continue an identifier. -/
private def isIdChar (c : Char) : Bool := c.isAlphanum || c == '_' || c == '\''

/-- The maximal runs of identifier characters and of other characters, in their order. -/
private def runsOf (s : String) : List String :=
  let step : List (String × Bool) → Char → List (String × Bool) := fun acc c =>
    match acc with
    | (w, b) :: rest => if isIdChar c == b then (w.push c, b) :: rest else (c.toString, isIdChar c) :: acc
    | [] => [(c.toString, isIdChar c)]
  ((s.toList.foldl step []).reverse).map (·.1)

/-- The text of a term of the state `x`, as the same term of the state `y` (the L2 state). -/
private def toY (s : String) : String := String.join ((runsOf s).map fun w => if w == "x" then "y" else w)

/-- An anonymous constructor of the parts, or the part when there is one. -/
private def tuple : List String → String
  | [] => "_"
  | [a] => a
  | xs => "⟨" ++ ", ".intercalate xs ++ "⟩"

/-- The projection of conjunct `i` of `n` from a right-nested conjunction, as a suffix: `.1`, `.2.1`, `.2.2`. -/
private def projOf (i n : Nat) : String :=
  if n ≤ 1 then ""
  else if i + 1 == n then String.join (List.replicate i ".2")
  else String.join (List.replicate i ".2") ++ ".1"

/-- The name of the hypothesis `x.input.r = y.input.r` of an input register. -/
private def inHyp (r : Reg64) : String := s!"hin_{regLower r}"

/-- The name of the hypothesis `x.r = y.r` of a state register. -/
private def stHyp (r : Reg64) : String := s!"hst_{regLower r}"

/-- The hypothesis of the register `r` as the block text names it: a state field, else an input. -/
private def regHyp (p : UpperPlan) (r : Reg64) : String :=
  if p.state.any (·.1 == r) then stHyp r else inHyp r

/-- The name of the heap after the store `k` of a block (as `UpperModel.lean`). -/
private def heapName (k : Nat) : String := if k == 0 then "h" else s!"h{k}"

/-! ## Hypotheses of a value

The hypotheses that turn the terms of a value from the state `x` into those of `y`: one for each register that it reads, and,
for a pop, those of its source (`Fwd`). The value of a heap load is a name that the proof binds, and has none. -/

mutual
/-- The hypotheses of the registers that a value reads; `fw k` gives those of the pop `k`. -/
private def valHyps (p : UpperPlan) (fw : Nat → List String) : Val → List String
  | .reg r => [if r == .rsp then "hsp" else regHyp p r]
  | .lit _ => []
  | .load k => fw k
  | .retAddr _ => []
  | .add a b => valHyps p fw a ++ valHyps p fw b
  | .sub a b => valHyps p fw a ++ valHyps p fw b
  | .mul a b => valHyps p fw a ++ valHyps p fw b
  | .shr a _ => valHyps p fw a
  | .zext32 a => valHyps p fw a
  | .and a b | .or a b | .xor a b | .replaceLow _ a b => valHyps p fw a ++ valHyps p fw b
  | .not a | .neg a | .shl a _ | .extract _ _ a _ | .zext _ a | .sext _ a => valHyps p fw a
  | .setcc c => condHyps p fw c
  | .ite c a b => condHyps p fw c ++ valHyps p fw a ++ valHyps p fw b

/-- The hypotheses of the registers that a condition reads. -/
private def condHyps (p : UpperPlan) (fw : Nat → List String) : Cond → List String
  | .eq a b => valHyps p fw a ++ valHyps p fw b
  | .ule a b => valHyps p fw a ++ valHyps p fw b
  | .ult a b => valHyps p fw a ++ valHyps p fw b
  | .slt a b => valHyps p fw a ++ valHyps p fw b
  | .slt32 a b => valHyps p fw a ++ valHyps p fw b
  | .not c => condHyps p fw c
  | .iff q r => condHyps p fw q ++ condHyps p fw r
  | .flag _ => []
end

/-- The pops of a block: for each load that a pop gives, the text that replaces its name and the hypotheses of its registers. -/
private structure Fwd where
  entries : List (Nat × String × List String)

/-- The hypotheses of the pop `k` (none for a heap load). -/
private def Fwd.hyps (f : Fwd) (k : Nat) : List String := ((f.entries.find? (·.1 == k)).map (·.2.2)).getD []

/-- The text `t` with the name of each pop replaced by its value. -/
private def Fwd.sub (f : Fwd) (t : String) : String :=
  f.entries.foldl (fun t (k, txt, _) => renameVar (loadName k) s!"({txt})" t) t

/-- The pops of the block with the context `c`, from their sources: a saved register is the input field and rewrites with the
hypothesis of the input; a pushed value is its text, with the earlier pops replaced, and rewrites with its own hypotheses. -/
private def fwdOf (p : UpperPlan) (c : Ctx) (srcs : List (Nat × StackSrc)) : Fwd :=
  srcs.foldl (init := ⟨[]⟩) fun f (k, src) =>
    match src with
    | .saved r => ⟨f.entries ++ [(k, srcText c src, [inHyp r])]⟩
    | .pushed v => ⟨f.entries ++ [(k, f.sub (srcText c src), valHyps p f.hyps v)]⟩

/-- The rewrites for the hypotheses `hs`, each once. -/
private def rewrites (hs : List String) : List String := hs.eraseDups

/-- The proof that a term of `x` is the same term of `y`: `rfl`, or the rewrites of the hypotheses `hs` of its registers. -/
private def sameTerm (hs : List String) : String :=
  if hs.isEmpty then "rfl" else s!"by simp only [{", ".intercalate (rewrites hs)}]"

/-! ## The invariant -/

/-- The name `hperm` of the byte-range permission of the input heap, for `Fn.CallB` (D40); none for `Fn.Call`. -/
private def permitsNames (p : UpperPlan) : List String := if p.call.bytePermits then ["hperm"] else []

/-- The name `hpm` of the byte-range permission of the memory of the state, for `Fn.CallB` with memory; none otherwise. -/
private def memPermitsNames (p : UpperPlan) : List String := if p.call.bytePermits && p.mem then ["hpm"] else []

/-- The conjuncts of `SimIn` in order: the policy iff the result has a heap, the input registers, the heap, the byte-range
permission of the heap for `Fn.CallB`, and, for a state with memory (a guarded store), `harea`: no object of the heap covers the
private area. -/
private def simInNames (p : UpperPlan) : List String :=
  (if p.kind.hasPolicy then ["hpol"] else []) ++ p.inputs.map inHyp ++ ["hh"] ++ permitsNames p ++
    (if p.mem then ["harea"] else []) ++ (if p.memRoom then ["hbel", "hrm"] else []) ++
    (if p.mem then ["hsp"] else [])

/-- The pattern of `SimSt x y` in `rintro`, and of `sim x y` with the facts of a result that has a heap. -/
private def simPattern (p : UpperPlan) : String :=
  let st := tuple (tuple (simInNames p) :: p.state.map (stHyp ·.1) ++ (if p.mem then ["hmh", "hmo"] else []) ++
    (if p.memRoom then ["hcv", "hroom"] else []))
  if p.mem then s!"⟨{", ".intercalate ([st, "hxa", "hyb", "hown"] ++ memPermitsNames p)}⟩" else st

/-- The relation of `Blocks.Returns.sim` (the argument `sim`). For `Fn.CallB` with memory, the memory of the state has the
byte-range permission (D40): `Heap.loadB_sound` and `Heap.storeB_sound` need it, and `Heap.Permits_storeB` keeps it. -/
private def simRelation (p : UpperPlan) : String :=
  if p.mem then
    let owned := "∀ c, x.mem.Owned c → x.input.heap.Owned c"
    let tail := if p.call.bytePermits then s!"({owned}) ∧ Heap.Permits y.input.policy x.mem" else owned
    s!"(fun x y => SimSt x y ∧ x.input = a ∧ y.input = b ∧ {tail})"
  else "SimSt"

/-- The relation of the results (the argument `simR`). -/
private def resultRelation (p : UpperPlan) : String :=
  match p.kind with
  | .heap => "(fun r r' => SimOut a b r (Prod.snd r'))"
  | .both => "(fun r r' => SimOut a b r r')"
  | .value => if p.mem then "(fun r r' => SimOut a b r r')" else "Eq"

/-- The proof of the invariant at the entry state: `initP a` and `init b`. A state register that is an input is the conjunct
of `SimIn`; the memory is the heap of the input. -/
private def startProof (p : UpperPlan) : String :=
  let n := (simInNames p).length
  let regs := p.state.map fun (r, _) =>
    if p.inputs.contains r then s!"hs{projOf ((simInNames p).idxOf (inHyp r)) n}" else "rfl"
  let proj (h : String) := s!"hs{projOf ((simInNames p).idxOf h) n}"
  let mem := if p.memRoom then [proj "hh", if p.kind == .value then "fun _ _ => rfl" else "fun _ _ _ => rfl", proj "hbel", proj "hrm"]
    else if p.mem then [proj "hh", if p.kind == .value then "rfl" else "fun _ _ => rfl"] else []
  let st := tuple (["hs"] ++ regs ++ mem)
  let perm := (memPermitsNames p).map fun _ => s!"hs{projOf ((simInNames p).idxOf "hperm") n}"
  if p.mem then s!"⟨{", ".intercalate ([st, "rfl", "rfl", "fun _ => id"] ++ perm)}⟩" else st

/-! ## A block -/

/-- The accesses of the block that the heap models have: the stack accesses (the pushes, the pops and the load of the return
word) are not in them. -/
private def heapAccesses (b : Block) : List Access := b.accesses.filter fun a => !(addrOf a).usesRsp

/-- The splits of the accesses of the model: the success case goes on at the indent `ind + 2`; the other two cases of the
result (`.stuck`, `.noFuel`) are `cases hstep`. `inner` gives the lines of the innermost case. -/
private def splitLines : List Access → Nat → (Nat → List String) → List String
  | [], ind, inner => inner ind
  | .load k .. :: rest, ind, inner =>
    [at' ind "split at hstep", at' ind s!"· rename_i {loadName k} hl{k}"] ++ splitLines rest (ind + 2) inner ++
      [at' ind "· cases hstep", at' ind "· cases hstep"]
  | .store k .. :: rest, ind, inner =>
    [at' ind "split at hstep", at' ind s!"· rename_i {heapName k} hst{k}"] ++ splitLines rest (ind + 2) inner ++
      [at' ind "· cases hstep", at' ind "· cases hstep"]

/-- The names of the facts about the current heap of a block: the heap holds the memory (`hh`), and, with memory, the frame
clause and the owned bytes. -/
private structure Facts where
  hh : String
  hf : String
  hown : String
  /-- The byte-range permission of the current heap (`Fn.CallB`, D40); empty for `Fn.Call`. -/
  hp : String
  /-- The names that the step of L2 rewrites with: one fact for each access. -/
  used : List String
  /-- The index of the last store, if the block has one. -/
  lastStore : Option Nat
  /-- A stack room with memory (`UpperPlan.memRoom`): no object of the current heap is in the room, and the current memory has
  the room. -/
  hcv : String := ""
  hroom : String := ""
  /-- The words that the block pushed: the depth and the read of the word in the current memory. -/
  words : List (Int × String) := []

/-- The facts at the start of a block. -/
private def startFacts (p : UpperPlan) : Facts :=
  let hp := if p.call.bytePermits then (if p.mem then "hpm" else "hperm") else ""
  if p.mem then { hh := "hmh", hf := "hmo", hown := "hown", hp, used := [], lastStore := none, hcv := "hcv", hroom := "hroom" }
  else ⟨"hh", "", "", hp, [], none, "", "", []⟩

/-- The premise of the frame clause for the room (`UpperPlan.memRoom`), as in `SimSt`. -/
private def roomPrem (p : UpperPlan) : String := if p.memRoom then s!"¬ SysV.Below y.input.sp {p.room} c → " else ""

/-! ## The facts of a label (PIL-CALL4)

With a stack room with memory (`UpperPlan.memRoom`), a block can pop a word that the entry block pushed. `SimSt` has no stack
words, so the proof uses `Blocks.Returns.simAt` (`Lift/Sem/SimAt.lean`) with one relation for each label: the base relation and,
for each label with facts, `l = .<label> → <facts>`. The facts of the entry label: `y.r = y.input.r` for each saved register `r`
that is a state field (the push writes `y.r`). The facts of each other label: the live words, `readRam … (y.input.sp - d) =
.ok y.input.r.toBitVec` for each word `d` that the entry block saved (`entrySlots`) and that no other block writes. A heap store
keeps a live word (`SysV.readRam_below`), and a push to another word keeps it (`SysV.readRam_push_other`). -/

/-- The facts of the labels. -/
private structure LabelFacts where
  /-- The name of the entry label. -/
  entry : String := "entry"
  /-- The saved registers that are state fields (the facts of the entry label). -/
  ent : List Reg64 := []
  /-- The live words: the depth and the saved register (the facts of each other label). -/
  words : List (Int × Reg64) := []
  /-- The labels with facts, in order, with the texts of their facts over `y`. -/
  labels : List (String × List String) := []

/-- The text of a live word over `y`. -/
private def wordText (mem : String) (d : Int) (r : Reg64) : String :=
  s!"readRam y.input.policy {mem} (y.input.sp - {d.toNat}) .W64 = .ok y.input.{regLower r}.toBitVec"

/-- The hypothesis of the live word at the depth `d`. -/
private def wordHyp (d : Int) : String := s!"hsv{d.toNat}"

/-- The hypothesis of the entry fact of the register `r`. -/
private def entHyp (r : Reg64) : String := s!"hent_{regLower r}"

/-- The context of the block `b`: as the G1 context of a block (`Model.lean`). -/
private def ctxOf (t : Target) (s : Summary) (b : Block) : Ctx :=
  ⟨s.vars, t.entryPC, b.accesses, (s.frame.delta.lookup b.offset).getD 0⟩

/-- The offsets that the term of a block goes to. -/
private def targetsOf (b : Block) : List Nat :=
  (exitsOfTerm b.term).filterMap fun
    | .goto n => some n
    | .call _ c => some c
    | _ => none

/-- The facts of the labels of the summary `s` (none without a stack room with memory). A jump back to the entry label is an
error when the entry label has facts. -/
private def labelFacts (t : Target) (s : Summary) (p : UpperPlan) : Except GenError LabelFacts := do
  let some b0 := s.blocks.head? | return {}
  if !p.memRoom then return {}
  let slots := entrySlots s
  let rest := s.blocks.drop 1
  let written : List Int := rest.flatMap fun b =>
    let c := ctxOf t s b
    b.accesses.filterMap fun
      | .store _ addr _ _ => if addr.usesRsp then depthOf c.depth addr else none
      | .load .. => none
  let words := slots.filter fun (d, _) => !written.contains d
  let ent := (slots.map (·.2)).eraseDups.filter fun r => p.state.any (·.1 == r)
  if ent.any (!p.inputs.contains ·) then
    throw (.unsupported b0.offset "a saved register that is a state field and not an input")
  if !ent.isEmpty && s.blocks.any (fun b => (targetsOf b).contains b0.offset) then
    throw (.unsupported b0.offset "a jump to the entry block, which saves a register of the state")
  let entFacts := ent.map fun r => s!"y.{regLower r} = y.input.{regLower r}"
  let labels := (if ent.isEmpty then [] else [(b0.name.s, entFacts)]) ++
    (if words.isEmpty then [] else rest.map fun b => (b.name.s, words.map fun (d, r) => wordText "y.mem" d r))
  pure { entry := b0.name.s, ent, words, labels }

/-- The conjunct of the label facts in the relation, or none. -/
private def factsConj (lf : LabelFacts) : Option String :=
  if lf.labels.isEmpty then none
  else some (" ∧ ".intercalate (lf.labels.map fun (l, fs) => s!"(l = .{l} → {" ∧ ".intercalate fs})"))

/-- The proof of the label facts at the label `l`, from the proofs `pf` of the facts of `l`: `fun _ => …` for `l`, and
`fun h => nomatch h` for each other label (in parentheses: `nomatch` takes a list of terms). -/
private def factsProof (lf : LabelFacts) (l : String) (pf : List String) : String :=
  let parts := lf.labels.map fun (l', _) => if l' == l then s!"(fun _ => {tuple pf})" else "(fun h => nomatch h)"
  tuple parts

/-- The facts of a stack access of the L2 memory form (`UpperPlan.memRoom`, PIL-CALL3; `Lift/Sem/StackPush.lean`), at the indent
`ind`. A push writes the room (`SysV.RoomAt.push`): `Holds` and the frame clause stay, since the push is outside each object,
and the read of each other pushed word stays (`readRam_push_other`). A pop reads a word that the block pushed; a pop of a word
of another block is an error: the relation of the states has no stack words. A load of the return word or above is not read. -/
private def stackFact (p : UpperPlan) (c : Ctx) (fw : Fwd) (ind : Nat) (b : Block) (lines : List String) (f : Facts) (a : Access) :
    Except GenError (List String × Facts) := do
  let n := p.room
  let dec := "(by decide)"
  match a with
  | .store k addr _ v =>
    let some d := depthOf c.depth addr | throw (.unsupported b.offset "a stack address that is not rsp plus a constant")
    let m := s!"m{k + 1}"
    let others := f.words.filter (·.1 != d)
    let keep := others.map fun (d', h) =>
      (d', at' ind s!"have hrd{k}_{d'.toNat} := SysV.readRam_push_other {h} hw{k} (sp := y.input.sp) (j := {d.toNat}) (k := {d'.toNat}) (n := {n}) (by bv_omega) (by bv_omega) {dec} {dec} {dec} {dec} {dec} {dec}")
    pure (lines ++
      [at' ind s!"obtain ⟨{m}, hw{k}, hroom{k}, hrd{k}, hout{k}⟩ := {f.hroom}.push (a := {toY (fw.sub (paren 1024 (bvText c addr)))}) (k := {d.toNat}) {dec} {dec} {dec} {dec} (by bv_omega) {toY (fw.sub (storeValue c .W64 v))}",
       at' ind s!"have hhs{k} := {f.hh}.push {f.hcv} hout{k}",
       at' ind (if p.kind == .value then
         s!"have hfs{k} : ∀ c, ¬ SysV.Below y.input.sp {n} c → {m}.get? c = y.input.mem.get? c := fun c hb => (hout{k} c hb).trans ({f.hf} c hb)"
         else s!"have hfs{k} : ∀ c, ¬ x.input.heap.Owned c → ¬ SysV.Below y.input.sp {n} c → {m}.get? c = y.input.mem.get? c := fun c hc hb => (hout{k} c hb).trans ({f.hf} c hc hb)")] ++
      keep.map (·.2),
      { f with hh := s!"hhs{k}", hf := s!"hfs{k}", hroom := s!"hroom{k}", used := f.used ++ [s!"hw{k}"], lastStore := some k,
               words := (d, s!"hrd{k}") :: keep.map fun (d', _) => (d', s!"hrd{k}_{d'.toNat}") })
  | .load k addr _ =>
    let some d := depthOf c.depth addr | throw (.unsupported b.offset "a stack address that is not rsp plus a constant")
    if d ≤ 0 then pure (lines, f)
    else match f.words.find? (·.1 == d) with
      | some (_, h) =>
        -- the read at the address text of the pop (`x.input.sp - 24 + 8` for the word at the depth 16)
        let line := at' ind s!"have hp{k} := SysV.readRam_at {h} {toY (fw.sub (paren 1024 (bvText c addr)))} (by bv_omega)"
        pure (lines ++ [line], { f with used := f.used ++ [s!"hp{k}"] })
      | none => throw (.unsupported b.offset s!"a pop of the word at the depth {d} that no live push saved: no push of the block, and no word of the entry block that the other blocks do not write")

/-- The lines that state the facts of the accesses, at the indent `ind`, and the facts after them. A load gives the read of
L2 (`Heap.load_sound`); a store gives the write of L2 and the new facts (`Heap.store_frame`, `Heap.Stores.owned`). For
`Fn.CallB` (D40) the lemmas are those of `loadB` and `storeB` (`Heap.loadB_sound`, `Heap.storeB_frame`, `owned_of_storeB`,
`Heap.owned_storeB`), with the byte-range permission of the heap, which `Heap.Permits_storeB` carries to the heap after a
store. The registers of `x` in a fact are rewritten to those of `y`. A stack access is in the facts only for a room with memory
(`stackFact`); a heap store then also keeps the room and the pushed words (`Heap.store_below`, `Heap.covered_store`). -/
private def factLines (p : UpperPlan) (c : Ctx) (fw : Fwd) (ind : Nat) (b : Block) (accs : List Access)
    (words : List (Int × String)) : Except GenError (List String × Facts) :=
  let regsLine (name : String) (hs : List String) : List String :=
    if hs.isEmpty then [] else [at' ind s!"rw [{", ".intercalate (rewrites hs)}] at {name}"]
  accs.foldlM (init := ([], { startFacts p with words })) fun (lines, f) a =>
    if (addrOf a).usesRsp then
      if p.memRoom then stackFact p c fw ind b lines f a else pure (lines, f)
    else
    match a with
    | .load k addr _ =>
      let sound := if p.call.bytePermits then s!"Heap.loadB_sound {f.hh} {f.hp}" else s!"Heap.load_sound {f.hh}"
      pure (lines ++ [at' ind s!"have hr{k} := {sound} hl{k}"] ++ regsLine s!"hr{k}" (valHyps p fw.hyps addr),
        { f with used := f.used ++ [s!"hr{k}"] })
    | .store k addr w v =>
      let m := s!"m{k + 1}"
      let b := p.call.bytePermits
      let ownedOf := if b then s!"owned_of_storeB {f.hh} hst{k}" else s!"owned_of_store {f.hh} hst{k}"
      let frame := if b then s!"Heap.storeB_frame {f.hh} {f.hp} hst{k}" else s!"Heap.store_frame {f.hh} hst{k}"
      let owned := if b then s!"Heap.owned_storeB hst{k} c" else s!"Heap.Stores.owned (.step _ _ _ hst{k} (.refl _)) c"
      let hbArg := if p.memRoom then " hb" else ""
      let room :=
        if p.memRoom then
          [at' ind s!"have hbl{k} := Heap.store_below hfr{k} {f.hcv}",
           at' ind s!"have hcv{k} : ∀ c, SysV.Below y.input.sp {p.room} c → ¬ Covered {heapName k} c := fun c hb hc => {f.hcv} c hb ((Heap.covered_store hst{k} c).mp hc)",
           at' ind s!"have hroom{k} := {f.hroom}.congr (by decide) hbl{k}"] ++
          f.words.map fun (d, h) =>
            at' ind s!"have hrd{k}_{d.toNat} := SysV.readRam_below {h} (k := {d.toNat}) (n := {p.room}) (by bv_omega) (by decide) (by decide) (by decide) hbl{k}"
        else []
      pure (lines ++
        [at' ind s!"have hcl{k} : {clearText "y" (fw.sub (bvText c addr).1) w} := fun i hi hp => harea _ hp (covered_of_owned ({f.hown} _ ({ownedOf} i hi)))"] ++
        regsLine s!"hcl{k}" (valHyps p fw.hyps addr) ++
        [at' ind s!"obtain ⟨{m}, hw{k}, hhs{k}, hfr{k}⟩ := {frame}"] ++
        regsLine s!"hw{k}" (valHyps p fw.hyps addr ++ valHyps p fw.hyps v) ++
        [at' ind s!"have hfs{k} : ∀ c, ¬ x.input.heap.Owned c → {roomPrem p}{m}.get? c = y.input.mem.get? c := fun c hc{hbArg} => (hfr{k} c fun ho => hc ({f.hown} c ho)).trans ({f.hf} c hc{hbArg})",
         at' ind s!"have hos{k} : ∀ c, {heapName k}.Owned c → x.input.heap.Owned c := fun c hc => {f.hown} c (({owned}).mp hc)"] ++
        (if b then [at' ind s!"have hps{k} := Heap.Permits_storeB hst{k} {f.hp}"] else []) ++ room,
        { f with hh := s!"hhs{k}", hf := s!"hfs{k}", hown := s!"hos{k}", hp := if b then s!"hps{k}" else "",
                 used := f.used ++ [s!"eq_true hcl{k}", "↓reduceIte", s!"hw{k}"], lastStore := some k,
                 hcv := if p.memRoom then s!"hcv{k}" else f.hcv, hroom := if p.memRoom then s!"hroom{k}" else f.hroom,
                 words := if p.memRoom then f.words.map (fun (d, _) => (d, s!"hrd{k}_{d.toNat}")) else f.words })

/-- The registers of the block that the state has, with their values at the block start (`rsp` is not a field). -/
private def updatesOf (p : UpperPlan) (b : Block) : List (Reg64 × Val) :=
  b.regs.filter fun (r, _) => r != .rsp && p.state.any (·.1 == r)

/-- The state of L2 after the block: `y` with the updates of the block, the values with the names of `y` (`Model.lean`
gives the same updates to `x`). -/
private def nextState (c : Ctx) (fw : Fwd) (p : UpperPlan) (b : Block) (f : Facts) : String :=
  let regs := (updatesOf p b).map fun (r, v) => s!"{regLower r} := {toY (fw.sub (u64Text c v).1)}"
  let mem := match f.lastStore with
    | some k => [s!"mem := m{k + 1}"]
    | none => []
  if regs.isEmpty && mem.isEmpty then "y" else "{ y with " ++ ", ".intercalate (mem ++ regs) ++ " }"

/-- The proof of `SimSt x' y'` for the state after the block. A register that the block sets is the equation of its value; any
other keeps its hypothesis. The memory is the facts after the accesses. -/
private def arrival (p : UpperPlan) (fw : Fwd) (b : Block) (f : Facts) : String :=
  let ups := updatesOf p b
  let regs := p.state.map fun (r, _) =>
    match ups.find? (·.1 == r) with
    | some (_, v) => sameTerm (valHyps p fw.hyps v)
    | none => stHyp r
  let mem := if p.mem then [f.hh, f.hf] else []
  let room := if p.memRoom then [f.hcv, f.hroom] else []
  let st := tuple (tuple (simInNames p) :: regs ++ mem ++ room)
  let perm := (memPermitsNames p).map fun _ => f.hp
  if p.mem then s!"⟨{", ".intercalate ([st, "hxa", "hyb", f.hown] ++ perm)}⟩" else st

/-- The proof of `simR r r'` at a return: `x.rax = y.rax` for a value; for a heap, the heap holds the L2 memory and the
bytes outside the input heap are those of the input memory; for both, the equation of `rax` and then the two facts of a heap. -/
private def returnProof (p : UpperPlan) (fw : Fwd) (b : Block) (f : Facts) : String :=
  let heap := [s!"by rw [← hxa, hpol]; exact {f.hh}", s!"by rw [← hxa, ← hyb]; exact {f.hf}"]
  match p.kind with
  | .heap => tuple heap
  | .both => tuple (sameTerm (valHyps p fw.hyps (endVal b .rax)) :: heap)
  | .value =>
    let value := sameTerm (valHyps p fw.hyps (endVal b .rax))
    if p.mem then tuple [value, s!"by rw [← hyb]; exact {f.hf}"] else value

/-- The step of L2 from `y`: `rfl` for a block with no access and no branch; else the rewrite with the facts (and, for a
branch, the condition `hc` with the registers of `y` turned into those of `x`; or, when a register of the condition is in the
address or the value of an access, `hc` with the registers of `x` turned into those of `y`). -/
private def stepProof (p : UpperPlan) (fw : Fwd) (accs : List Access) (f : Facts) (cond : Option Cond) : String :=
  match accs, cond with
  -- a pop of the L2 memory form is a fact in `f.used` with no heap access
  | [], none => if f.used.isEmpty then "rfl" else s!"by simp only [{", ".intercalate ("blocks" :: f.used)}]"
  | _, none => s!"by simp only [{", ".intercalate ("blocks" :: f.used)}]"
  | _, some k =>
    -- a register of the condition that is also in a fact of an access: the rewrite of the goal to `x` would change the term of
    -- the fact, so the condition `hc` is rewritten to `y` instead
    let hs := condHyps p fw.hyps k
    let clash := hs.any fun r => accs.any fun
      | .load _ addr _ => (valHyps p fw.hyps addr).contains r
      | .store _ addr _ v => (valHyps p fw.hyps addr ++ valHyps p fw.hyps v).contains r
    if clash then
      s!"by rw [{", ".intercalate (rewrites hs)}] at hc; simp only [{", ".intercalate ("blocks" :: f.used ++ ["hc", "↓reduceIte"])}]"
    else
      let back := (rewrites hs).map ("← " ++ ·)
      s!"by simp only [{", ".intercalate ("blocks" :: f.used ++ back ++ ["hc", "↓reduceIte"])}]"

/-- The L2 result of a return: `_` (the step proof or the result proof fixes it), or, for both, the pair of `rax` and the memory
after the stores: the `simp` of a step with accesses does not fix a result that the proof of `SimOut` reads only by its parts.
A value result that is not a name or a literal is the term of `rax` with the registers of `y`. -/
private def l2Result (c : Ctx) (fw : Fwd) (p : UpperPlan) (b : Block) (f : Facts) : String :=
  match p.kind with
  | .both =>
    let mem := match f.lastStore with
      | some k => s!"m{k + 1}"
      | none => "y.mem"
    s!"({toY (fw.sub (u64Text c (endVal b .rax)).1)}, {mem})"
  | .value =>
    -- a term with a space (an `if`, a sum, a load): the `simp` of the step does not fix it either
    let v := toY (fw.sub (u64Text c (endVal b .rax)).1)
    if p.mem then s!"({v}, {match f.lastStore with | some k => s!"m{k + 1}" | none => "y.mem"})"
    else if v.any (· == ' ') then s!"({v})" else "_"
  | .heap => "_"

/-- The `exact` term of an exit. A trap in a branch is an error. -/
private def exitProof (s : Summary) (lf : LabelFacts) (p : UpperPlan) (c : Ctx) (fw : Fwd) (b : Block) (accs : List Access)
    (f : Facts) (cond : Option Cond) : Exit → Except GenError String
  | .goto n => do
    let st := arrival p fw b f
    let st ← if lf.labels.isEmpty then pure st else do
      let l := lblOf s n
      -- the live words at `l`: each is a word of the current memory; a word that the entry block pushed from a state field
      -- has the value of the field, which the entry fact rewrites to the input
      let pf ← if lf.labels.any (·.1 == l) then lf.words.mapM fun (d, r) => do
          let some (_, h) := f.words.find? (·.1 == d)
            | throw (.unsupported b.offset s!"the word at the depth {d} is not live at the end of {b.name.s}")
          pure (if b.name.s == lf.entry && lf.ent.contains r then s!"(by rw [{entHyp r}] at {h}; exact {h})" else h)
        else pure []
      pure s!"⟨{st}, {factsProof lf l pf}⟩"
    pure (tuple [nextState c fw p b f, stepProof p fw accs f cond, st])
  | .ret => pure (tuple [l2Result c fw p b f, stepProof p fw accs f cond, returnProof p fw b f])
  | .trap => throw (.unsupported b.offset "a trap in a branch at L2+ (the type Next has no stuck)")
  | .call .. => throw (.unsupported b.offset "a call in a branch at L2+")

/-! ## A call (PIL-CALL4)

The call of a callee `F` with memory and room 0 (`upperCallees`, `UpperModel.lean`; a callee with no memory: `callLinesNoMem`). The callee fact of `Blocks.Returns.simAt` is
`Lift.Sem.CallArm.callee` from the callee rows `F.refines_l2p` and `F_shape` (the heap of a result covers and owns the bytes
of the input heap). The relation of the callee inputs is `F.SimIn` and that the callee heap does not own the `K` kept bytes
(`keptBytes`); the relation of the results is `F.SimOut` and the shape. The arm of the block of the call gives the L2 call,
the inputs of `F` (`CallArm.free_callee`: the return word of the call is in the room) and the kept bytes (`CallArm.free`);
after the call, the facts of the caller from `CallArm.cont`, and the live words from `CallArm.word`. -/

/-- The relation of the inputs, the relation of the results and the callee fact of `Blocks.Returns.simAt` for the callee `c`
of a summary with the kept bytes `k`, as functions of the inputs and the results. With memory: the order facts of `F.SimIn` and
`F.SimOut` take the conjuncts of the generated forms apart (the policy, the inputs, the heap, the private area; the value, the
heap, the frame clause), and the fact is `CallArm.callee`. With no memory: `F.SimIn`, the equation of the values, and the row
`F.refines_l2p`. -/
private def calleeParts (p : UpperPlan) (c : Callee) (k : Nat) : String × String × String :=
  let f := c.model
  -- Resolve the field through the exported input type. Its namespace may also
  -- contain a different In2p structure in a parent scope.
  if c.heapWrites then
    let regs := c.inputs.map fun r => s!"hr_{regLower r}"
    let perms := if p.call.bytePermits then ["hperm"] else []
    let permsOut := if p.call.bytePermits then ["(Heap.Permits_perm hp).mp hperm"] else []
    let hX := s!"(fun _ _ _ hp ⟨{", ".intercalate (["h0"] ++ regs ++ ["hh"] ++ perms ++ ["ha", "hsp"])}⟩ => ⟨{", ".intercalate (["h0"] ++ regs ++ ["(Heap.Holds_perm hp).mp hh"] ++ permsOut ++ ["fun c hc hv => ha c hc ((covered_perm hp c).mpr hv)", "hsp"])}⟩)"
    let shape := if p.call.bytePermits then "ShapeB" else "Shape"
    let rule := if p.call.bytePermits then "calleeB" else "callee"
    let hY := "(fun _ _ _ _ _ _ hp hp' ⟨h1, hh, hf⟩ => ⟨h1, (Heap.Holds_perm hp').mpr hh, fun c hc => hf c fun ho => hc ((Heap.owned_perm hp c).mpr ho)⟩)"
    (s!"(fun (x : {f}.In2p) (xl : {f}.In2) => {f}.SimIn x xl ∧ ∀ i, i < {k} → ¬ x.heap.Owned (xl.sp + BitVec.ofNat 64 i))",
     s!"(fun (x : {f}.In2p) (xl : {f}.In2) y yl => {f}.SimOut x xl y yl ∧ Lift.Sem.CallArm.{shape} x.heap y.2)",
     s!"(Lift.Sem.CallArm.{rule} (fun (x : {f}.In2p) => x.heap) (fun x k => \{ x with heap := k }) (fun (x : {f}.In2) => x.sp) (fun (x : {f}.In2) => x.mem) {k} (fun _ _ => rfl) {f}.refines_l2p {hX} {hY} (fun _ _ _ _ ⟨_, _, hf⟩ => hf) {f}.shape)")
  else if c.mem then
    (s!"(fun (x : {f}.In2p) (xl : {f}.In2) => {f}.SimIn x xl)",
     s!"(fun (x : {f}.In2p) (xl : {f}.In2) (y : UInt64) (yl : UInt64 × DataMem) => {f}.SimOut x xl y yl)",
     s!"{f}.refines_l2p")
  else
    (s!"(fun (x : {f}.In2p) (xl : {f}.In2) => {f}.SimIn x xl)",
     s!"(fun (_ : {f}.In2p) (_ : {f}.In2) (y : UInt64) (yl : UInt64) => y = yl)",
     s!"{f}.refines_l2p")

/-- The callee arguments of `Blocks.Returns.simAt` for the callees `cs` of the summary `s`: the named arguments of the callee
relations (two or more callees), `simX simY`, and the callee fact. One callee has the families `fun _ => …`; two or more the
matches over `Cal`. The kept bytes of a callee with memory are those of the continuation of its call. -/
private def calleeArgs (s : Summary) (p : UpperPlan) (cs : List Callee) : String × String :=
  let kOf (c : Callee) : Nat := keptBytes s ((s.blocks.findSome? fun (b : Block) => match b.term with
    | .exit (.call g k) => if g == c.name then some k else none
    | _ => none).getD 0)
  let parts := cs.map fun c => calleeParts p c (kOf c)
  match parts with
  | [(x, y, f)] => (s!"(fun _ => {x}) (fun _ => {y})", s!" (fun _ => {f})")
  | _ =>
    let arms (g : String × String × String → String) : String :=
      String.join (parts.zipIdx.map fun (q, i) => s!" | .c{i} => {g q}")
    (s!"(calleeHi := CalP.rel) (calleeLo := fun c => (Cal.model c).returns) " ++
      s!"(fun{arms (·.1)} : (c : Cal) → CalP.In c → Cal.In c → Prop) " ++
      s!"(fun{arms (·.2.1)} : (c : Cal) → CalP.In c → Cal.In c → CalP.Out c → Cal.Out c → Prop)",
     s!" (fun{arms (·.2.2)})")

/-- The lines of the exit of a block that calls the callee `cl` with no memory and goes on at `cont`, at the indent `ind`
(MULTI-CALLEE2): the L2 call with the inputs of `F.SimIn`; after the call the value is the result, and the heap, the memory
and the facts of the caller are those at the call. -/
private def callLinesNoMem (s : Summary) (lf : LabelFacts) (p : UpperPlan) (c : Ctx) (fw : Fwd) (b : Block)
    (accs : List Access) (f : Facts) (cl : Callee) (cont : Nat) (ind : Nat) : Except GenError (List String) := do
  if cl.mem then throw (.unsupported b.offset s!"a value call of {cl.name} with exact output memory: no generated proof text")
  if !p.memRoom then throw (.unsupported b.offset "a call at L2+ with no stack room with memory")
  let mem := match f.lastStore with
    | some k => s!"m{k + 1}"
    | none => "y.mem"
  let args := cl.inputs.map fun r => toY (fw.sub (u64Text c (endVal b r)).1)
  let argHyps := cl.inputs.map fun r => sameTerm (valHyps p fw.hyps (endVal b r))
  let upd := (callUpdates b).reverse
  let st := (upd.map fun (r, v) => s!"{regLower r} := {toY (fw.sub (u64Text c v).1)}") ++
    (if f.lastStore.isSome then [s!"mem := {mem}"] else []) ++ ["rax := r"]
  let l := lblOf s cont
  let x' := "⟨" ++ ", ".intercalate (["y.input.policy", mem] ++ args) ++ "⟩"
  let k' := s!"fun r => (.{l}, \{ y with {", ".intercalate st} })"
  let simIn := tuple (argHyps ++ [f.hh] ++ (if p.call.bytePermits then [f.hp] else []))
  let regs := p.state.map fun (r, _) =>
    if r == .rax then "hr1"
    else match upd.find? (·.1 == r) with
      | some (_, v) => sameTerm (valHyps p fw.hyps v)
      | none => stHyp r
  let base := tuple (tuple (simInNames p) :: regs ++ [f.hh, f.hf, f.hcv, f.hroom])
  let simSt := s!"⟨{", ".intercalate ([base, "hxa", "hyb", f.hown] ++ (memPermitsNames p).map fun _ => f.hp)}⟩"
  let words ← if lf.labels.any (·.1 == l) then lf.words.mapM fun (dd, r) => do
      let some (_, h) := f.words.find? (·.1 == dd)
        | throw (.unsupported b.offset s!"the word at the depth {dd} is not live at the call in {b.name.s}")
      pure (if b.name.s == lf.entry && lf.ent.contains r then s!"(by rw [{entHyp r}] at {h}; exact {h})" else h)
    else pure []
  let after := if lf.labels.isEmpty then simSt else s!"⟨{simSt}, {factsProof lf l words}⟩"
  pure [at' ind s!"refine ⟨{x'}, {k'}, {stepProof p fw accs f none}, {simIn}, ?_⟩",
    at' ind "rintro r r' hr1",
    at' ind s!"exact ⟨rfl, {after}⟩"]

/-- The lines of the exit of a block that calls the callee `cl` and goes on at `cont`, at the indent `ind`. -/
private def callLines (s : Summary) (lf : LabelFacts) (p : UpperPlan) (c : Ctx) (fw : Fwd) (b : Block) (accs : List Access)
    (f : Facts) (cl : Callee) (cont : Nat) (ind : Nat) : Except GenError (List String) := do
  if !p.memRoom then throw (.unsupported b.offset "a call at L2+ with no stack room with memory")
  let some d := depthOf c.depth (endVal b .rsp) | throw (.unsupported b.offset "a call with rsp that is not rsp plus a constant")
  let n := p.room
  let dec := "(by decide)"
  let mem := match f.lastStore with
    | some k => s!"m{k + 1}"
    | none => "y.mem"
  let args := cl.inputs.map fun r => toY (fw.sub (u64Text c (endVal b r)).1)
  let argHyps := cl.inputs.map fun r => sameTerm (valHyps p fw.hyps (endVal b r))
  let upd := (callUpdates b).reverse
  let st := (upd.map fun (r, v) => s!"{regLower r} := {toY (fw.sub (u64Text c v).1)}") ++ ["mem := r.2", "rax := r.1"]
  let l := lblOf s cont
  -- the `rsp` of the call as the L2 model writes it (`x.input.sp - 8 - 8` in a block at the depth 8)
  let x' := "⟨" ++ ", ".intercalate (["y.input.policy", mem, toY (fw.sub (bvText c (endVal b .rsp)).1)] ++ args) ++ "⟩"
  let k' := s!"fun r => (.{l}, \{ y with {", ".intercalate st} })"
  let simIn := tuple (["hpol"] ++ argHyps ++ [f.hh] ++ (if p.call.bytePermits then [f.hp] else []) ++ [s!"Lift.Sem.CallArm.free_callee {f.hcv} (n := {n}) (d := {d.toNat}) (by bv_omega) {dec} {dec} {dec}",
    sameTerm (valHyps p fw.hyps (endVal b .rsp))])
  let free := s!"Lift.Sem.CallArm.free harea {f.hown} (sp := y.input.sp) (n := {n}) (d := {d.toNat}) (by bv_omega) {dec} {dec} {dec}"
  let regs := p.state.map fun (r, _) =>
    if r == .rax then "hr1"
    else match upd.find? (·.1 == r) with
      | some (_, v) => sameTerm (valHyps p fw.hyps v)
      | none => stHyp r
  let base := tuple (tuple (simInNames p) :: regs ++ ["(hpol ▸ hrh : _)", "hfsC", "hcvC", "hroomC"])
  let simSt := s!"⟨{", ".intercalate ([base, "hxa", "hyb", "hosC"] ++ (memPermitsNames p).map fun _ => "hpermC")}⟩"
  let words ← if lf.labels.any (·.1 == l) then lf.words.mapM fun (dd, r) => do
      let some (_, h) := f.words.find? (·.1 == dd)
        | throw (.unsupported b.offset s!"the word at the depth {dd} is not live at the call in {b.name.s}")
      let w := s!"Lift.Sem.CallArm.word {f.hcv} hrf {h} (k := {dd.toNat}) {dec} {dec} {dec} rfl"
      pure (if b.name.s == lf.entry && lf.ent.contains r then s!"(by have hw := {w}; rw [{entHyp r}] at hw; exact hw)" else s!"({w})")
    else pure []
  let after := if lf.labels.isEmpty then simSt else s!"⟨{simSt}, {factsProof lf l words}⟩"
  pure ([at' ind s!"refine ⟨{x'}, {k'}, {stepProof p fw accs f none}, ⟨{simIn}, {free}⟩, ?_⟩",
    at' ind "rintro r r' ⟨⟨hr1, hrh, hrf⟩, hsh⟩"] ++
    (if p.call.bytePermits then [at' ind s!"have hpermC := hsh.2 _ {f.hp}", at' ind "have hsh := hsh.1"] else []) ++
    [at' ind s!"obtain ⟨hfsC, hosC, hcvC, hroomC⟩ := Lift.Sem.CallArm.cont {f.hf} {f.hown} {f.hcv} {f.hroom} {dec} hrf hsh",
    at' ind s!"exact ⟨rfl, {after}⟩"])

/-- The case of the block `b` in `cases l with` (4.3 of the plan; section 6). -/
private def armLines (t : Target) (s : Summary) (p : UpperPlan) (lf : LabelFacts) (cal : List Callee) (b : Block) :
    Except GenError (List String) := do
  let c := ctxOf t s b
  -- the pops: `stackLoads` checks the stack accesses, and the heap accesses are the others
  let fw := fwdOf p c (← stackLoads (entrySlots s) c b)
  let accs := heapAccesses b
  if !p.mem && accs.any (fun | .store .. => true | .load .. => false) then
    throw (.unsupported b.offset "a store in a function with no memory in its state")
  -- the facts of the label (PIL-CALL4): `hwd` at this label
  let lfs := lf.labels.length
  let own := match lf.labels.findIdx? (·.1 == b.name.s), lf.labels.find? (·.1 == b.name.s) with
    | some i, some (_, fs) =>
      let names := if b.name.s == lf.entry then lf.ent.map entHyp else lf.words.map (wordHyp ·.1)
      [at' 4 s!"have {if names.length == 1 then names.headD "hlf" else "hlf"} : {" ∧ ".intercalate fs} := hwd{projOf i lfs} rfl"] ++
        (if names.length > 1 then [at' 4 s!"obtain {tuple names} := hlf"] else [])
    | _, _ => []
  let head := at' 2 s!"| {b.name.s} =>"
  let ind := 4 + 2 * accs.length
  -- a room with memory: the stack accesses are in the facts (`stackFact`), and the splits are those of the heap accesses
  let words := if b.name.s == lf.entry || !lf.labels.any (·.1 == b.name.s) then [] else lf.words.map fun (d, _) => (d, wordHyp d)
  let (facts, f) ← factLines p c fw ind b (if p.memRoom then b.accesses else accs) words
  match b.term with
  | .exit .trap =>
    -- both models are `stuck`: the step of L2⁺ is not a result
    pure ([head] ++ own ++ [at' 4 "simp only [blocksP] at hstep"] ++ splitLines accs 4 fun i => [at' i "cases hstep"])
  | term =>
    let top :=
      if accs.isEmpty then at' 4 "simp only [blocksP, Res.ok.injEq] at hstep" else at' 4 "simp only [blocksP] at hstep"
    let pre := (if accs.isEmpty then [] else [at' ind "simp only [Res.ok.injEq] at hstep"]) ++ [at' ind "subst hstep"]
    let exits ← match term with
      | .exit (.call g cont) => do
        let some cl := cal.find? (·.name == g) | throw (.unsupported b.offset s!"a call of {g} at L2+ with no callee")
        if cl.heapWrites then callLines s lf p c fw b accs f cl cont ind else callLinesNoMem s lf p c fw b accs f cl cont ind
      | .exit e => do pure [at' ind s!"exact {← exitProof s lf p c fw b accs f none e}"]
      | .branch k y n => do
        let ey ← exitProof s lf p c fw b accs f (some k) y
        let en ← exitProof s lf p c fw b accs f (some k) n
        let condition := fw.sub (propText c k).1
        -- `split` descends into an `if` inside the condition. In that case, select the
        -- outer condition explicitly. Otherwise, reuse the condition already in the goal.
        -- Neither form rewrites equal load values in the state.
        if (runsOf condition).contains "if" then
          pure [at' ind s!"by_cases hc : {condition}",
            at' ind "· rw [ite_eq_left hc]", at' (ind + 2) s!"exact {ey}",
            at' ind "· rw [ite_eq_right hc]", at' (ind + 2) s!"exact {en}"]
        else
          pure [at' ind "split",
            at' ind "· rename_i hc", at' (ind + 2) s!"exact {ey}",
            at' ind "· rename_i hc", at' (ind + 2) s!"exact {en}"]
    pure ([head] ++ own ++ [top] ++ splitLines accs 4 fun _ => pre ++ facts ++ exits)

/-! ## The rows -/

/-- Why a function has no text, or `none` when it has one. -/
private def refusal (s : Summary) (p : UpperPlan) : Option GenError :=
  if s.frame.room != p.room then
    some (.shape 0 s!"the plan has a stack room of {p.room} bytes, the summary {s.frame.room}")
  else if s.vars.mem != p.mem then
    some (.shape 0 "the plan and summary have different memory state flags")
  else if p.privateStack then
    some (.unsupported 0 "private stack bytes: no generated proof text")
  else if p.stackArgs > 0 then
    some (.unsupported 0 "stack arguments: no generated proof text")
  else if let some why := roomRefusal p.room p.mem p.kind then some (.unsupported 0 why)
  else if s.blocks.isEmpty then some (.shape 0 "a function with no block has no case text")
  else if p.kind == .heap && !p.mem then some (.unsupported 0 "a heap result with no memory in the state has no proof text")
  else if p.kind == .both && !p.mem then
    some (.unsupported 0 "a result that is a value and a heap (both) with no memory in the state has no proof text")
  else none

/-- The tactic block of `refines_l2p` for the target `t`, the summary `s` and the plan `p`. -/
def refinesProof (t : Target) (s : Summary) (p : UpperPlan) : Except GenError String := do
  if let some e := refusal s p then throw e
  let cal ← upperCallees t s
  if let some cl := cal.find? (fun cl => cl.heapWrites && 0 < cl.room) then
    throw (.unsupported 0 s!"a heap call of {cl.name} with a stack room: no generated proof text")
  let lf ← labelFacts t s p
  let arms ← s.blocks.mapM (armLines t s p lf cal)
  let (callee, calleeFact) := if cal.isEmpty then ("(fun f => f.elim) (fun f => f.elim)", " (fun f => f.elim)")
    else calleeArgs s p cal
  let head := match factsConj lf, cal with
    | none, _ :: _ => [
      at' 2 "intro a b r hs h",
      at' 2 s!"refine Blocks.Returns.simAt {callee} (fun _ => {simRelation p}) {resultRelation p}{calleeFact} ?_ h",
      at' 4 s!"(y := init b) {startProof p}",
      at' 2 s!"rintro l x y n {simPattern p} hstep",
      at' 2 "cases l with" ]
    | none, [] => [
      at' 2 "intro a b r hs h",
      at' 2 s!"refine Blocks.Returns.sim (fun f => f.elim) (fun f => f.elim) {simRelation p} {resultRelation p} (fun f => f.elim) ?_ h",
      at' 4 s!"(y := init b) {startProof p}",
      at' 2 s!"rintro l x y n {simPattern p} hstep",
      at' 2 "cases l with" ]
    | some fc, _ =>
      -- one relation for each label (PIL-CALL4): the base relation and the facts of the labels
      let base := (simRelation p).drop "(fun x y => ".length |>.dropRight 1
      let base := if p.mem then base else "SimSt x y"
      [ at' 2 "intro a b r hs h",
        at' 2 s!"refine Blocks.Returns.simAt {callee} (fun l x y => ({base}) ∧ {fc}) {resultRelation p}{calleeFact} ?_ h",
        at' 4 s!"(y := init b) ⟨{startProof p}, {factsProof lf lf.entry (lf.ent.map fun _ => "rfl")}⟩",
        at' 2 s!"rintro l x y n ⟨{simPattern p}, hwd⟩ hstep",
        at' 2 "cases l with" ]
  pure ("\n".intercalate (head ++ arms.flatten))

/-! ## The shape row of a callee (PIL-CALL5)

The row `shape : ∀ a r, l2p.returns a r → Lift.Sem.CallArm.Shape a.heap r.2` of a function with memory and a result of a value
and a heap: the heap of each result covers and owns the bytes of the input heap. A caller of the function needs it
(`CallArm.callee`): the `SimOut` texts do not say it. The proof is `Blocks.Returns.inv` with the invariant
`Shape a.heap x.mem`; each heap store keeps it (`Shape.store`). Scalar callees keep the heap.
A heap result uses the callee's checked shape row and its input and output permutations. -/

/-- The statement of the row `shape`. -/
def shapeStatementFor (bytePermits : Bool) : String :=
  s!"∀ a r, l2p.returns a r → Lift.Sem.CallArm.{if bytePermits then "ShapeB" else "Shape"} a.heap r.2"

def shapeStatement : String := shapeStatementFor false

/-- Only partial accesses need a case split. Private stack stores are total; private loads below
the return word can fail. Stack arguments and the return word have no result match. -/
private def shapeAccesses (s : Summary) (p : UpperPlan) (b : Block) : List Access :=
  let depth := (s.frame.delta.lookup b.offset).getD 0
  b.accesses.filter fun a =>
    if !(addrOf a).usesRsp then true
    else if !p.privateStack then false
    else match a with
      | .load _ addr _ => (stackArg depth a).isNone && (depthOf depth addr).any (0 < ·)
      | .store .. => false

/-- Pass register expressions as arguments to a checked constructor lemma. Direct conversion
from `Next.Inv` to a heap projection can exceed the kernel's memory with word arithmetic. -/
private def shapeGoto (p : UpperPlan) (topLevel : Bool := false) : List String :=
  let shape := if p.call.bytePermits then "ShapeB" else "Shape"
  let regs := p.state.map fun (r, _) => regLower r
  let flags := p.flags.map (·.name)
  let fields := " ".intercalate (["input"] ++ regs ++ flags ++ ["mem"])
  let state := if p.privateStack then s!"(StP.mk (St.mk {fields}) stack)" else s!"(St.mk {fields})"
  let binders := ["{input : In2p}"] ++
    (if regs.isEmpty then [] else ["{" ++ " ".intercalate regs ++ " : UInt64}"]) ++
    (if flags.isEmpty then [] else ["{" ++ " ".intercalate flags ++ " : Bool}"]) ++
    ["{mem : Heap}"] ++ (if p.privateStack then ["{stack : Lift.Sem.PrivateStack}"] else [])
  let stateTy := if p.privateStack then "StP" else "St In2p Heap"
  let indent := if topLevel then 0 else 2
  [at' indent ((if topLevel then "theorem" else "have") ++
     " shape_goto {F : Type} {X Y : F → Type} {callee : ∀ f, X f → Y f → Prop}"),
   at' (indent + 2) "{Q : UInt64 × Heap → Prop} {heap : Heap} {l : Lbl}",
   at' (indent + 2) (" ".intercalate binders),
   at' (indent + 2) s!"(hs : Lift.Sem.CallArm.{shape} heap mem) :",
   at' (indent + 2) s!"Lift.Sem.CallArm.Next.Inv (fun (_ : Lbl) (x : {stateTy}) => Lift.Sem.CallArm.{shape} heap x.mem) Q callee",
   at' (indent + 4) s!"(.goto l {state}) := hs"]

/-- The case of the block `b` in the proof of the row `shape`. -/
private def shapeStep (s : Summary) (p : UpperPlan) (callees : List Callee) (b : Block) : Except GenError (List String) := do
  let accs := shapeAccesses s p b
  let shape := if p.call.bytePermits then "ShapeB.storeB" else "Shape.store"
  let chain := (accs.filterMap fun | .store k .. => some k | .load .. => none).foldl
    (fun acc k => s!"(Lift.Sem.CallArm.{shape} {acc} hst{k})") "hsh"
  let closeExit (exit : Exit) : Except GenError (List String) := do
    match exit with
    | .call name _ =>
      let some callee := callees.find? (·.name == name)
        | throw (.unsupported b.offset s!"the shape row has no interface for callee {name}")
      if callee.heapWrites then
        pure ["intro y hy", "rcases hy with ⟨k, k', hr, hp⟩",
          s!"exact {chain}.trans (({callee.model}.shape _ _ hr).perm hp.perm_in hp.perm_out)"]
      else pure ["intro y hy", s!"exact {chain}"]
    | .trap => throw (.unsupported b.offset "the shape row of a branch with a trap")
    | .goto _ => pure [s!"exact shape_goto {chain}"]
    | _ => pure [s!"exact {chain}"]
  let branchArm : List String → List String
    | [] => []
    | first :: rest => ("· " ++ first) :: rest.map ("  " ++ ·)
  let close ← match b.term with
    | .exit .trap => pure none
    | .exit exit => some <$> closeExit exit
    | .branch _ y n => do
      -- Keep arm constructors opaque when matching the outer condition. Default reduction
      -- can expand the word encoding of a shift before it finds the branch arguments.
      pure (some (["with_reducible refine shape_branch (Q := Lift.Sem.CallArm.Next.Inv _ _ _) ?_ ?_"] ++
        branchArm (← closeExit y) ++ branchArm (← closeExit n)))
  let top := if accs.isEmpty then at' 2 "simp only [blocksP, Res.ok.injEq] at hstep" else at' 2 "simp only [blocksP] at hstep"
  let inner (ind : Nat) : List String := match close with
    | none => [at' ind "cases hstep"]
    | some c => (if accs.isEmpty then [] else [at' ind "simp only [Res.ok.injEq] at hstep"]) ++
      [at' ind "subst hstep"] ++ c.map (at' ind)
  match b.term, accs with
  | .exit .trap, [] => pure [at' 2 "simp only [blocksP] at hstep", at' 2 "cases hstep"]
  | _, _ => pure ([top] ++ splitLines accs 2 inner)

private def shapeArm (s : Summary) (p : UpperPlan) (callees : List Callee) (b : Block) : Except GenError (List String) := do
  pure ([at' 2 s!"| {b.name.s} =>"] ++ (← shapeStep s p callees b).map (at' 2))

/-- The tactic block of the row `shape` for the summary `s` and the plan `p`. -/
def shapeProof (s : Summary) (p : UpperPlan) (callees : List Callee := []) : Except GenError String := do
  if p.kind != .both || !p.mem then throw (.unsupported 0 "the shape row of a function with no memory and no result of a value and a heap")
  if s.blocks.isEmpty then throw (.shape 0 "a function with no block has no case text")
  let arms ← s.blocks.mapM (shapeArm s p callees)
  let shape := if p.call.bytePermits then "ShapeB" else "Shape"
  pure ("\n".intercalate (shapeGoto p ++ [
    at' 2 "have shape_branch {α : Type} {P : Prop} [Decidable P] {yes no : α}",
    at' 4 "{Q : α → Prop} (hy : Q yes) (hn : Q no) : Q (if P then yes else no) := by",
    at' 4 "split <;> assumption",
    at' 2 "intro a r h",
    at' 2 (s!"refine Lift.Sem.CallArm.Blocks.Returns.inv (fun _ x => Lift.Sem.CallArm.{shape} a.heap x.mem) " ++
      s!"(fun r => Lift.Sem.CallArm.{shape} a.heap r.2) ?_ h (Lift.Sem.CallArm.{shape}.refl _)"),
    at' 2 "rintro l x n hsh hstep",
    at' 2 "cases l with"] ++ arms.flatten))

/-- Check each block's heap shape in a separate theorem. The final induction
only applies these theorems, so its command budget excludes their calculations.
Helper declarations stay in the proof's frozen scope. -/
def shapeProofParts (s : Summary) (p : UpperPlan) (interfaces : List Callee := []) : Except GenError Proof := do
  if p.kind != .both || !p.mem then throw (.unsupported 0 "the shape row of a function with no memory and no result of a value and a heap")
  if s.blocks.isEmpty then throw (.shape 0 "a function with no block has no case text")
  let callees ← (calledOf s.blocks).mapM fun name => do
    let some c := interfaces.find? (·.name == name)
      | throw (.unsupported 0 s!"the shape row has no interface for callee {name}")
    pure c
  let rel := if callees.isEmpty then "noCall" else calleeRel callees
  let shape := s!"Lift.Sem.CallArm.{if p.call.bytePermits then "ShapeB" else "Shape"}"
  let steps ← s.blocks.mapM fun b => do
    let body ← shapeStep s p callees b
    pure ("\n".intercalate ([
      s!"theorem shape_step_{b.name.s} (heap : Heap) (x : {p.stateType})" ++ " {n}",
      s!"    (hsh : {shape} heap x.mem)",
      s!"    (hstep : blocksP.step .{b.name.s} x = .ok n) :",
      "    Lift.Sem.CallArm.Next.Inv",
      s!"      (fun (_ : Lbl) (x : {p.stateType}) => {shape} heap x.mem)",
      s!"      (fun r => {shape} heap r.2) {rel} n := by"] ++ body))
  let helpers := "\n\n".intercalate (["\n".intercalate (shapeGoto p true),
    "theorem shape_branch {α : Type} {P : Prop} [Decidable P] {yes no : α}\n" ++
      "  {Q : α → Prop} (hy : Q yes) (hn : Q no) : Q (if P then yes else no) := by\n" ++
      "  split <;> assumption"] ++ steps)
  let proof := "\n".intercalate (["by", "  intro a r h",
    s!"  refine Lift.Sem.CallArm.Blocks.Returns.inv (fun _ x => {shape} a.heap x.mem) " ++
      s!"(fun r => {shape} a.heap r.2) ?_ h ({shape}.refl _)",
    "  rintro l x n hsh hstep", "  cases l with"] ++
    s.blocks.map fun b => s!"  | {b.name.s} => exact shape_step_{b.name.s} a.heap x hsh hstep")
  pure { helpers, proof }

/-- The tactic block of `above_l2p` for the summary `s` and the plan `p`. -/
def aboveProof (s : Summary) (p : UpperPlan) : Except GenError String := do
  if let some e := refusal s p then throw e
  let regHyps := p.inputs.map fun r => s!"hr_{regLower r}"
  let hasPol := p.kind.hasPolicy
  let sp := if p.mem then ["s.data.regs.rsp.toBitVec"] else []
  let room := if p.room == 0 then [] else ["hroom"]
  -- PIL-HEAP: a frame that reads the heap has the L2 input memory `SysV.hide s <room>`; the heap holds in it, since no object
  -- meets the room (`hbelow`)
  let mem := if p.hide then s!"SysV.hide s {p.room}" else "s.data.dmem"
  let b := tuple (["policy", mem] ++ sp ++ p.inputs.map fun r => s!"a.{regLower r}")
  -- the L2 model has `True` for the input memory of a function that does not read it and uses the stack (G1-16)
  let memRep := if p.hide then s!"SysV.hide_hidden s {p.room}" else if pinsInputMem s then "rfl" else "trivial"
  let bRep := tuple (["rfl", memRep, "he"] ++ regHyps ++ (if p.mem then ["rfl"] else []) ++ room)
  let hh := if p.hide then s!"(holds_congr hh fun c hc => (SysV.hide_hidden s {p.room}).1 c fun hb => hbelow c hb hc)" else "hh"
  let simIn := tuple ((if hasPol then ["hpol"] else []) ++ p.inputs.map (fun _ => "rfl") ++ [hh] ++ permitsNames p ++
    (if p.mem then ["harea"] else []) ++ (if p.memRoom then ["hbelow", "hroom"] else []) ++
    (if p.mem then ["hsp"] else []))
  let simY := match p.kind with
    | .heap => "(fun _ _ a b r r' => SimOut a b r (Prod.snd r'))"
    | .both => "(fun _ _ a b r r' => SimOut a b r r')"
    | .value => if p.mem then "(fun _ _ a b r r' => SimOut a b r r')" else "(fun _ _ _ _ => Eq)"
  -- a room with memory: the frame clause has the room of `y.sp`, which is the `rsp` of `l2.rep` (`hbsp`)
  let lo := if p.memRoom then s!"⟨-, hbm, -, {String.join (p.inputs.map fun _ => "-, ")}hbsp, -⟩" else "⟨-, hbm, -⟩"
  let fr := if p.memRoom then "fun c hc hb => by rw [hmem, hfr c hc (by rwa [hbsp]), hbm]" else "fun c hc => by rw [hmem, hfr c hc, hbm]"
  let post := match p.kind with
    | .heap =>
      [at' 2 s!"· rintro _ _ _ _ _ _ _ - {lo} ⟨hh, hfr⟩ ⟨hex, -, hmem, -⟩",
       at' 4 s!"exact ⟨hex, hmem ▸ hh, {fr}⟩"]
    | .both =>
      [at' 2 s!"· rintro _ _ _ _ _ _ _ - {lo} ⟨hv, hh, hfr⟩ ⟨hex, hrax, hmem, -⟩",
       at' 4 s!"exact ⟨hex, by rw [hrax, hv], hmem ▸ hh, {fr}⟩"]
    | .value =>
      -- the L2 post of a frame has the mapped words of the room (G1-16); the L2⁺ post does not
      if p.mem then
        [at' 2 s!"· rintro _ _ _ _ _ _ _ - {lo} ⟨hv, hout⟩ ⟨hex, hrax, hmem, -⟩",
         at' 4 (if p.room == 0 then "exact ⟨hex, hmem.trans (hout.trans hbm), by rw [hrax, ← hv]⟩"
           else "exact ⟨hex, (fun c hc => by rw [hmem, hout c (by rwa [hbsp]), hbm]), by rw [hrax, ← hv]⟩")]
      else [at' 2 "· rintro _ _ _ _ _ _ _ _ _ rfl ht", at' 4 (if p.room == 0 then "exact ht" else "exact ⟨ht.1, ht.2.1, ht.2.2.2⟩")]
  pure ("\n".intercalate ([
    at' 2 s!"refine Above.ofRefines (fun _ _ => SimIn) {simY} (fun _ _ => refines_l2p) ?_ ?_",
    at' 2 s!"· rintro policy a s ⟨{", ".intercalate ((if hasPol then ["hpol"] else []) ++ ["hh"] ++ permitsNames p ++ ["he"] ++ regHyps ++ (if p.mem then ["harea"] else []) ++ (if p.hide || p.memRoom then ["hbelow"] else []) ++ room ++ (if p.mem then ["hsp"] else []))}⟩",
    at' 4 s!"exact ⟨{b}, {bRep}, {simIn}⟩" ] ++ post))

/-! ## The row `above_l3` (rule 4.5, path B)

`above_l3 : ∀ <params> frame (pol), Above l2p (l3 <params> frame (pol))` is `Above.ofRefines` of `refines_l3`. The text is a
function of the statement shape (the hypotheses and the arguments, as in `UpperRel.lean`) and the plan (the fields, the kind,
the parameters). The row `refines_l3 <params> frame` is applied to the parameters and the frame, not to `pol`: `SimArr`, the
output relation and `l2p.returns` do not name the policy.

The relation of the results of `refines_l3` (the argument of `Above.ofRefines` that the text leaves to the unifier):
* a value: `fun _ _ y r => r.toBitVec = y`; a narrow value: the field of the low bits of `r` (`ValueTy.rel`, `UpperRel.lean`);
* a heap: `fun x a y r => a.heap = heapOf <params> frame x ∧ r = heapOf <params> frame y`. The plan has `r = heapOf … y`
  only. With it, the frame clause of `l3.post` is not provable: `l2p.rep` fixes no ownership of the heap of `a`, and only
  the input heap equation does (as `SimOut3` of `Mark.lean`). Open point for G3-09.
* both (L3-U3): the value part on `r.1` and `y.1`, `a.heap = objsP … ++ frame`, and the statement's `post` for each memory that
  holds `r.2` (`UpperRows`). The post case rewrites `rax` to `r.1` and the policy `pol` to `a.policy`, and applies the last
  conjunct to the memory of the return.

The machine state of the start case is `s` (`freshName`: it does not hide an input of the statement).

The start case builds the L2⁺ input from the registers of `s` and the heap `objsP … ++ frame`; each conjunct of `l2p.rep` and of
`SimArr` is a conjunct of `l3.rep` (`rfl` for a register of the input). The names: `hpol`, `hh` (the heap holds the memory),
`hC` (the source contract), `hy<i>` (a hypothesis of the statement), `he` (the entry), `hq<i>` (the equation of argument `i`), `harea` (a state with
memory: no object covers the private area). -/

/-- The names of the hypotheses of the statement in `l3.rep`. -/
private def hypNames (sh : StmtShape) : List String := (List.range sh.hyps.length).map fun i => s!"hy{i}"

/-- The names of the equations of the arguments in `l3.rep`. -/
private def eqNames (sh : StmtShape) : List String := (List.range sh.args.length).map fun i => s!"hq{i}"

/-- The anonymous constructor of the parts (always, also for one part: a structure). -/
private def anon (parts : List String) : String := "⟨" ++ ", ".intercalate parts ++ "⟩"

/-- The tactic block of `above_l3` for the statement shape `sh` and the plan `p`. The row `refines_l3` is in scope, with the
parameters and the frame as its arguments. More than six arguments are an error. -/
def aboveL3Proof (sh : StmtShape) (p : UpperPlan) : Except GenError String := do
  if sh.args.length > 6 then throw (.unsupported 0 "more than six register arguments")
  if p.stackArgs > sh.call.stack.length then
    throw (.unsupported 0 "stack inputs have no separate statement arguments")
  let stack := sh.call.stack.take p.stackArgs
  let registers : List Reg64 := [.rdi, .rsi, .rdx, .rcx, .r8, .r9]
  let hstack := freshName sh p "hstack"
  let st := freshName sh p "s"
  let haddr := freshName sh p "haddr"
  let hread := freshName sh p "hread"
  let stackVals := stack.map fun a => s!"UInt64.ofBitVec ({a.term.s})"
  let stackReads := stack.zipIdx.map fun (a, i) =>
    s!"(by have {haddr} : ({st}.data.regs.rsp.toBitVec + 8) + BitVec.ofNat 64 {8 * i} = {st}.data.regs.rsp.toBitVec + {8 * (i + 1)} := (by simp [BitVec.add_assoc]); have {hread} := ({hstack}.2 ({8 * i}, ⟨.W64, {a.term.s}⟩) (by simp [Lift.Trusted.offsets])).1; rw [{haddr}] at {hread}; exact {hread})"
  let fm := sh.form
  let pl := freshName sh p "policy"
  let pf := " ".intercalate (p.params.map (·.name.s) ++ ["frame"])
  let hy := (if sh.contract.s == "True" then [] else [freshName sh p "hC"]) ++ hypNames sh
  let hq := eqNames sh
  let objs := s!"objsP {" ".intercalate (p.params.map (·.name.s) ++ fm.names)} ++ frame"
  let hasPol := p.kind.hasPolicy
  let room := if p.room == 0 then [] else ["hroom"]
  let below := if p.hide || p.memRoom then ["hbelow"] else []
  let repPat := (if hasPol then ["hpol"] else []) ++ ["hh"] ++ permitsNames p ++ hy ++ ["he"] ++ hq ++ (if p.mem then ["harea"] else []) ++ below ++ room ++ (if sh.call.stack.isEmpty then [] else [hstack])
  let b := anon ((if hasPol then [pl] else []) ++ [objs] ++ p.inputs.map (fun r => s!"{st}.data.regs.{regLower r}") ++ stackVals ++
    (if p.mem then [s!"{st}.data.regs.rsp.toBitVec"] else []))
  let lo := tuple ((if hasPol then ["rfl"] else []) ++ ["hh"] ++ permitsNames p ++ ["he"] ++ p.inputs.map (fun _ => "rfl") ++ stackReads ++
    (if p.mem then ["harea"] else []) ++ below ++ room ++ (if p.mem then ["rfl"] else []))
  let holds := if hasPol then "⟨_, hh⟩" else s!"⟨{pl}, _, hh⟩"
  let simEqs := if sh.call.stack.isEmpty then hq else hq.zipIdx.filterMap fun (h, i) =>
    if (registers[i]?).any p.inputs.contains then some h else none
  let sim := tuple (hy ++ simEqs ++ stack.map (fun _ => "rfl") ++ ["rfl", holds])
  let post :=
    if p.kind == .heap then
      [at' 2 "· rintro policy _ a s y r t ⟨hp, -⟩ ⟨hbp, -⟩ ⟨hain, hr⟩ ⟨hex, hh, hfr⟩",
       at' 4 "rw [hr, hbp] at hh",
       at' 4 "rw [hain] at hfr",
       at' 4 "exact ⟨hex, by rw [← hp]; exact hh, hfr⟩"]
    else if p.kind == .both && sh.l3Form == .post then
      [at' 2 "· rintro policy _ a s y r t ⟨hp, -⟩ ⟨hbp, -⟩ ⟨hain, hm⟩ ⟨hex, hrax, hh, hfr⟩",
       at' 4 "rw [hain] at hfr",
       at' 4 "exact ⟨hex, by rw [hrax, ← hp, ← hbp]; exact hm _ hh, hfr⟩"]
    else if p.kind == .both then
      -- `hm`: the statement's `post` at each memory that holds `r.2`; `hrax` gives the result field of `rax`
      [at' 2 "· rintro policy _ a s y r t ⟨hp, -⟩ ⟨hbp, -⟩ ⟨hv, hain, hm⟩ ⟨hex, hrax, hh, hfr⟩",
       at' 4 "rw [hain] at hfr",
       at' 4 "exact ⟨hex, by rw [hrax]; exact hv, by rw [hrax, ← hp, ← hbp]; exact hm _ hh, hfr⟩"]
    else if p.val.isWord then
      [at' 2 "· rintro _ _ _ _ _ _ _ _ _ hr ⟨hx, hm, ht⟩",
       at' 4 "exact ⟨hx, hm, by rw [ht, hr]⟩"]
    else
      -- a narrow value: `hr` is the field of the low bits of the L2⁺ result, and `ht` rewrites the register into it
      [at' 2 "· rintro _ _ _ _ _ _ _ _ _ hr ⟨hx, hm, ht⟩",
       at' 4 "exact ⟨hx, hm, by rw [ht]; exact hr⟩"]
  let simArr :=
    match fm with
    | .one _ => s!"(fun _ _ => SimArr {pf})"
    | .flat _ => s!"(fun _ _ _ => SimArr {" ".intercalate (pf :: fm.names)})"
  pure ("\n".intercalate ([
    at' 2 s!"refine Above.ofRefines {simArr} _ (fun _ _ => refines_l3 {" ".intercalate (pf :: fm.modelArgs)}) ?_ ?_",
    at' 2 s!"· rintro {pl} {fm.pat} {st} ⟨{", ".intercalate repPat}⟩",
    at' 4 s!"exact ⟨{b}, {lo}, {sim}⟩" ] ++ post))

end Skel.Gen
