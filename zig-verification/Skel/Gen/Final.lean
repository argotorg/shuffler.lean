import Skel.Gen.UpperRows
import Skel.Render

/-! The last row of the lift chain, `final` (task FINAL-LINK): the proof of the trusted statement constant itself (for example
`Lift.Spike.SumStatement.SumStatement`) from the row `contract`. The row statement is the name of the constant, so the type of the
theorem is the constant, not a copy of its body. The proof has the shape of the hand test `Lift/Spike/Test/SumFromContract.lean`,
with the lemmas of `Lift/Sem/Final.lean`:

1. intro the inputs, the contract, the binders, the hypotheses, the policy, the return address, the entry state and the entry
   (`Fn.Entry`; `Fn.EntryB` for `.callB`; `Fn.Entry` and the stack words for `.call8`);
2. `l3.rep` with the frame `[]` from the entry: `Final.holds`, `Final.permits` (`.callB`), the source contract, the hypotheses, `Bridge.Fn.Entry.sysV`,
   one register equation per argument (`Final.bv64`, `Final.bvw`, `Final.nat64` with the bound from the contract or from the
   array of words), `Final.not_covered` (a state with memory), `Final.hidden` (`UpperPlan.hide`), `Final.room` (a stack room), and the stack words (`.call8`);
3. the row `contract` gives `Reaches` of `l3.post` and `run x = some y`;
4. `Final.ret` gives `Fn.Return` from the exit, the frame clause of `l3.post` and the statement's `post`. The `post` comes from
   `run x = some y` (the result form `run`) or from the L3 function of a result term (the result form `result`: the run is `some`
   of the term, `StmtShape.result`).

Decisions:
* The text names the row `contract` and the definition `l3` of the model text; the check file declares both.
* `.call8` assumes the conjunct of the stack words last in `l3.rep`, as the relation text of L2-NORUN writes it (`stackConj`).
* The bound `n < 2 ^ 64` of an argument `BitVec.ofNat 64 n` is tried in order: `omega`, `omega` after the contract is unfolded,
  and the length of the first or second object of the statement as an array of words.
* A `Nat` argument `BitVec.ofNat 64 t` with a variable `t` of the inputs is not bounded by the contract alone (FINAL-BOUND): the proof
  proves the bounded form (`t < 2 ^ 64` as a hypothesis, used by `Final.nat64`) and then applies `Final.of_bounded`. The cases of
  `t` come from the structure of the contract: the text unfolds the contract and splits it (`split_cases`, each conjunction and
  disjunction), and each case has `t < 2 ^ 64` by `omega` (from the case, or from the size of an object that the entry has), or the
  statement for `t % 2 ^ 64`: the contract holds there, the entry equals it (`Final.ofNat_mod`), and `post` is equal (by `simp`). A
  statement that no case proves is not accepted. No case uses a name of a function.
* A local name of the text is primed when a variable of the statement has it (`freshName`). -/

namespace Skel.Gen

/-- The id of the row `name` of the function `fn`. -/
private def rowId (fn name : String) : ObId := { function := fn, name := name }

/-- The head of a term as a constant to unfold: the first word, when the term is an application of a name. A term that starts
with a bracket (a list, a function) has none. -/
private def headConst (t : String) : Option String :=
  let h := (t.splitOn " ").headD ""
  if h.length > 0 && h.toList.all (fun c => c.isAlphanum || c == '.' || c == '_' || c == '\'') && (h.get 0).isAlpha then
    some h else none

/-- The width constructor of a width. -/
private def widthName : Width → String
  | .W8 => "W8" | .W16 => "W16" | .W32 => "W32" | .W64 => "W64"

/-- The statement has a contract hypothesis: a contract that is not `True` (`Shape.lean`). -/
private def hasContract (sh : StmtShape) : Bool := sh.contract.s != "True"

/-- The identifiers of a text. -/
private def tokens (s : String) : List String :=
  let isId (c : Char) := c.isAlphanum || c == '_' || c == '\''
  (s.toList.splitBy fun a b => isId a == isId b).filter (fun w => w.all isId) |>.map String.ofList

/-- The variables `t` of the inputs with an argument `BitVec.ofNat 64 t` whose bound the proof gets from the cases of the
contract (`Final.of_bounded`): the contract is not `True` (there is a case to split), no binder or hypothesis names `t` (`revert t`
reverts only the contract and the entry), and the call form has one entry hypothesis (`Call8` has the stack words too). Another
`Nat` term (`xs.length`) has its bound from `boundText`. -/
private def natVars (sh : StmtShape) : List String :=
  let free (v : String) : Bool :=
    !(sh.binders.any fun b => (tokens b.type.s).contains v) && !(sh.hyps.any fun h => (tokens h.s).contains v)
  let cands := sh.args.filterMap fun a => match a.form with | .nat t => some t.s.trimAscii.toString | .bv => none
  match sh.call with
  | .call8 .. | .call8B .. => []
  | _ => if hasContract sh then (cands.filter fun v => sh.form.names.contains v && free v).eraseDups else []

/-- The local names of the text, primed when a variable of the statement or a parameter has the name. -/
private structure FinalLocals where
  (policy ra s he heB hstk hC hrep t y hexit hmem hrel hrun hpp hh hsz : String) (hyps : List String) (hlts : List String)

private def localsOf (sh : StmtShape) (p : UpperPlan) : FinalLocals :=
  let f := freshName sh p
  { policy := f "policy", ra := f "ra", s := f "s", he := f "he", heB := f "heB", hstk := f "hstk", hC := f "hC",
    hrep := f "hrep", t := f "t", y := f "y", hexit := f "hexit", hmem := f "hmem", hrel := f "hrel", hrun := f "hrun",
    hpp := f "hpp", hh := f "hh", hsz := f "hsz", hyps := (List.range sh.hyps.length).map fun i => f s!"hyp{i}",
    hlts := (natVars sh).map fun v => f s!"hlt_{v}" }

/-- An alternative of `first` as a sequence of tactics at the level of `first`, then `done`: `(t₁; …; tₙ; done)`. Inside
`exact`, an inner `by` that leaves a goal (or recovers from an error, as `all_goals` does) logs the error and does not throw it,
so `first` takes the alternative and the error is reported at the row (PIL-HEAP2). In the sequence each error is thrown, so the alternative fails as a
whole and `first` goes on. The term with the inner proof becomes `refine t ?_` or `apply f`, then the tactics of the proof. -/
def altSeq (steps : List String) : String := "(" ++ "; ".intercalate (steps ++ ["done"]) ++ ")"

/-- The proof of the bound `n < 2 ^ 64` of an argument `BitVec.ofNat 64 n`. -/
private def boundText (sh : StmtShape) (n : FinalLocals) : String :=
  let unfoldC := match headConst sh.contract.s, hasContract sh with
    | some c, true => [s!"(simp only [{c}] at {n.hC}; omega)"]
    | _, _ => []
  let mem := match headConst sh.objs.s with
    | some o => s!"simp only [{o}]; "
    | none => ""
  let words (m : String) :=
    altSeq ["apply Lift.Sem.Final.length_lt_of_has_words", s!"apply {n.he}.has", s!"{mem}exact {m}"]
  "(by first | " ++ " | ".intercalate (["omega"] ++ unfoldC ++
    [words "List.mem_cons_self", words "List.mem_cons_of_mem _ List.mem_cons_self"]) ++ ")"

/-- The proof of the equation of the argument `k` (`argEqs` of `UpperRel`). -/
private def argText (sh : StmtShape) (n : FinalLocals) (k : Nat) (a : ArgShape) : String :=
  match a.form, a.width with
  | .nat _, _ => s!"Lift.Sem.Final.nat64 {n.he}.inRegs {k} rfl {boundText sh n}"
  | .bv, .W64 => s!"Lift.Sem.Final.bv64 {n.he}.inRegs {k} rfl"
  | .bv, w => s!"Lift.Sem.Final.bvw .{widthName w} {n.he}.inRegs {k} rfl"

/-- The proofs of the conjuncts of `l3.rep`, in the order of `l3Text` of `UpperRel`. -/
private def repParts (t : Target) (sh : StmtShape) (p : UpperPlan) (n : FinalLocals) : List String :=
  (if p.kind.hasPolicy then ["rfl"] else []) ++
  [s!"Lift.Sem.Final.holds {n.he}"] ++
  (match sh.call with | .callB | .call8B .. => [s!"Lift.Sem.Final.permits {n.heB}"] | _ => []) ++
  (if hasContract sh then [n.hC] else []) ++
  n.hyps ++
  [s!"Lift.Sem.Bridge.Fn.Entry.sysV (lo := {t.lo}) (hi := {t.hi}) {n.he} (by decide +kernel) (by decide +kernel)"] ++
  (sh.args.zipIdx.map fun (a, k) => argText sh n k a) ++
  (if p.mem then [s!"Lift.Sem.Final.not_covered {n.he} {p.room} rfl"] else []) ++
  -- the conjunct of `UpperPlan.belowConj`: no object meets the room (PIL-HEAP `hide`, U5b `memRoom`)
  (if p.hide || p.memRoom then [s!"Lift.Sem.Final.hidden {n.he} {p.room} rfl"] else []) ++
  (if p.room == 0 then [] else [s!"Lift.Sem.Final.room {n.he} {p.room} rfl"]) ++
  (match sh.call with | .call8 .. | .call8B .. => [n.hstk] | _ => [])

/-- The frame argument of `Final.ret` from the memory clause `hmem` of `l3.post`. -/
private def finalFrame (p : UpperPlan) (n : FinalLocals) : String :=
  match p.kind with
  | .value => if p.room == 0 then s!"(fun _ _ _ => by rw [{n.hmem}])" else s!"(fun b _ hb => {n.hmem} b hb)"
  -- a room with memory (`UpperPlan.memRoom`): the frame clause of `l3.post` has the premise of the room, as `Final.ret`
  | .heap | .both => if p.memRoom then s!"(fun b ho hb => {n.hmem} b ho hb)" else s!"(fun b ho _ => {n.hmem} b ho)"

/-- The pattern of `l3.post x y s t`, by the kind of the result (`l3Text`). -/
private def l3PostPattern (sh : StmtShape) (p : UpperPlan) (n : FinalLocals) : String :=
  match p.kind with
  | .value => s!"⟨{n.hexit}, {n.hmem}, {n.hrel}⟩"
  | .heap => s!"⟨{n.hexit}, {n.hrel}, {n.hmem}⟩"
  | .both => if sh.l3Form == .post then s!"⟨{n.hexit}, {n.hpp}, {n.hmem}⟩"
    else s!"⟨{n.hexit}, {n.hrel}, {n.hpp}, {n.hmem}⟩"

/-- The pattern of `∃ y, l3.post x y s t ∧ run = some y` (the row `contract`), or, for a statement with a result term, of
`(∃ y, l3.post x y s t) ∧ post` (the row `result`, with the statement's `post` as `hrun`). -/
private def postPattern (sh : StmtShape) (p : UpperPlan) (n : FinalLocals) : String :=
  if sh.byResult then s!"⟨⟨{n.y}, {l3PostPattern sh p n}⟩, {n.hrun}⟩" else s!"⟨{n.y}, {l3PostPattern sh p n}, {n.hrun}⟩"

/-- The lines that prove the statement's `post` at the result field. `run`: `post` is `∃ y, run x = some y ∧ <field>`. `result`:
the run is `some` of the result term, and `post` is the field of the term. `both`: `l3.post` has the statement's `post`. -/
private def resultLines (sh : StmtShape) (p : UpperPlan) (n : FinalLocals) : List String :=
  let unfold := (headConst sh.post.s).toList ++ (headConst sh.fn.term.s).toList
  let simpUnfold := if unfold.isEmpty then [] else [s!"  simp only [{", ".intercalate unfold}]"]
  let enc := "Lift.Trusted.Encode.encode"
  match p.kind, sh.byResult with
  | _, true => [s!"  exact {n.hrun}"]
  | .both, _ => [s!"  exact {n.hpp}"]
  | .heap, _ =>
    let mem := match headConst sh.objs.s with | some o => s!"simp [{o}]" | none => "simp"
    simpUnfold ++ [s!"  exact ⟨{n.y}, {n.hrun}, Lift.Sem.Final.has_of_holds {n.hrel} _ (by {mem})⟩"]
  | .value, _ =>
    simpUnfold ++ [s!"  first | exact ⟨{n.y}, {n.hrun}, {n.hrel}⟩ | " ++
      altSeq [s!"refine ⟨{n.y}, {n.hrun}, ?_⟩", s!"simp [{enc}, Width.bits, {n.hrel}]"] ++ " | " ++
      altSeq [s!"refine ⟨{n.y}, {n.hrun}, ?_⟩", s!"simpa [Width.bits] using {n.hrel}"]]

/-- The lines that prove the cases of the variable `v` (the second hypothesis of `Final.of_bounded`, with `v`, the contract and the entry
introduced): `v < 2 ^ 64`, or the statement for `v % 2 ^ 64` gives the statement. The facts: the size of each object that the entry
has (`Final.sizes`, `Final.size_words`); then the entry is cleared, so that `split_cases` does not take it apart. The contract is
unfolded and split: each case has `omega` for the bound (from the case, or from the sizes), or the statement for `v % 2 ^ 64`: the
contract holds there (`simp`), the entry is the same (`Final.ofNat_mod`) and so is `post` (`congr_post` and `simp` with the definitions
of the statement). The lines have the indentation `ind`. -/
private def casesLines (sh : StmtShape) (n : FinalLocals) (ind : String) : List String :=
  let c := (headConst sh.contract.s).toList
  let unfoldC := match c with
    | [] => []
    | c :: _ => [s!"try simp only [{c}] at {n.hC}"]
  let objs := (headConst sh.objs.s).toList.map (· ++ ", ")
  let unfold := ", ".intercalate (c ++ (headConst sh.post.s).toList ++ sh.runConst.toOption.toList)
  let simpC := match c with | [] => "simp" | c :: _ => s!"simp [{c}]"
  let lines :=
    (match sh.call with | .callB | .call8B .. => [s!"have {n.he} := {n.heB}.1"] | _ => []) ++
    [s!"have {n.hsz} := Lift.Sem.Final.sizes {n.he}.has",
     s!"try simp only [{String.join objs}List.forall_mem_cons, Lift.Sem.Final.size_words, List.length_map] at {n.hsz}",
     s!"clear {n.he}" ++ (match sh.call with | .callB | .call8B .. => s!" {n.heB}" | _ => "")] ++
    unfoldC ++
    ["split_cases",
     "all_goals first",
     "  | (left; omega)",
     "  | (right; subst_vars; refine ⟨?_, ?_, ?_⟩",
     s!"     · first | assumption | ({simpC}; done)",
     s!"     · intro {n.hh}; rw [Lift.Sem.Final.ofNat_mod]; exact {n.hh}",
     s!"     · intro {n.hh}; refine Lift.Sem.Final.congr_post ?_ {n.hh}; funext _ _ _; simp [{unfold}, Lift.Sem.Final.ofNat_mod_lit])"]
  lines.map (ind ++ ·)

/-- The lines `core` inside the proofs of the bounded form for each variable of `vs` (`Final.of_bounded`): `revert v` reverts `v`,
the contract and the entry `entry`; the lemma has two goals, the cases of `v` and the bounded form with `hlt : v < 2 ^ 64`. The names
of the contract and of the entry stay, so that `core` is the proof of the bounded form as it is. -/
private def boundedLines (sh : StmtShape) (n : FinalLocals) (entry : String) : List String → List String → List String
  | [], core => core
  | v :: vs, core =>
    let hlt := (((natVars sh).zip n.hlts).lookup v).getD "hlt"
    [s!"  revert {v}", "  refine Lift.Sem.Final.of_bounded ?bounded ?cases", "  case cases =>",
     s!"    intro {v} {n.hC} {entry}"] ++ casesLines sh n "    " ++
    ["  case bounded =>", s!"    intro {v} {hlt} {n.hC} {entry}"] ++ (boundedLines sh n entry vs core).map ("  " ++ ·)

/-- The proof text of the row `final` of the target `t`, the statement shape `sh` and the plan `p`: a `by` block. -/
def finalProof (t : Target) (sh : StmtShape) (p : UpperPlan) : Except GenError String := do
  checkNames sh p
  let _ ← sh.runConst
  if p.kind == .heap then let _ ← heapInput sh
  let n := localsOf sh p
  let entry := match sh.call with
    | .call => [n.he]
    | .callB => [n.heB]
    | .call8B .. => [n.heB, n.hstk]
    | .call8 .. => [n.he, n.hstk]
  let bounded := natVars sh
  -- with a bounded variable the entry is introduced up to its first hypothesis; the proof of the bounded form follows
  let intros := sh.form.names ++ (if hasContract sh then [n.hC] else []) ++ sh.binders.map (·.name.s) ++ n.hyps ++
    [n.policy, n.ra, n.s] ++ (if bounded.isEmpty then entry else entry.take 1)
  let params := p.params.map (·.name.s)
  let l3 := "(l3 " ++ " ".intercalate (params ++ ["[]"] ++ sh.form.modelArgs ++ (if p.kind.hasPolicy then [n.policy] else [])) ++ ")"
  let contractArgs := params ++ ["[]"] ++ sh.form.modelArgs ++ (if p.kind.hasPolicy then [n.policy] else []) ++ [n.policy] ++
    (match sh.form with | .one b => [b.name.s] | .flat _ => []) ++
    [n.s, n.hrep, if hasContract sh then n.hC else "trivial"]
  let core :=
    (match sh.call with | .callB | .call8B .. => [s!"  have {n.he} := {n.heB}.1"] | _ => []) ++
    [s!"  have {n.hrep} : {l3}.rep {n.policy} {sh.form.arg} {n.s} :=",
     s!"    ⟨{", ".intercalate (repParts t sh p n)}⟩",
     s!"  refine ({if sh.byResult then "result" else "contract"} {" ".intercalate contractArgs}).mono ?_",
     s!"  rintro {n.t} {postPattern sh p n}",
     s!"  refine Lift.Sem.Final.ret {n.he} {p.room} rfl {n.hexit} {finalFrame p n} ?_"] ++
    resultLines sh p n
  let lines := ["by", s!"  intro {" ".intercalate intros}"] ++ boundedLines sh n entry.head! bounded core
  pure ("\n".intercalate lines)

/-- The row `final` of `fn`: the statement is the trusted statement constant `stmt`. The row depends on `contract`, or on
`result` for a statement with a result term (`byResult`, L2-NORUN): `result` has the statement's `post` already. -/
def finalRow (fn stmt : String) (byResult : Bool := false) : Obligation :=
  { id := rowId fn "final", cls := .link, origin := .unit, statement := stmt,
    deps := [rowId fn (if byResult then "result" else "contract")], claim := .none }

/-- The theorem text of the proof of the statement of `fn`: `theorem <fn>_proof : <stmt> := <proof>`, with the binders `hyps`
before the colon (the tests give the row `contract` as a binder). The helpers of a proof text (`Skel.Proof.ofText`) go before the
theorem. -/
def finalTheorem (fn stmt proof : String) (hyps : List String := []) : String :=
  let p := Proof.ofText proof
  let thm := s!"theorem {fn}_proof{String.join (hyps.map (" " ++ ·))} : {stmt} := {p.proof}"
  if p.helpers.isEmpty then thm else p.helpers ++ "\n\n" ++ thm

end Skel.Gen
