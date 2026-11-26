# Kraken: how to prove x86-64 code in Lean

Kraken is a Hoare logic for x86-64 assembly in Lean 4. A program is AT&T assembly text, parsed to
Lean data; its meaning is an operational semantics of sequential x86-64 (registers, flags, memory;
no OS, no concurrency). You prove that a program, or a function in it, meets a specification. The
sources are in `vendor/Kraken/Kraken/`; complete proofs are in `vendor/Kraken/Kraken/X64/Examples/WP/`
(`Jumps.lean`, `LoadStore.lean`, `PushPopLoop.lean`, `P3.lean`, `CallSwap.lean`, `ManyCalls.lean`,
`ChangingFrames.lean`, `EvenOdd.lean`, `Memmove.lean`, `Halts.lean`, `Surprises.lean`). There is
no Mathlib.

Names: only the parser is in a `Kraken` namespace (`Kraken.X64.Parser`). The rest has no `Kraken.`
prefix: `Mem.Mapped`, `MachineData.push64`, `Program.WP.Spec.mov_reg_reg`, `FunSpec.autoframes`;
the specs of `VerifiedNix.X64Specs` are `X64Specs.…`; the examples are in `State.…`.

Find names and lemmas with `lean_loogle`, before you `#check` a guess. It searches Kraken and the
project's library, and gives each declaration's full statement:
- `"mov_reg32"` (in quotes: a part of a name): the specs `Program.WP.Spec.mov_reg32_mem`,
  `X64Specs.mov_reg32_imm`, `X64Specs.mov_reg32_reg32`; `"Program.WP.Spec"` lists Kraken's specs (57 declarations).
- `Mem.Contains`: every declaration that mentions it; `Mem.WritesOnly, Mem.storeInt`: those that
  mention both (`Mem.WritesOnly.storeInt`, `Mem.WritesOnly.trans_storeInt`, …).
- `Mem.Contains (Mem.storeInt _ _ _ _) _ _`: the lemmas whose statement has this pattern.

Use `view_file` to read a whole file (an example proof, `Spec.lean`), and `grep` for text that is
not a declaration name: assembly syntax, how examples call `vcgen`. Declarations have their
namespace in the source (`def MachineData.push64`, `abbrev MachineData.StackBelow`), so a grep for
`def push64` finds nothing; grep for the last part of the name, or use `lean_loogle`. The section
"Reference" below has the definitions and lemmas that proofs need most often.

In a working proof file, put every helper input in its declaration's binders. The checker rejects
all `variable` commands, including those in a `section` or `namespace`. A helper about pure data
should take only that data and its facts; add `[Host]` or `[FunDecls]` only when its statement or
proof needs them. This prevents a helper from taking unused instances through section scope.

Campaign proofs also pass a source importer. Use helper definitions and theorems, and call tactics
directly. Do not add `syntax`, `macro`, `macro_rules`, notation, or elaborator commands. These commands
are not supported by the importer, even when Lean accepts the proof. Helper names are local to one
obligation. Use the exported obligation theorems to share results between proofs.

For a disproof, omit the target theorem and add `theorem target.disproof : ¬ (T) := by ...`,
where `T` is its full original type. Read that type from `view_original_file` and include every
binder. For `theorem target (x : α) : P x`, the disproof type is `¬ (∀ x : α, P x)`.
Keep the frozen imports and definitions unchanged.

Copy source `match` expressions from the original type. Output from `#print` can contain internal
names such as `target.match_1` or `target.disproof.match_2`; these names depend on the declaration
being elaborated. Do not declare helpers under these names or copy them into the disproof type.
Use ordinary helper names, such as `counterexampleState`, and state the exact original negation.
The validator checks that negation even if a handwritten matcher computes the same results on
the counterexample.

## The objects

- `Program := List Directive`. A directive is a label, an instruction or bytes.
  `parse("…")` (with `open Kraken.X64.Parser`) turns AT&T text into a `Program` at elaboration
  time. A fragment such as `p ++ q` is also a program.
- `MachineData` is the state without the program counter: `regs : Reg64s` (fields `rax` … `r15`,
  each a `UInt64`), `status : StatusFlags` (`cf pf af zf sf of`), `zmms`, and
  `dmem : Mem 64` (a partial map from addresses to bytes: an address without a byte is not mapped,
  and an access to it is a fault).
  Two spellings of a register: `s.regs.rax : UInt64` and `s.regs.get64 .rax : BitVec 64`.
  Use `.toNat` or `.toBitVec` to compare values; `s.regs.rsp.toBitVec` and `s.regs.get64 .rsp`
  are equal.
- `[Host]`: the whole linked program `Host.prog` and its layout, unknown at proof time.
  `label "foo" : Int64` is the address of label `foo`. Different labels need not have different
  addresses unless a fact says so (`Embeds.label_ne`, `Host.addrOf_ne`).
- `[Embeds p]`: the fragment `p` is a part of `Host.prog`. `[FunDecls]`: the declared functions;
  a hypothesis `(h : FunDecls.at (label "f") = some ⟨f⟩)` says that `call f` runs the fragment `f`.

## The statements

`Q : Unit → MachineData → Prop` is the condition when the fragment falls through its end;
`E : Int64 → MachineData → Prop` is the condition when it exits by a jump to the address `a` (a
`ret`, a jump to a label outside the fragment, a tail call).

    WP.wp p Q E s                     -- from state s, the run of p ends in Q or E
    ⦃ P ⦄ p ⦃ Q; E ⦄                  -- for each s with P s: WP.wp p Q E s
    Eventually (step1 Host.exe) post ⟨s, startAddr hp⟩   -- start with: apply Program.WP.step1_of_wp hp

All of them are total correctness: the run must end. A loop needs a variant (below).

A function spec (`import Kraken.FunSpec`):

    funspec f_spec "f" [Host] [FunDecls] [Embeds f]
        (hf : FunDecls.at (label "f") = some ⟨f⟩) at s
        requires P                       -- about s, the state before the call
        ensures s' => Q                  -- about s and s', the state after the return
        autoframes calling_conv SysV preserves rcx rdx := by
      proof

`s` is the state before the `call`; the body starts in `s.push64 ra` (the return address `ra`
pushed). The command makes two theorems: `f_spec.go`, the triple of the body, which `proof`
proves:

    ⦃ fun s₀ => s₀ = s.push64 ra ∧ P ⦄ f ⦃ fun _ _ => False; fun a t => a = ra ∧ Q ∧ … ⦄

and `f_spec`, the form for callers. Clauses:
- `autoframes` adds a frame to the postcondition: `t.regs.rsp = s.regs.rsp`, the registers of
  `calling_conv` (SysV: rbx rbp r12–r15) and of `preserves` are unchanged, and memory changes only
  in the return slot, in `reserve k` more stack slots below it, and in the `writes b[*...<n]`
  blocks. Without `autoframes` the postcondition is only `a = ra → Q`.
- `exits a s' => X`: the condition for an exit at an address `a ≠ ra`; `halts ["l"]` for exits at
  halt labels (see `Halts.lean`).
- Recursion: `termination_by m` after the proof, and `mutual … end` for mutual recursion; the
  recursive spec is then usable in its own proof (`EvenOdd.lean`).
- `where` after a `funspec` proof defines abbreviations for the invariants (`Memmove.lean`).
  `funspec` emits these definitions before it checks the proof. An ordinary theorem's `where`
  helper is a local constant during its proof: `unfold` and the fuzz test cannot read its value
  there. Define such a predicate before the theorem, or use a local `let` with a value.
  For an invariant helper `I` with an implicit start state, use
  `· fun {s₀} => @I s₀` in the invariant clause.

## The proof: `vcgen`

Nearly every proof is one call of `vcgen` (with `set_option experimental.vcgen true`):

    vcgen [prog, g_spec]          -- the program to unfold, and the specs of the functions it calls
      invariants
      · fun {s₀} l s' => match l with   -- an assertion for each label of prog
          | "loop" => …
          | _ => False
      · fun l s' => …              -- a variant: a Nat for each label
      with kfinish

How it works: the program is cut into blocks at its labels. For each block, `vcgen` steps through
the instructions with their `@[spec]` theorems and makes verification conditions (VCs): the
invariant of the block's label, assumed at the start, must give the invariant of each label that
the block jumps or falls to, `Q` at the end of the program, and `E` at an exit.

- **The invariant** `I : {s₀ : MachineData} → Label → MachineData → Prop` gives the state at each
  label; `s₀` is the start state of the fragment (or use the theorem's own start state, as in
  `fun _ s' => s' = s`). The first label of a function: `s' = s₀`. Labels that no run reaches:
  `| _ => False`.
- **A jump to a label of the fragment needs `rsp` at or below its start value** (the run must own
  the stack). Put `s'.regs.rsp = s.regs.rsp` (or the actual offset) into the invariant of each
  label that a jump reaches; without it the jump VC is false.
- **The variant** `var : Label → MachineData → Nat`: on each edge from block `l` to block `l'`,
  `var l' s' < var l s`, or the same value and `l'` later in the text. So `fun _ _ => 0` is enough
  when all jumps go forward; a back edge (a loop) needs a variant that decreases, such as the
  loop counter `s'.regs.rcx.toNat`.
- **The specs**: the list after `vcgen` holds the program definitions to unfold and the spec of
  each called function (`vcgen [many, touch_spec]`). With a program built by `++`, unfold its parts
  with the `simp` clause: `vcgen [pswap] invariants … simp [swap] with kfinish`.
- **`kfinish`** closes each VC with Kraken's `grind` setup; extra lemmas: `kfinish [lemma]`.
  With `import VerifiedNix.X64Specs`, it also works as an ordinary tactic after `vcgen` and in
  helper proofs: `all_goals kfinish`. It runs `sym => kfinish` and accepts the same options,
  `only`, and lemma list, for example `kfinish (clean := true) only [helper]`.

Without an `invariants` clause, `vcgen` leaves the goals `inv1 : Program.CfgInvariant` and
`inv2 : Program.CfgVariant`, and the VCs contain `sorry` in place of the invariant. Always give
both invariants when the program has a label (one label is enough: `touch:`).

## When `kfinish` fails

The error is only "`finish` has failed". Find the VCs that fail:

    vcgen [prog]
      invariants
      · …
      · …
      with try kfinish
    trace_state        -- shows only the VCs that kfinish did not close
    all_goals sorry

Read each remaining VC: it is almost always an invariant that is too weak (a fact that the next
block needs is missing: `rsp`, a bound, a register that a later block reads, the memory) or a
wrong variant. Strengthen the invariant and try again. `with skip` instead of `with try kfinish`
shows all VCs, named `vc1`, `vc2`, …; prove one by hand with `case vc3 => …`:

- a VC without `Program.Intercept` (an entry, a fall-through, an arithmetic fact): `grind`;
- a jump VC `⊢ Program.Intercept ["l₀", "l₁", …] s₀ I' E a s`: the target is the label at index
  `i` of the list: `apply Program.Intercept.intro_label (i := i) rfl`, then `left` (the jump stays
  in the fragment: prove `s.StackAtOrBelow s₀ ∧ I' l (i+1) s`) or `right` (it exits: prove `E`),
  then `grind`.
- the exit part of the VC of a function's `ret`, `∀ l ∈ ls, label l = a → (c.push64 ra).StackBelow t`
  (with `t` a large state literal): `fun _ _ _ => MachineData.push64_stackBelow (by simp)`. The
  lemma (in `VerifiedNix.X64Specs`) needs only `t.regs.get64 .rsp = c.regs.get64 .rsp`; `simp`,
  `grind` or `decide` on the whole literal timed out in several runs.

If a goal displays names with `✝`, use `expose_names` or `rename_i` before a manual step. Do not
copy the displayed names into the proof. For example, after `intro`, `rename_i s` gives the last
unnamed binder the name `s`.

For an unavailable tactic, use the core form that fits the goal. Replace `by_contra h` with
`apply Classical.byContradiction; intro h`. For `norm_num`, try `decide` on closed arithmetic,
`simp` for rewrites, or `omega` for linear `Nat` and `Int` facts. Use `grind` for logical goals
that would use `tauto`. In place of `set x := value with hx`, use `let x := value` and
`have hx : x = value := rfl`.

For a stack comparison with equal stack pointers, rewrite the register equality before you apply
reflexivity of the scalar relation. This avoids equality search over whole machine states:

    example (s t : MachineData) (h : t.regs.rsp = s.regs.rsp) :
        t.StackAtOrBelow s := by
      change ¬ s.regs.rsp.toBitVec.SerialLt t.regs.rsp.toBitVec
      rw [h]
      exact BitVec.not_serialLt_self _

For a register read from `push64`, give its rewrite explicitly to `simp`:
`simp [MachineData.regs_push64]`. For example, this proves
`(s.push64 ra).regs.rdi = s.regs.rdi`.

## Test an invariant before you prove it

The test runs by itself. With `import VerifiedNix.X64Specs`, each `vcgen … invariants · I · V` of
a program with a loop (a jump to a label at or before the jump) that leaves VCs open (goals, or an
error such as "`finish` has failed") runs a fuzz test. It runs the program on random start states
that satisfy the theorem's hypotheses, and checks each conjunct of `I` at each visit of a label,
`V` on each edge between labels (the rule of `vcgen`), `E` at each exit and `Q` at the end of the
program. Its result is one message at `vcgen`, in the check report of each edit (an info, not an
error; the VCs and errors are those of `vcgen` alone):

    25:3: info: fuzz: 200 samples (0 skipped by pre), 1322 label visits: 1 failures
    sample 1: invariant at .Lnext, conjunct 1, false at a visit: s'.regs.rax.toNat + 1 < n
      state: rax=2 rbx=… rdi=3 rsp=2147352568 …

- A failure is a run from a state that satisfies the hypotheses: the conjunct, the variant
  ("variant does not decrease from l (a) to l' (b)"), the exit condition ("postcondition") or `Q`
  ("fall-through condition") that it names is false. A fault ("the run faults: load at the
  unmapped address …") shows a missing `Mem.Mapped`. Correct these before you read the VCs.
- `no check failed.`: the samples found no error. The invariant can still be too weak for the
  VCs (no `rsp`, no `Mapped`, a fact that a later block needs): read the VCs.
- `fuzz: not run: <reason>`: no test, for example for a hypothesis that is not decidable (a callee
  spec `∀ c ra, ⦃…⦄ …`, a fact about `Host` or `FunDecls`), a program that calls code outside it,
  or a precondition without `s₀ = …`.
- Named predicates are unfolded in a bounded search when their components have executable
  decisions. Local `let` values are expanded in the test's hypotheses, start state, invariant,
  variant and postconditions. Opaque predicates and local constants without values can still
  prevent a test. The message distinguishes a dependency, a missing decision, a missing
  generator, and samples that all fail the precondition; use the stated reason.
- The samples come from the hypotheses (of the theorem and of the precondition):
  `Mem.Mapped [(c.regs.r.toBitVec + d, n), …] c.dmem` and `Mem.Contains c.dmem c.regs.r.toBitVec bs`
  give register `r` a buffer of its own (with the bytes `bs`); `c.regs.r.toNat = n`,
  `bs.length = c.regs.r.toNat` or `c.regs.r = v` set `r`; numbers and byte lists are small. The
  other hypotheses only skip samples ("N skipped by pre"; "no sample satisfied pre" when none
  passes). The other registers have random 64-bit values: a loop on such a register can run out of
  steps ("the run did not end within 10000 steps").
- The same `I`, `V` and goal again give the result without a new run. `set_option fuzz.vcgen false`
  turns the test off.

The `fuzz` tool runs `#fuzz` commands after the working file: the same test, with the parts given
by hand, for example before the first `vcgen`, or on a part of a program:

    #fuzz prog args (c : MachineData) (ra : Int64) (bs : List UInt8) (hl : bs.length = c.regs.rdx.toNat)
        (hc : Mem.Contains c.dmem c.regs.rsi.toBitVec bs) with
      (start := c.push64 ra)
      (invariant := fun {s₀} l s' => match l with | "prog" => s' = s₀ | … | _ => False)
      (variant := fun l s' => …)
      (post := fun a t => a = ra ∧ …)

`args` are the theorem's variables and hypotheses; the samples come from them as above. `post`
(the exit condition `E`), `(runs := 200)`, `(seed := 0)` and `(fuel := 100000)` are optional, and
so are `(gen := …)` and `(pre := …)` before `start`: `gen` gives the values of the variables as a
tuple (`Fuzz.stack (← Fuzz.machine)`, `Fuzz.buffer s .rsi bytes`, `Fuzz.setReg`, `Fuzz.bytes n`,
`Fuzz.nat n`, `Fuzz.ret`), `pre` skips the samples that do not satisfy it. `FuzzTest.lean` has
complete examples.

## Instructions without a spec

`vcgen` steps an instruction only if a `@[spec]` theorem matches its exact form. Otherwise:
"No spec found for program Directive.instr (Instr.regular Width.W64 Width.W64 (Operation.sub …))".
The existing specs are in `vendor/Kraken/Kraken/X64/WP/Spec.lean` (`lean_loogle` with `"Program.WP.Spec"`,
or a part of the name: `"mov_reg"`, `"push"`): mostly 64-bit
register forms of mov, add, adc, sub (immediate), cmp, test, xor, and, inc, dec, lea of a label,
mulx, shl (32-bit), push, pop, jmp, jcc, call, ret, nop; stores of 1, 2, 4 and 8 bytes and loads
of 1, 2 and 4 bytes at `d(%b)`; 8-byte loads and stores at `d(%b,%i,8)`. There is no spec for a
plain 64-bit load `movq d(%b), %r` (only `addq d(%b), %r`), for an index with scale 1, 2 or 4, for
`movzbl`/`movzx`, `lea` of a register, `setcc`, or an operation on memory.

`VerifiedNix/X64Specs.lean` (`import VerifiedNix.X64Specs`) adds proved `@[spec]`s for: `movq d(%b), %r`
(`mov_reg_mem`), `movq %r, d(%b,%i)` (`mov_sib1_reg`), `movb %r8, d(%b,%i)` (`mov_sib1_reg8`),
`movzbl d(%b,%i), %r32` (`movzx_reg32_sib1_8`), `addq $i, d(%b)` (`add_mem_imm`), `movl $i, %r32`
(`mov_reg32_imm`), `movl %r32, %r32` (`mov_reg32_reg32`), `leal d(%b), %r32` (`lea_reg32`), and
`shlq $i, %r` (`shl_reg_imm`). A file that imports it needs no spec of its own for these forms. Write a spec for a missing form in the working file, after the
pattern of `Spec.lean`, with the constructor term from the error message, and give it to `vcgen`:

    theorem sub_reg_reg_spec [Host] [FunDecls] {Q : Unit → MachineData → Prop}
        {E : Int64 → MachineData → Prop} (asz : Width) (rd rs : Reg64) :
        ⦃ fun s => Q () { s with regs := s.regs.set64 rd (s.regs.get64 rd - s.regs.get64 rs), status := StatusFlags.ofSub (s.regs.get64 rd) (s.regs.get64 rs) } ⦄
          (Directive.instr (.regular asz .W64 (.sub (.reg (.low rd .W64)) (.regOrMem (.reg (.low rs .W64))))))
        ⦃ Q; E ⦄ := by
      refine Triple.intro fun s hpre => ?_
      refine Program.wp_single fun _ _ _ _ hn _ => ?_
      simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp,
        RegOrMem.interp, MachineData.set, MachineData.setReg, Reg64s.get_low_W64,
        Reg64s.set_low_W64, Effects.All]
      exact hn _ hpre

    … vcgen [prog, sub_reg_reg_spec] … with kfinish

The precondition is the postcondition `Q` on the state after the instruction. A memory access
adds `(Mem.loadInt s.dmem addr n).isSome = true ∧ …` (see `mov_mem_reg`); a jump uses `E`. If
the `exact` fails, the goal after `simp only` shows the real effect of the instruction. In a structure instance
`{ s with regs := … }`, a new line that starts with `(` or an identifier is read as a new field
("unexpected token '('; expected '}'"): keep each field value on one line. A value that a later
spec or `kfinish` must compute should use `BitVec.setWidth`, not `s.regs.get (.low r .W32)`:
`grind` does not evaluate the `BitVec.take` that this gives, even on literals.

## Memory

- `Mem.loadInt m a n : Option Int`, `Mem.loadBytes m a n : Option (List UInt8)`,
  `Mem.storeInt m a n v`; `n` bytes, little endian.
- State a loaded value as `BitVec.ofInt 64 (m.loadInt a 8).get!` (4 bytes: `BitVec.ofInt 32 …`),
  in statements and invariants. `kfinish` proved the same program with this form and failed with
  `(m.loadInt a 8).map (BitVec.ofInt 64) = some v`.
- `Mem.Mapped [(a, n), …] m`: the bytes are mapped, so loads and stores there do not fault. Each
  load and store needs it, for buffers that are only read as well (`Contains` alone did not give
  `kfinish` the mapping), and so does each `call` and `push` (the slot at `rsp - 8`), and `ret`
  (the slot at `rsp`, which `s.push64 ra` fills).
- `Mem.Blocks.Disjoint bs bs'`: the blocks do not overlap. A store into one block does not change
  a load from a disjoint one; give the disjointness of buffers and stack slots as hypotheses.
- `Mem.WritesOnly bs m m'`: `m'` equals `m` outside the blocks `bs`. `Mem.Contains m a bs`: the
  bytes `bs` are at `a`. `Mem.Block.ofStackSlots rsp k`: the `k + 1` slots of 8 bytes below `rsp`.
- Separation logic: `m =⋆ P ⋆ R` (`Mem.Blocks bs`, `v.At a`); see `PushPopLoop.lean`,
  `AluMem.lean`.
- In a loop invariant, keep the memory facts that later blocks need (`Mapped`, `Contains`,
  `WritesOnly` against the start memory), as `Memmove.lean` does.
- `bv_omega` takes `r.toNat` and `r.toBitVec.toNat` of a register as one value (a lemma of
  `VerifiedNix.X64Specs` in its preprocessing); plain `omega` takes them, and
  `{ toBitVec := v }.toNat`, as different values and fails on true goals.
- Arithmetic side conditions (`Disjoint.of_sub`, offsets): `bv_omega only [hwrap]` (in
  `VerifiedNix.X64Specs`) runs `bv_omega` with only the listed facts. Plain `bv_omega` uses every
  fact of the context; in a proof with many address equations a false goal then took minutes and
  gigabytes before it failed. With `only` it fails at once, with a counterexample. Use it only for
  offsets from one base: two different pointers (`rsi` and `rdi`) are disjoint by a hypothesis,
  not by arithmetic; take that from the hypothesis (`Mem.Blocks.Disjoint` lemmas, `of_inside`).
  An edit that raises `maxHeartbeats` above 400000 is refused: split a slow step instead.
- A load through a chain of stores (`VerifiedNix.MemSimp`, in `VerifiedNix.X64Specs`): the tactic
  `mem_simp` rewrites `(m.storeInt a n v).loadInt x k` to `some (Int.ofBytes (Int.toBytes n v))`
  when `x = a` and `k = n`, and to `m.loadInt x k` when the blocks do not overlap, then goes on down
  the chain. Use it before `kfinish`: `vcgen [prog] with (mem_simp; kfinish)`, or after
  `with try kfinish`: `all_goals mem_simp`, then `all_goals kfinish`. `kfinish` alone does not
  do this rewrite (in `grind` it broke proofs that worked before). This needs no hypothesis when
  `x` and `a` differ by a constant:
  the same terms with the same factors and a different number (`rdi` and `rdi + 8#64`,
  `16#64 * i + rdi + 24#64` and `rdi + i * 16#64 + 32#64`, `rsp - 16#64 + 8#64` and
  `16#64 + (rsp - 16#64)`). The number decides, modulo `2 ^ 64`. A load that overlaps a store
  but has a different address or size stays at that store: the stores below it are not passed. The
  `ret` of a function body reads the return slot through the stores of its frame in the same way.
- When the terms differ (`rdi + 4#64` and `8#64 * i + rdi + 8#64`), the blocks are disjoint only
  with a bound. Give it to `mem_simp [hwrap]`: it proves `n ≤ (x - a).toNat` and
  `k ≤ (a - x).toNat` with `bv_omega` from the listed facts only, with a small heartbeat budget. A
  load whose conditions it cannot prove stays; `mem_simp` does not fail. In the `vcgen` clause:
  `with (mem_simp [hwrap]; kfinish)`; after `with try kfinish`: `all_goals mem_simp [hwrap]`, then
  `all_goals kfinish`. `mem_simp` without a list does only the constant case; `mem_simp []`
  also runs `bv_omega`, without facts.
- Two different pointers (`rdi` and `rsi`) are disjoint only by a hypothesis
  `Mem.Blocks.Disjoint …`; `mem_simp` does not change such a load, `kfinish` uses the hypothesis.
- Struct fields and array elements (addresses `base + d` and `16 * i + base + d` from one base):
  `kfinish` does not unfold `Mem.Blocks.Inside` and does not try `Mem.Blocks.Disjoint.of_sub` by
  itself. Give them: `with kfinish [Mem.Blocks.Inside, Mem.Blocks.Disjoint.of_sub]`. Then it proves
  that such an address is inside a mapped block.
- Spellings of one address: before the comparison, `let` variables are read through their values
  and the projections of structure literals are reduced (`{ …, rsp := { toBitVec := e }, …
  }.rsp.toBitVec` is `e`). `mem_simp` also reads `r.get64 .rsp` as `r.rsp.toBitVec`,
  `(s.push64 ra).regs.rsp.toBitVec` as `s.regs.rsp.toBitVec - 8#64` (the other registers of
  `s.push64 ra` as those of `s`), and `(s.push64 ra).dmem` as the store of `ra` at `rsp - 8`; it
  writes these register reads in the goal in that spelling.
- `Mem.Blocks.Inside x n bs` with a constant difference `x - a` for a block `(a, len)` (also
  `Mem.Block.ofStackSlots rsp k` with a literal `k`): `mem_simp` decides it block by block: `True`
  when a block contains the access (blocks before it may be undecided), `False` when each block is
  decided not to and the list ends. A block with other terms (`rdi` against the frame of `rsp`) is
  undecided. In `kfinish` and `grind`, the lemma `Inside.of_stackSlots_toNat` reduces an `Inside`
  in stack slots to `(x - a).toNat + n ≤ len`.
- `kfinish` and `grind` do not use hypotheses for these rewrites. In a function body the VC has the
  start state as a variable, `t✝ = s.push64 ra✝`: the stores of the body are at `t✝.regs.rsp`, the
  frame of `autoframes` is at `s.regs.rsp`. `mem_simp` first substitutes such equations: for each
  local variable `x` of the memories and addresses in the goal, an equation `x = e` or `e = x` (as
  `subst` does). For the `WritesOnly` part of a frame under `autoframes` (stores into
  `8(%rsp)` after `subq $16, %rsp`), `kfinish` also needs the loads inside `grind`: put
  `attribute [local seval] MemSimp.loadStore MemSimp.subToNat` before the theorem (an opt-in: in
  `grind` by default these broke other proofs), then `with try kfinish`, `all_goals mem_simp`,
  `all_goals kfinish`.
- `mem_simp at h`, `mem_simp at h ⊢`, `mem_simp at *`: as for `simp`. A hypothesis that becomes
  `False` closes the goal. The `grind`-mode `mem_simp` (in `vcgen … with`) works on the target only
  and does not substitute equations.

## Private stack reads in generated Lift proofs

`Lift.Sem.PrivateStack` uses signed byte offsets from the entry stack pointer. Use its
rules before you unfold `store` or `loadBytes`:

- `PrivateStack.load_store_self stack width offset value` reads a value at its stored width.
- `PrivateStack.load_store_slice stack writeWidth offset value readWidth start h` reads a
  little-endian slice. `start` is a `Nat` byte offset. Prove
  `start + readWidth.bytes ≤ writeWidth.bytes` as `h`.
- `PrivateStack.load_store_disjoint stack readWidth writeWidth readOffset writeOffset value h`
  removes a store from a disjoint read. Prove either
  `writeOffset + writeWidth.bytes ≤ readOffset` or
  `readOffset + readWidth.bytes ≤ writeOffset`. `omega` proves bounds with fixed offsets.
  Adjacent intervals are permitted. Overlapping intervals need a slice or a byte proof.
- `PrivateStack.loadBytes_store_slice` and `PrivateStack.loadBytes_store_disjoint` give the
  same rules for a `Nat` byte count, including zero.

The widths can differ. A store initializes only its own bytes. A load with a missing byte
returns `.stuck`; do not assume that the private stack is initialized at entry. If the read
address is `offset` but the slice rule needs `offset + 0`, use `simpa` with the slice rule.
Use the rules through the frozen imports; do not change a proof file's imports.

## Calls

- A `call f` in `prog` needs `(hf : FunDecls.at (label "f") = some ⟨f⟩)`, `[Embeds f]`, the spec
  `f_spec` in the `vcgen` list, and the return slot mapped: `Mem.Mapped [(rsp - 8, 8)]` in the
  caller's state at the call. A caller with an `autoframes` spec reserves stack for its callees:
  `reserve 1` and `Mem.Mapped [(s.regs.rsp.toBitVec - 16#64, 8)]` for one level of calls
  (`Halts.lean`, `toucher_spec`).
- A callee's spec can also be a hypothesis of the theorem, in the form of the body triple:
  `(hg : ∀ c ra, ⦃ fun s₀ => s₀ = c.push64 ra ∧ … ⦄ FunDecls.body "g" ⦃ fun _ _ => False; fun a t => a = ra ∧ … ⦄)`;
  `vcgen [prog, hg]` uses it, and no `FunDecls.at` fact is needed.
- If the callee's spec is a premise `hg0 : GSpec` where `GSpec` is a `def` over `∀ h s ra Q E`,
  `vcgen [prog, hg0]` and `vcgen [prog, fun h s ra => hg0 h s ra]` give "No spec found for program
  FunDecls.body …". Fix the model variables, and give `vcgen` a body triple over `c ra' Q E` only:
  `have hg : ∀ c ra' Q E, ⦃ fun s₀ => s₀ = c.push64 ra' ∧ … ⦄ FunDecls.body "g" ⦃ Q; E ⦄ :=
  fun c ra' Q E => hg0 h c ra' Q E`, then `vcgen [prog, hg]` (this form proved `Rb.Increment`).
- After the call, the caller knows only the callee's `ensures` and its frame: the registers not in
  the frame are unknown. Choose `preserves` and `ensures` of the callee so that the caller's proof
  has what it needs.
- A `jmp f` or a `call` made by hand (`sub $8, %rsp; jmp f`) is no call: it is an exit at
  `label "f"` (`Surprises.lean`).
- Observed: `kfinish` proved a caller with two calls whose spec has no `autoframes`, but not the
  same caller with `autoframes … reserve 1` (the VC of the final `ret` was left). If that VC
  remains, read it with `with try kfinish` before you change the spec.

## Reference: definitions and lemmas

The definitions that proofs need most often (namespaces as in the source; `w = 64` for x86-64):

    def MachineData.push64 (s : MachineData) (v : Int64) : MachineData :=          -- X64/WP/Spec.lean
      { s with regs := s.regs.set64 .rsp (s.regs.get64 .rsp - 8#64),
               dmem := Mem.storeInt s.dmem (s.regs.get64 .rsp - 8#64) 8 v.toBitVec.toInt }
    def MachineData.retAddr (t : MachineData) : Option Int64 :=                      -- X64/WP/Instance.lean
      (Mem.loadInt t.dmem (t.regs.get64 .rsp) 8).map (fun i => Int64.ofBitVec (BitVec.ofInt 64 i))
    abbrev MachineData.StackBelow (s' s : MachineData) : Prop :=                     -- X64/WP/Step.lean
      (s'.regs.get64 .rsp).SerialLt (s.regs.get64 .rsp)
    abbrev MachineData.StackAtOrBelow (s' s : MachineData) : Prop := ¬ s.StackBelow s'
    def Program.Intercept (ls : List Label) (s₀ : MachineData) (I' : Label → Nat → MachineData → Prop)
        (E : Int64 → MachineData → Prop) (a : Int64) (s : MachineData) : Prop :=   -- StateCfg.lean
      (∃ i l, ls[i]? = some l ∧ label l = a ∧ s.StackAtOrBelow s₀ ∧ I' l (i + 1) s)
      ∨ (E a s ∧ ∀ l ∈ ls, label l = a → s₀.StackBelow s)

In `SeparationMem.lean` (namespace `Mem`; a block is `(address, length)`):

    def Blocks.Inside (addr : BitVec w) (n : Nat) : List (BitVec w × Nat) → Prop
      | [] => False
      | (a, len) :: bs => (addr - a).toNat + n ≤ len ∨ Blocks.Inside addr n bs
    def Mapped bs m := ∀ b, Blocks.Inside b 1 bs → (m.get? b).isSome
    def Blocks.Disjoint bs bs' := ∀ b, Blocks.Inside b 1 bs → ¬ Blocks.Inside b 1 bs'
    def WritesOnly bs m m' := UnchangedOutside bs m m' ∧ DomainGrows m m'
    def Contains m a bs := m.loadBytes a bs.length = some bs

Lemmas (hypotheses in parentheses, then the result):

- `Mem.loadInt_storeInt_64` (also `_8`, `_16`, `_32`): `(m.storeInt a 8 v).loadInt a 8 =
  some (Int.ofBytes (Int.toBytes 8 v))`.
- `mem_simp`, `mem_simp [h₁, …]`, `mem_simp … at h ⊢`, `mem_simp … at *` (tactic; in `grind` mode
  for `vcgen … with`, without `at` and without the substitution): substitutes the equations
  `x = e` of the local variables of the memories and addresses, then rewrites each load through a
  chain of stores and decides `Mem.Blocks.Inside` with constant differences (section "Memory"); the
  projection `{ dmem := t, … }.dmem` becomes `t`. The simprocs `MemSimp.loadStore` (loads) and
  `MemSimp.subToNat` (`(x - a).toNat`) are inside `grind` only with
  `attribute [local seval] MemSimp.loadStore MemSimp.subToNat`.
- `Mem.Blocks.Inside.of_toNat (h : (x - a).toNat + n ≤ len)`: `Inside x n ((a, len) :: bs)`
  (give it to `kfinish [Mem.Blocks.Inside.of_toNat]`; as a default `grind` lemma it caused timeouts);
  `Inside.of_stackSlots_toNat (h : (x - (rsp.toBitVec - BitVec.ofNat 64 (8 * (k + 1)))).toNat + n ≤
  8 * (k + 1))`: `Inside x n (Block.ofStackSlots rsp k :: bs)` (a `grind` lemma).
- `MachineData.loadInt_push64_rsp s v` (`grind`): `(s.push64 v).dmem.loadInt
  (s.push64 v).regs.rsp.toBitVec 8 = some (Int.ofBytes (Int.toBytes 8 v.toBitVec.toInt))`.
- `Mem.loadInt_storeInt_of_disjoint (hd : Disjoint [(x, k)] [(a, n)]) v`:
  `(m.storeInt a n v).loadInt x k = m.loadInt x k`; `loadInt_storeInt_of_inside (hd : Disjoint bs₁
  bs₂) (hx : Inside x k bs₁) (ha : Inside a n bs₂) v` gives the same.
- `Mem.Blocks.Disjoint.of_sub (h₁ : n ≤ (x - a).toNat) (h₂ : k ≤ (a - x).toNat)`:
  `Disjoint [(x, k)] [(a, n)]`. `Disjoint.of_inside (hd : Disjoint bs₁ bs₂) (hx : Inside x n bs₁)
  (hy : Inside d k bs₂)`: `Disjoint [(x, n)] [(d, k)]`; `of_inside_left` for `bs₂ = [(d, k)]`.
- `Mem.Blocks.Inside.base (h : n ≤ len)`: `Inside a n ((a, len) :: bs)`; `Inside.tail`: from `q ::
  bs` to `p :: q :: bs`; `Inside.of_singleton (hb : Inside b 1 [(x, n)]) (hx : Inside x n bs)`.
- `Mem.Mapped.storeInt (h : Mapped bs m) a n v`: `Mapped bs (m.storeInt a n v)`;
  `Mem.Mapped.storeInt_self v (hw : n ≤ 2 ^ 64)`: `Mapped [(a, n)] (m.storeInt a n v)` (a store maps
  its own block; in `VerifiedNix.MemSimp`); `Mem.Blocks.Disjoint.symm h`: the other order (write it
  with its full name: `h.symm` does not work, as `Disjoint` unfolds to a `∀`);
  `Mapped.of_inside (h : Mapped bs m) (hx : Inside x n bs)`: `Mapped [(x, n)] m`;
  `Mapped.loadInt_isSome (h : Mapped bs m) (hin : Inside addr n bs)`: `(m.loadInt addr n).isSome`.
- `Mem.WritesOnly.storeInt (hin : Inside a n bs) v`: `WritesOnly bs m (m.storeInt a n v)`;
  `trans_storeInt (h : WritesOnly bs m m') (hin : Inside a n bs) v`: `WritesOnly bs m
  (m'.storeInt a n v)`; `trans`; `WritesOnly.loadInt (h : WritesOnly bs m m') (hd : Disjoint
  [(a, n)] bs)`: `m'.loadInt a n = m.loadInt a n`; `WritesOnly.mapped (h) (hc : Mapped cs m)`:
  `Mapped cs m'`.
- `Mem.Contains.loadInt (h : Contains m a bs) (hi : (addr - a).toNat < bs.length)`:
  `m.loadInt addr 1 = some bs[(addr - a).toNat]!.toNat`; `Contains.storeInt_of_disjoint`: a store
  outside the bytes keeps them; `Contains.extend`: a 1-byte store after the prefix `bs.take k`
  gives `bs.take (k + 1)`.
- Kraken's stack lemmas are in the namespace `Program.WP`:
  `Program.WP.MachineData.stackBelow_push64 s ra : (s.push64 ra).StackBelow s` and
  `Program.WP.MachineData.not_stackBelow_self s : ¬ s.StackBelow s` (with `open Program.WP`, the
  short names). `MachineData.push64_stackBelow` (in `VerifiedNix.X64Specs`) is the other order,
  for the exit of a `ret`.

## A worked example

    def decMid : Program := parse("
    top:
      dec %rcx
      jnz top
      mov $1, %rax")

    example [Host] [FunDecls] (s : MachineData) (h : 0 < s.regs.rcx.toNat) :
        WP.wp decMid (fun _ t => t.regs.rcx = 0 ∧ t.regs.rax = 1) (fun _ _ => False) s := by
      vcgen [decMid]
        invariants
        · fun _ s' => 0 < s'.regs.rcx.toNat
        · fun _ s' => s'.regs.rcx.toNat
        with try kfinish
      trace_state
      all_goals sorry

`trace_state` shows one VC left: the back edge `jnz top`,
`⊢ Program.Intercept ["top"] s (fun l j s => 0 < s.regs.rcx.toNat ∧ …) … (label "top") {…}`.
The jump needs `rsp` at or below its start value, and the invariant says nothing about `rsp`.
With `· fun _ s' => 0 < s'.regs.rcx.toNat ∧ s'.regs.rsp = s.regs.rsp` and `with kfinish`, the
proof is complete. With the variant `fun _ _ => 0` it fails again: `jnz top` is a back edge, so
the variant must decrease on it; `rcx` does.

## Lift composed instruction blocks

Generated call interfaces have two checked bridges. `call_bridge` maps
semantic returns to ABI returns. `call_bridge_rev` maps ABI returns to
semantic returns through `callInput`. The generator uses the reverse
bridge to reuse an imported `refines_l2p` proof when the semantic result
retains the full ABI result. It checks the input fields, memory operations,
state fields and private stack before it generates this proof.

A heap-only semantic result omits the return register. Its reverse bridge
can return the heap, but that semantic refinement cannot prove the ABI
register equality. Keep the code-level proof in this case. Do not copy a
callee proof across nominal input types or remove byte-permission premises.

`lift_block_split` joins instruction proofs to a generated block statement.
Its condition and register-value solvers share flag normalization. This
reduces low register writes, Boolean word encodings, casts and modular
borrow calculations before it proves the remaining arithmetic.

For a separate scalar goal, `lift_compose_flag_eq` normalizes flag values,
splits their conditions and tries `bv_decide` with a ten-second solver
limit. `lift_compose_flag_cond h` proves a condition from branch fact `h`.
Use `lift_compose_flag_norm` alone to inspect the reduced goal, or
`lift_compose_flag_norm at h ⊢` to reduce the premise and goal together.
These tactics are available through `Lift.Tactic.Compose`.

The borrow rules require equal natural and integer modulus values and a
positive modulus. Recovering a Boolean from a zero word requires positive
word width. Byte order does not imply whole-register order or signed
order. Missing access, bound and invariant facts remain proof obligations.

## Lift typed heaps

Some generated lifting goals use `Lift.Sem.Heap`, with typed objects and a
`Heap.Holds` fact. If the file imports `Lift.Tactic.LoopClose`, start with
`loop_close [definitions]`. It also tries `heap_frame` for heap operation goals.

- `heap_step hs with value hvalue` computes one exposed successful heap
  operation in execution equation `hs`. First expose the step definition.
  The tactic tries checked rules from `using [rule1, rule2]`, then
  `heap_frame`. It keeps the computed value as a local definition, keeps
  the operation equation as `hvalue`, and keeps the continuation as `hs`.
  A store also supplies a held output heap for the next operation.
  For example, use `heap_step hs with heap hstore`, then
  `heap_step hs with value hload`, then `res_step hs` at a terminal success.
  Use distinct names that are not already in the context. Failed rules
  restore the prior proof state. Missing bounds or permissions are refused;
  no unchecked rule result or sorry can select the output. The tactic also
  handles local result matches with generalized proof arguments. Explicit
  dependent match equations and several value discriminators are refused.
  This automates semantic heap operations. It does not prove an arbitrary
  physical machine write is permitted, discover an invariant, or construct
  the model encoding or next simulation relation. Use `array_update`,
  `word_arith` and `sim_state` for those separate proof steps.
- `heap_frame` proves exact load/store results and selects held subheaps. It
  finds explicit objects inside cons and append, including unknown list frames.
  It checks writability and bounds, and keeps each untouched object unchanged.
- `array_update [encoding_rules]` proves list and vector equalities for encoded
  array updates. It uses pointwise indexing for `List.set`, `Array.set`,
  `Vector.set`, `setIfInBounds` and `Vector.ofFn`. It supports maps, ranges,
  `getD` and list appends. An interval encoding `old.length ≤ i ∧ i < current.length`
  with `current = old ++ [item]` reduces to one vector update. Empty intervals
  and updates outside the vector capacity keep the original vector. Two vectors changed at the same index can encode one
  machine word. Supply opaque encoding definitions as extra rules. The
  procedure keeps fixed capacities and opaque encoders from being expanded
  during rule matching. It proves only the equality; memory permissions and bounds remain
  separate premises of the heap operation.
- `word_arith [h₁, ...]` proves natural-number and bit-vector arithmetic with
  only the listed premises. With no arguments it proves an unconditional fact.
  Opaque scalar expressions become fresh parameters of a separate theorem.
  This keeps heap facts and computed vectors out of the solver. It normalizes
  `BitVec.ofNat` casts and tries `ac_rfl`, `omega`, then `bv_decide` with a
  ten-second solver limit. It contains no program, address or layout names.
  Supply a required bound explicitly, for example `word_arith [indexBound]`.
  It does not prove an unbounded natural subtraction equal to word subtraction.
  On failure use another tactic; the original goal remains available.
- `heap_slice` proves byte loads inside an object, word array, or fixed-size
  record array. Use a byte-range result for a partial cell or a range across
  cells. Opaque record encoders need a fixed-size hypothesis.
- `heap_call rule` applies a checked callee theorem and tries the known heap
  premises. Missing premises remain as goals. A generated `call_summary`
  constructs a return witness from a semantic result. It does not identify an
  arbitrary observed return state with that witness.

For an encoded store, prove the encoded-list equality with `array_update`,
rewrite the new object to `Obj.words ... (oldWords.set index value)`, then use
`heap_frame`. The frame procedure abstracts a computed word list while it
checks the operation, retaining its length. Explicit word lists keep their
scalar values available for loads. Mapped heap lists stay opaque
frames; expose the selected object or supply a membership fact for a load.

Frame reassembly needs the output heap, its shape relation, and a proof that
the call preserves frame contents. Shape alone does not prove those contents.
Use `Heap.Holds.focus` with an explicit permutation when selection changes
object order. Model byte loads and concrete machine access permissions are
separate proof obligations. See `Lift/Sem/README.md` and the tests in
`Lift/Tactic/Test/HeapFrame.lean` and `Lift/Tactic/Test/HeapRanges.lean`.

## Checklist

1. Read the statement: the program, `Q` (fall-through), `E` (exits), the hypotheses on memory.
2. Write `vcgen [prog, callee specs…] invariants · I · var with try kfinish`, then
   `trace_state` and `all_goals sorry`.
3. One invariant case per label: the entry `s' = s₀`, the loop facts, `rsp`, the memory facts;
   `| _ => False` for the rest. A variant that decreases on each back edge, and that does not grow
   on the edge from the entry into the loop (give the entry label a value, such as the count).
4. Read the `fuzz:` message of the check report first (section "Test an invariant before you
   prove it"): the test runs by itself at each `vcgen` of a loop that leaves VCs open. A failure
   there is a wrong invariant, variant or postcondition; correct it before you read the VCs. In
   one run, a variant without a value at the entry label cost 19 turns of reading VCs; the test
   reports that error in its message.
5. Read the VCs that remain, strengthen the invariant, repeat. Write a spec for each instruction
   without one. A VC `⊢ Program.Intercept [labels] …` is a jump VC: use `with skip`, then
   `case vcN => apply Program.Intercept.intro_label (i := k) rfl`, `left` or `right`, `grind`
   (section "When `kfinish` fails"). Do not use `simp_all` on it.
6. When none remain, use `with kfinish` and remove `trace_state` and `sorry`.


### Construct a simulation state relation

Use `sim_state` on a structure proposition that relates record states. It is available
through `Lift.Tactic.LoopClose`; keep the frozen imports unchanged. The tactic uses the
relation's constructor and makes one goal for each relation field, in constructor order.
It reduces projections of record literals while updated field values are helper parameters.
This keeps large UInt64 expressions out of repeated record reduction in the kernel.

For unchanged fields, use the corresponding field of the old relation. For an updated
register, prove its equality directly, for example:

```lean
sim_state
· exact h.input
· exact congrArg (fun v : UInt64 => v + 18446744073709551615) h.counter
```

The number and order of goals depend on the relation. The tactic does not infer a loop
invariant, evaluate a block, or supply memory permissions. Prove load, store, frame and
stack-room conditions from the current state. A missing fact must remain open. Do not
reuse permission or room facts after a memory update without a preservation proof.
`sim_state` only constructs the state relation; there is no complete `sim_step` driver yet.

For a proposition about updated record states, use `sim_state => proof`.
The proposition can contain conjunctions, existentials or a control-flow
constructor. The tactic replaces computed record fields by fresh parameters
while it checks `proof`, then applies that checked proof to the actual values.
The inner proof must close all goals. This form is useful when the invariant
uses fields that the step preserves:

```lean
sim_state => exact ⟨hinput, pre, m, hperm, hholds, hreg⟩
```

Use the witnesses and field order required by the current invariant. The
inner proof must hold for all values of the replaced fields. A fact about
an old changed field cannot prove a fact about its new value. This form
does not supply permissions, frame proofs or missing invariant facts.
A failed inner proof restores the prior goal.

The inner goal has record-literal projections reduced. The checked helper
keeps the original record expression as its result type. This avoids a
later comparison of two expanded updates when a supplied fact has a
different record expression in its type. For an unchanged field, use
`sim_state => exact oldFieldFact`. For changed fields, prove the new
relation from the operation result or a congruence proof. Abstraction
does not relate two different computed values.

For a nested `Lift.Sem.Res` match in a successful execution equation, use
`res_step hs with value hvalue`. It reads one exposed match from `hs`.
It introduces `value`, proves that the matched operation equals `.ok value`
as `hvalue`, and keeps the remaining execution equation under the name `hs`.
Repeat it for dependent reads. Expose only the required step definition first.
The tactic checks that failure inputs cannot give the successful output.
It refuses recovery branches that can succeed. It restores the goal on failure.
It does not split a remaining program branch or prove heap access permissions,
bounds, frame preservation or the next invariant. There is no complete
`sim_step` driver yet. The production tactic contains no client function,
label, register, layout or capacity name.

After the reads and required branch split, `res_step hs` handles a terminal
equation `.ok computed = .ok output`. It changes the goal from the predicate
of `output` to that of `computed`. It keeps the other hypotheses unchanged.
This avoids substituting a large state into the full proof context.
It requires successful results on both sides and supplies no invariant facts.
For example, a branch that changes only untracked registers can use:

```lean
res_step hs
sim_state => exact ⟨hinput, pre, m, hperm, hholds, hreg⟩
```

These steps do not implement the complete `sim_step` procedure.

Generated heap-shape proofs check each block in a separate theorem. The
final proof applies those checked steps with `Blocks.Returns.inv`. This
keeps the block calculations out of one large proof command. The generator
uses the actual callee interfaces and their checked shape rows. A missing
heap-callee shape row remains an error. These proofs establish shape,
not preservation of frame contents. A worker must still prove the frame
and the semantic state relation.

When the callee model is exported from an imported
`Module.skel_semantic.skel_call`, its checked
`Module.skel_semantic.call_shape` proves the callee's shape row directly.
The generator selects this proof only for a matching semantic capability
and byte-access mode. Do not copy its raw shape proof into another `Cal`
family. Without that capability, the code-derived proof path remains.

The library command `#realize_match_congruences` generates checked
congruence equations for matchers in their defining module. It prevents
sibling modules from creating equal public helper names independently.
This is a library build step. A frozen proof still keeps its original
imports and statements.



# Typed heaps and callee calls

Use `Heap.Holds.eq_of_sameShape` when two heaps have the same typed
layout and are held by the same memory. Shape alone does not imply equal
values. Keep both memory facts.

Use `heap_perm_step_typed hs` after exposing the next typed heap operation
in execution equation `hs`. Keep a heap permutation and its source
memory witness in context. It handles typed loads and stores, preserves
the next relation, and restores state if a candidate does not match.

Use `heap_partition_exact` to select explicit callee objects from the
caller heap. It infers the remaining frame. The prefix composition rule
uses explicit arguments, including the inferred remainder. The earlier
`heap_partition` version fails on the full MapInPlace object prefix.

For MapInPlace's `map(j,j)` call, use
`MapInPlaceCall.call_in_place`. It needs the actual caller heap, its held
memory, register bindings, `j : Fin 1024`, and the MapSpec result. It
returns the actual PermLift call, encoded result and exact updated caller
heap with held memory. Reuse the proved callee; do not unfold its
functional proof in the caller loop.

The loop bound is `min src.length tgt.length ≤ 1024`. Neither individual
list length is required to be at most 1024. Do not add that assumption.

These helpers are staged. Install their checked modules and imports
through a later checked recovery before adding this note to a worker's
primer. They are not yet part of the queued paid continuation.


For semantic/call model equality, use `bridge_case` to split only the next
result operation or exit condition. Expose the block definitions first.
Keep a constructor lemma for state conversion, then try that lemma and
reflexivity before another step. The tactic does not split conditions
inside a load/store argument or a register expression. It refuses an
unsupported front expression and restores its tactic state.


## Reuse a proved callee in a generated loop

A saved callee proof can run inside the caller's local proof scope.
Keep each helper module's opens within that helper namespace. Use full
callee names for the model, states, labels and summaries. An enclosing
caller declaration takes precedence over an open callee namespace.

Retain every helper needed by the generated row. A loop row can have
fewer dependencies than the complete function module. Do not depend on
private frame helpers unless that row imports them. Put small checked
facts in the local scope when needed.

The checked MapInPlace import candidates use the actual Map summary,
replay the callee in caller heap order, and keep the exact current heap
and memory witness through induction. The candidate contains its support
and does not import the caller. The generic heap support modules must
be installed before the main campaign can use this example.


### Preserve a caller frame across heap permutations

Use `heap_perm_step hs` to replay a byte load or store on a permuted
heap. Keep a current `List.Perm` fact and a current `Heap.Holds` witness.
A permutation alone does not imply that overlapping objects give the
same value. The tactic refuses a step without the required evidence.

`CallFrame.PermLift.canonicalAt` selects a callee input heap order. It
needs a proof of the selected permutation and a checked replay rule.
Keep the output permutation and the transformed owned prefix when you
reuse the result. A byte store can change that prefix while the caller
frame stays fixed.

Keep helper namespace opens local. Use full callee names in a caller's
proof scope. A local caller declaration can take precedence over an
opened callee name. Do not import the caller's generated module into
its own row proof. Place reusable callee facts in the checked callee
proof scope and use their exported names.
