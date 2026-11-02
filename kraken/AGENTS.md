# Guidance for proofs in kraken/

This file is for persons and agents that write Lean proofs about the asm in this directory.
It gives the rules for fast and stable proofs, and it tells how to use the Kraken tactics and the
tactics of this repo.

## Layout

| Path | Content |
|---|---|
| `Theorems/Main.lean` | the main planner statements, their assumptions, results, and trust boundary |
| `Theorems/` | the review definitions: input assumptions, result comparison, encodings, and machine contract; no proof tactics |
| `ShufflerBridge/` | correspondence proofs for emission, spills, and the planner |
| `FlatShuffler/Permutation/` | the permutation model and trace lemmas used by the C++ proofs |
| `FlatShuffler/` | the models, contracts, and assembly proofs of the C++ shuffler methods |
| `FlatShuffler/Kit.lean` | the shared lemmas and macros of the bbu proofs (`rd`, `bbu_norm`, `bbu_flags`, `bbu_rd`) |
| `FlatShuffler/Fn/` | one file (or directory) for each function of the asm |
| `FlatShuffler/Sep/` | the separation library: atoms, the struct view, the contracts with a frame (see below) |
| `ProofKit/` | proof tools that do not depend on one function: `Shape`, `SymExec`, `Cfg`, `Idioms`, `SepLoad` |
| `ProofKitTest/` | tests of the ProofKit tools on real `kvcgen64` VCs |
| `test/` | shell tests: the model against the originals, the binary against the asm, the struct layout, the axioms; the field generator `gen_fields.sh` |

## Build and check

- Run `lake update` from the repository root after checkout.
  The pinned Kraken dependency is used without source changes.
- Run the full build from the repository root: `lake build`. It includes the
  assembly proofs, the correspondence proofs, and `Theorems.Main`.
  Run the build commands in this section from the repository root.
  Both packages use the root `lean-toolchain`. The shell tests use the root dependency graph.
- Both local packages pass `-E warning` to Lean. Dependency warnings remain visible.
- Start files that import `Theorems.Main` with `module`. Its public contracts
  keep the Kraken and Shuffler implementation imports private.
- Run `kraken/test/modules_test.sh` to check this boundary.
- Run only one Lean process at a time. The machine is shared.
- Do not kill a `lean` or `lake` process that you did not start. Do not use `pkill lean` or
  `pkill lake`.
- The proof build generates `build/kraken/c/build_bottom_up.S` with CMake and GCC 15.3.0.
  The assembly is not kept in source control. Use `nix develop` for these tools.
- One target: `lake build FlatShuffler` (or `ProofKit`, `ProofKitTest`).
- One file, without a build of its dependents:
  `lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false kraken/FlatShuffler/Unit/Push.lean`.
- Find the slow declarations:
  ```
  lake env lean -Dtrace.profiler=true -Dtrace.profiler.threshold=200 -DElab.async=false FILE
  ```
  The profiler adds time. A proof that is near its heartbeat limit can fail under the profiler.
- Heartbeats do not change from run to run. Wall time changes by about 20% on a machine with a high
  load. Compare heartbeats, not seconds. To measure one declaration, read `IO.getNumHeartbeats`
  before and after it.
- Axioms: `kraken/test/axioms.sh` checks the listed final and transfer theorems;
  `kraken/test/axioms.sh FILE NAME...` checks the theorems NAME... of FILE.
  `kraken/test/axioms_test.sh` tests the check. Permitted:
  - `propext`, `Classical.choice`, `Quot.sound`;
  - the `bv_decide` axioms. On this toolchain, each use of `bv_decide` adds one axiom
    `D._native.bv_decide.ax_I_J` with the type `Std.Tactic.BVDecide.Reflect.verifyBVExpr _ _ = true`.
    An axiom with this name and a different type is not permitted.

  Not permitted: `sorryAx`, the `native_decide` axioms (`D._native.native_decide.ax_I_J`) and all
  other axioms. Do not write an `axiom` declaration: a user axiom with the name and the type of a
  `bv_decide` axiom is not different in the environment, so `test/axioms.sh` rejects each `axiom`
  declaration in the `.lean` files of this package.
- `bv_decide` is for small lemmas on words, as in `ProofKit/Idioms.lean`. It does not close the VCs
  of a function proof (see the KrakenTactics section).

## Rules for efficient proofs

Most of the time of the old proofs is in the discharge steps after `kvcgen64`. It is not in
`kvcgen64` or in the kernel. Example, `swapWith_body` (133 s): the kernel takes 0.35 s, `kvcgen64`
takes less than 2 s, and one `all_goals` block with `omega` alternatives takes 100 s.

1. **Do not use a `first | … | …` cascade of `omega` calls.** A failed `omega` is slow. A
   cascade of 20 alternatives that each try `omega` can take 3 to 28 s for one goal. Select the
   lemma from the form of the term (a field name, an address shape) and use `omega` only on the
   side goals of that lemma. Example: a field-read lemma set and a `simp only` with a direct
   lookup took 0.43 s for 5 goals. The `omega` cascade took 50.3 s for the same 5 goals.
2. **Put addresses in one normal form before you use a lemma on them.** `simp` lemmas and
   `ecancel` match terms, not values. `S + 72#64` and `S + BitVec.ofInt 64 (Int64.toInt 72)` are
   different terms. Normalize the address to `base + constant` or to a named field term first.
3. **Write one lemma for each block of a large function.** Lean cannot check the parts of one
   declaration in parallel. When one step changes, Lean checks the full declaration again. Use
   `#cfg_skeleton` to get the blocks, and prove each block in its own lemma when the block is large.
4. **Keep the context of `omega` small.** `omega` reads all the arithmetic hypotheses. Give it only
   the facts that the goal needs (`revert` or a `have` with a small statement, then `omega`).
5. **Keep a margin to the heartbeat limit.** A proof that uses more than about 50% of its
   `maxHeartbeats` can fail after a small change in Kraken or in the compiler output. Example:
   `push_body` used 88-94% of the default 200000. Make the proof faster before you increase the limit.
   If you increase the limit, use `set_option maxHeartbeats N in` on that declaration only.
6. **Use names that do not depend on the asm.** The `vcN` tags of `kvcgen64` change when the
   compiler adds or removes an instruction. Select the goals by block (`cfg_blocks`) and by kind
   (`vc_by_shape`), not by `vcN`, in new proofs.
7. **Do not unfold large recursive definitions.** Keep definitions such as an array of 1024 words
   out of the `simp` sets. Prove `rd`/`store`/`isSome` lemmas for them by induction, and use only
   those lemmas.
8. **Give the values when the goal has metavariables.** `ecancel` and `simp` can time out in `whnf`
   when an atom value is a metavariable. Give the value as a named argument (`(v := …)`) when you
   apply the lemma.
9. **State compiler-pattern lemmas on words and model values**, not on `Mem`. Put a general lemma
   in `ProofKit/Idioms.lean`, and add a test for it on a real VC in `ProofKitTest/Idioms.lean`.
10. **Make each change small and check it.** Check the file after each block proof. Do not write a
    long proof and then check it one time.

## Kraken tactics (Kraken rev 2fd79ae)

### `kvcgen64 [specs] (with discharge)?`

- This is `vcgen` with the machine state folded as it steps: register writes become a literal of
  the register file, register reads from the literal become the field, and ground arithmetic and
  flags are evaluated.
- Give the specs of the instructions and of the called functions in the brackets, for example
  `kvcgen64 [hscp]`.
- The goals that stay are the VCs: loads in mapped memory (`(Mem.loadInt m a n).isSome = true`),
  `retAddr.isSome`, jumps (`Program.Intercept …`), the invariant of the next block, and flag facts.
- Known limits:
  - It keeps the `{..}.status` projection in jump hypotheses. Use
    `rw [MachineData.status_mk, …] at hj` or `idioms at hj`.
  - It does not reduce `get64` of a register-file literal in the else-branch of a `cmov`. Close
    it with `rfl`.
  - `addq` gives `src + dst`, not `dst + src`.
  - The immediate of `cmp $k` is an `Int` literal and a `BitVec.ofNat` literal. A `simp` lemma with a
    variable in that position does not match a literal.

### `Program.WP.cfg`, `cfg_cases`, `cfg_view`

- A function proof starts with `refine Program.WP.cfg (fun | .entry, t => … | .label l, t => … |
  .exit, _ => False) (variant) ?_ rfl`.
- `cfg_cases` splits the goal into one goal for each block. The tags are `left`, `right.left`,
  `right.right.left`, …. Use `cfg_blocks` (ProofKit) to get the label names as tags.
- `cfg_view as h` gives the equation of the blocks of the program. `cfg_cases` uses it.
- `Program.Intercept.intro_label` and the grind extension `cfg_exit` close the label lookup of a
  jump. `cfg_goto` (ProofKit) does the same as a tactic and leaves three goals.

### `ecancel` (Kraken.SeparationTactics)

- It proves `P = Q` and `P ⊑ Q` for `MProp` assertions up to the associativity and the commutativity
  of `∗`. It can assign a metavariable for the rest (`?R`).
- `∗` is exact: `(P ∗ Q).get m` splits all of `m`. A top-level frame must hold all other memory.
- It matches atoms by term. Normalize the addresses first (rule 2). Give the atom values (rule 8).
- Lake builds a module of the Kraken package only when a module of this package imports it.
  `FlatShuffler/Sep/Atoms.lean` imports `Kraken.SepCancel`, so `lake build` builds the separation
  modules. Library proof files start with `module`. The executable entry files can use the
  older import system because the packages set `allowNonModules`.
- `FrameWP` (X64/WP/Frame.lean) has no cfg rule and no call rule. Use the state wp
  (`Program.WP.cfg`, `kvcgen64`, `CallSpec`) and put the `∗` assertion inside the invariants and
  the contracts.

### KrakenTactics: `kfold`, `clear_dead`, `kfold_discharge`

Do not use them in this repo. Measured on 5 function proofs:

- `kfold`, `clear_dead`, `kfold_discharge` and `bv_decide` close 0 of the VCs.
- `bv_decide` gives "potentially spurious counterexample", because memory and `Mapped` become free
  atoms.
- `kfold` before the original steps adds 0.2-0.7% heartbeats and breaks `permute_spec`.
- `clear_dead` breaks all 5 proofs:
  - it removes hypotheses that later steps use by name;
  - it keeps the old local instances (ClearDead.lean:103), so instance synthesis can return a
    removed free variable ("unknown free variable");
  - it takes 4.6 s for each goal on `swapWith_body`.
- `Fold.lean` does not compile as a module on this toolchain (a `meta` error). `KrakenTactics` is
  not a default target, so the normal build does not show this.

## Tactics of this repo

All the tools in `ProofKit/` are untrusted: they only make terms or select tactics, and the kernel
checks the result.

### ProofKit/Cfg.lean

| Tactic | Use |
|---|---|
| `cfg_blocks` | `cfg_cases`, then each block goal has the tag of its block (`entry` or the label). Select a block with ``case «.LB.Emission.push.0» t ht => …``. |
| `cfg_goto` | A jump to a label of the cfg. It leaves three goals: the stack, the invariant of the label, the variant. |
| `cfg_stk` | The stack goal of `cfg_goto` when `rsp` is below the `rsp` at entry. |
| `vc_by_shape \| kind => tac …` | Runs `tac` on each goal of that kind. The kinds are `load`, `retAddr`, `goto "L"`, `ret`, `jumpOut`, `fall`, `closed`, `other`. The first arm that matches is used. A goal that no arm matches stays. A tactic failure is an error that gives the kind and the tag. |
| `#cfg_skeleton p` | Prints a `Program.WP.cfg` proof for `p` with a `sorry` for each invariant, each variant hole and each block. A label gets a variant hole if it is on a cycle, if a block at or after it jumps to it, or if it reaches such a label. The entry proof is a `sorry` too. |

Notes:
- `kvcgen64` splits `I ∧ Decreases`, so the parts of a fall-through show as `other` and `closed`,
  not as `fall`.
- After `cfg_goto`, the variant goal is an unreduced `match`. `decide` fails on it. Use `simp`.

### ProofKit/Shape.lean

- `vc_shapes` logs `tag: kind | target` for each goal. Use it to write the arms of `vc_by_shape`.

### ProofKit/SymExec.lean

- `#symexec p from "L" (using tac)?` runs `kvcgen64` on the block at label `L` from a free state, then
  `symexec_norm` (or `tac`). For each exit `i` it adds the definitions `….L.x{i}.cond` and
  `….L.x{i}.st`, and it logs them as text.
- Use these definitions in the invariants, for example `t = x1.st (s.pushRa ra)`. Then
  `exact Or.inl rfl` closes the invariant goal by definitional equality.
- The printed text of `st` does not elaborate back to the same term (the flags print with `Nat`
  casts). Use the definitions, not the text.
- `symexec_norm` is the default normal form: the `kvcgen64` register lemmas, literal evaluation and
  `ofInt (toInt x) = x`, `at *`. `symexec_norm at loc` normalizes only `loc`. With large
  hypotheses in many goals, use `symexec_norm at ⊢` and normalize the branch hypotheses that a case
  uses. In `Unit/SwapWith.lean` (35 goals, 15 sep hypotheses), this changes the proof from about
  130k to about 90k heartbeats.

### ProofKit/Idioms.lean

- Lemmas for the `g++ -O1` instruction patterns: `cmp`/`test` + `jcc`, `setcc` pairs, `cmov`,
  `lea` address forms, slot pack and unpack, slot compare, the `Status` return values.
- Two ways to use them:
  - `rw [Idioms.cmp_a_imm _ _ (by decide)] at h`: one composite lemma for each pattern.
  - `idioms at h ⊢`: a `simp only` set that puts flags, shift counts, `setcc` bytes and slot words
    in a normal form for `omega` and `bv_omega`.
- For a literal immediate with `rw`, use `cmp_*_imm (w := 64) _ k (by decide)`.
- `setne`/`sete` write only bits 0..7. The lemmas give `.take 8` of the result.
- No lemma yet: `movw`/`movzwl`, byte loads of slot fields, `movb` stores. These are memory patterns.
- 9 lemmas use `bv_decide` (`pack40_*`, `pack32_*`, `slot_eq_iff`, `slot_beq`, `extract48_eq_iff`).

### The separation library (FlatShuffler/Sep/, ProofKit/SepLoad.lean)

| File | Content |
|---|---|
| `Sep/Fields.lean` | The address of each member of `Emission` (`Fld.stack_size S`, `Fld.mapping_positionOf S i`, …) and the `fold_*` lemmas from the asm address forms. It is generated. Do not edit it. `Sep/Off.lean` has the offset lemmas that it uses. |
| `Sep/Atoms.lean` | The atoms `Wd`, `B8`, `B16`, `B32` (8, 1, 2, 4 bytes) and `Arr` (words), with their load and store lemmas. `Wd.split` and `Wd.store411` for the 4+1+1-byte slot store. `Wd.rdb_byte` for one byte of a word. |
| `Sep/View.lean` | `View S g`: the struct, the working stack, the trace buffer, the target, and the spilled bytes that are not in the target (`splOut`). `G.Ok.spl` gives the value of a spilled byte in the target. The ghost `G` has `Vector` fields, so an array of the wrong length does not typecheck. `OpM` is one 12-byte record. |
| `Sep/Stores.lean` | One load and one store lemma for each field, `View.focus`/`unfocus` for a record, `View.rdb_spl` for a spilled byte (with `G.Ok`), and `view_load`. |
| `Sep/Contract.lean` | `Stk`, `Pre`, `Post`, `Body`, `Spec`, `spec_of_body`, and the body state `Kp` (`init`, `next`, `retAddr`, `ret`, `agree`). |
| `Sep/*Test.lean` | Tests. `ContractTest` has a body with `pushq`/`popq` and a call through a `Spec`. |

- The memory part of each contract is `(View S g ∗ Stk sp fr v ∗ F).get m`. The frame `F` is a
  parameter. At a call, the caller gives its return slot and `F` as the frame of the callee
  (`Stk.call`). See `cal_body` in `Sep/ContractTest.lean`.
- `sep_load [l₁, …]` (ProofKit) closes a load VC. It tries `with_reducible apply l h` for each lemma
  `l` and each hypothesis `h : (P ∗ F).get m`, and closes the side goals with `assumption`.
  It tries first the hypotheses at the memory term of the goal. In `dup_unit` (14 such
  hypotheses, 20 load goals), this order decreases the heartbeats from 112260 to 83564.
  `view_load` is `sep_load` with the `View` and `OpM` lemmas.
  - The match is reducible: the memory and the address of the goal must be the same terms as in the
    hypothesis. Fold the address first (`rw [hS, Fld.fold_stack_size]`). In `rbx_body`, the stack
    addresses (`(s.pushRa ra).regs.rsp.toBitVec - 8#64` and `rsp s - 8#64 - 8#64`) are equal only
    by unfolding, so `exact` is necessary there.
- A load value goal after `symexec_norm` is `BitVec.ofInt 64 (Mem.loadInt m a 8).get! = …`.
  `exact View.rd_len hm` closes it (`rd` unfolds). To put a loaded value in a store, use
  `change (_ ∗ F).get (Mem.storeInt _ _ 8 (rd t.dmem A).toInt)`.
- When the ghost in the hypothesis is not the same term as in the goal (for example
  `{ g with … }`), use `(View.rd_data h :)`: the term elaborates with no expected type.

Traps:
1. **A lemma of one atom on a hypothesis with another atom first can take a `whnf` timeout.**
   With reducible atoms, `exact B8.isSome h` with `h : (B32 a x ∗ F).get m` took a timeout at
   400000 heartbeats (about 22 s). `fail_if_success` and `try` do not catch a timeout. For this
   reason, the atoms are `@[irreducible]`: the same step fails in less than 1 s. In a proof of an
   atom lemma, use `unfold Wd at h ⊢`. In a tactic that tries lemmas, use `with_reducible`.
2. **A tactic that tries lemmas must not take a logged error as a success.** In a tactic block,
   `apply l h` with an `h` that does not fit `l` logs an error, changes `l h` to `sorry` and closes
   the goal. Run `apply` under `Term.withoutErrToSorry`, as `sep_load` does.
3. **In `fail_if_success`, put the tactic form and `done`.** An error in a nested `by` in a term is
   logged, not thrown. Then the tactic in `fail_if_success have … := f h (by simp)` succeeds when
   `simp` fails, and the negative test does not test the step. Write the steps as tactics:
   `fail_if_success (apply f h; simp; done)`.

### The field generator (test/gen_fields.sh)

- `test/gen_fields.sh` writes `FlatShuffler/Sep/Fields.lean` from the g++ `offsetof` and `sizeof` of
  `Emission` in `c/shuffler/stack/Shuffler.cpp`. Run it after a change to the struct.
- `test/gen_fields.sh --check` does not write the file. It fails if the file is not current.
- It fails if the struct has bytes that no member of the probe covers (a hole, or bytes after the
  last member), or if an array element is not 8 bytes. `test/gen_fields_test.sh` tests these
  cases and `--check`.

### FlatShuffler/Kit.lean

| Tactic | Use |
|---|---|
| `bbu_norm (at h)?` | The normal form of the `kvcgen64` goals: registers, `pushRa`, `wordAt`, literal arithmetic. |
| `bbu_flags (at h)?` | A flag hypothesis of an unsigned or equality jump, as a `Prop` for `bv_omega`. Then use `borrow_iff` / `no_borrow_iff` for the carry flag. |
| `bbu_rd (at h)?` | A read after 8-byte stores, with `rd_store_same` and `rd_store_other`. The side goals use `bv_omega`. |

`bbu_rd` tries `bv_omega` on each store in the chain. It is correct, but slow on long chains of
stores. Do not add a `first` cascade around it (rule 1).

### File-local macros

These macros are for one proof. Do not copy them into a new file. If a new proof needs the same
step, move it to `Kit.lean` or `ProofKit/`, with a test.

- `FlatShuffler/Fn/PushDup.lean`: `addr_omega`, `pd_clear`, `pd_off`, `pd_disch`, `pd_rd`. `pd_disch`
  is an `omega` cascade (rule 1).
- `FlatShuffler/Fn/SwapWithLemmas.lean`: `in_omega`.
- `FlatShuffler/Fn/Loop/Defs.lean`: `loop_case`, `loop_goto`.
- `FlatShuffler/Link.lean`: `head_tac`, `at_tac`.
- `FlatShuffler/Unit/SwapWith.lean`: `mem_load`, a `sep_load` that tries only the hypotheses on the
  memory of the load. Tests in `Unit/SwapWithTest.lean`.

## Procedure for a new function proof

1. Get the skeleton: `#cfg_skeleton p`. Copy the output into the file.
2. Write the invariant of each label. For a straight-line block, use `#symexec` to get the exit
   states as definitions.
3. In each block: `kvcgen64 [specs]`, then `vc_shapes` to see the goals.
4. Replace `vc_shapes` with `vc_by_shape`. Write one arm for each kind. Use `idioms` for flags and a
   field lemma, `view_load` or a `∗` lemma for each `load`.
5. Check the file. Read the heartbeats of the new declaration (rule 5).
6. Check the axioms with `test/axioms.sh FILE NAME`.
