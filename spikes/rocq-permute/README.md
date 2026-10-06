# Rocq Permute spike

This directory uses GPL-3.0-or-later. See [LICENSE](LICENSE).

The algorithm can stay the same. The proof scripts must be rewritten, and the
main library work is in the cycle-count and optimality proofs. This spike ports
the execution loop and checks proofs about termination, result values, and the
emitted swaps. It does not replace the Lean implementation.

The source inspected was commit `0e92d2a1a9b720a9e127814d8c2c4192055638ce`.
The five `Shuffler/Permute/*.lean` files contain 886 lines: 128 in `Defs.lean`
and 758 in the four proof files. They contain 50 named lemmas and theorems.
These counts exclude Mathlib and the shared stack and trace definitions.
`Permute` does not import the 431-line `Mapping.lean` module.

## Run the checks

From the repository root:

```sh
nix develop --impure --expr 'import ./spikes/rocq-permute/shell.nix' \
  --command sh spikes/rocq-permute/check.sh
```

The shell reads the repository's existing Nix lock directly to avoid the
worktree Git `narHash` error. The versions used for this
spike are Rocq 9.1.1, Stdlib 9.0.0, and MathComp 2.5.0. The script compiles in
a temporary directory and then runs `coqchk` on all five modules.

Validation completed: all five modules compile, all eight execution tests
pass, and `coqchk` accepts the modules and their dependencies. The spike has
409 lines of Rocq, including tests; its proof scope is smaller than the Lean
development, so this is not a full-port size comparison.

## What the spike contains

| File | Scope |
| --- | --- |
| `Permute.v` | Finite permutations, the search, the two swap branches, depth errors, and result types |
| `Proofs.v` | Decreasing measure, no fuel exhaustion, result correctness, legal swap traces, positive errors, and a result with its proof |
| `Compute.v` | Two proved equations and a tactic for execution tests |
| `CycleProbe.v` | One generic cost lemma using MathComp's existing orbit-count theorem |
| `Tests.v` | Eight tests of the actual Rocq implementation |

The tests cover an empty stack, identity, a top swap, a cycle below a fixed
top, equal values, depth 16, a blocked depth-17 top swap, and a blocked cycle
below a fixed top. Successful tests check both values and the exact depth
sequence. Equal values still cause swaps, as in the current Lean code. The
two C++ matching TODOs in `Defs.lean` are not implemented here.

`run_correct` proves that a successful result has value `source (perm^-1 i)`
at every position `i`, for any value type and stack size. `run_trace` proves
that the returned trace consists of swaps that produce that result, with
depths from 1 through 16. Position bounds follow from the ordinal type.
`run_no_exhaustion` proves that the initial fuel is sufficient.
`certified_permute` returns the result together with these properties for
nonempty stacks, or a proof that a blocked error has positive excess.

The checked assumptions of `certified_permute`, the main loop lemmas, and
the cycle cost lemma are empty. There are no `Admitted` commands or added
axioms. The concrete tests use proved rewrite rules and `vm_compute`.

This is a proof about the Rocq implementation. It is not a machine-checked
equivalence between the Lean and Rocq programs. The code comparison and
regression cases provide the evidence for the translation so far.

## Changes needed for a full port

| Lean feature | Rocq choice tested here | Effect on the port |
| --- | --- | --- |
| `Equiv.Perm (Fin n)` | MathComp `'S_n`, permutations of `'I_n` | Keeps invalid permutations out of the input type |
| `perm * swap` | `tperm * perm` | Multiplication order is reversed between the libraries; copying the expression changes its meaning |
| `List Value` and length equalities | A function `'I_n -> A` | Removes length casts from this proof experiment; a list or tuple adapter is still needed for the existing API |
| `foldl` retaining the last moved position | Recursive last-moved search over the same ascending enumeration | Same selection order; this avoids dependent search results in the loop |
| Lexicographic termination measure | `2 * moved_below_top + top_is_fixed` | Same two progress arguments, expressed as one natural number |
| Well-founded `go` | Structural recursion on fuel, proved sufficient | No added termination assumption; the result with its proof excludes exhaustion |
| Indexed `Trace` in `Type` | Explicit depth list plus indexed `SwapTrace` in `Prop` | Trace data and its proof are separate; `certified_permute` joins them |
| `omega` | `lia`, after explicit Boolean/number conversions | Arithmetic transfers, but the proof steps need new scripts |
| `simp`, `ext`, generated recursion induction | SSReflect rewriting, permutation/set extensionality, and fuel induction | Proof structure transfers; tactic scripts do not |
| `native_decide` execution tests | Proved computation equations, then `vm_compute` | Direct reduction stops at MathComp's locked definitions; `Compute.v` supplies the required equations |

The representation changes are choices for this spike, not requirements of
Rocq. Rocq also supports dependent lists, tuples, indexed traces in `Type`,
and well-founded recursion. A literal port would retain more casts and need
different proof automation. The current function representation remains pure;
it is not yet an implementation of a C array.

## Cycle proofs and remaining scope

MathComp provides `porbit`, `porbits`, and `porbits_mul_tperm` in `perm.v`.
The last theorem states how the orbit count changes under a transposition.
`CycleProbe.v` uses it to prove that one swap can reduce the candidate
arbitrary-swap cost by at most one.

There is a representation difference: Mathlib's `cycleFactorsFinset` excludes
fixed points and contains permutations. MathComp's `porbits` includes fixed
points and contains sets of positions. The candidate arbitrary-swap cost is
therefore `n - number_of_orbits`, instead of
`support_size - number_of_nontrivial_cycles`. Their equivalence, the top-cycle
count, and the remaining optimality theorems still need proofs.

A full port must also provide:

- The list/tuple adapter and integration with the shared `Value` and `Trace`
  types. `Permute` uses only literal traces and swaps; the other trace
  constructors and spills are not exercised by this spike.
- Success for every reachable permutation, and the exact original-position
  witness for every unreachable error. The spike proves successful-result
  correctness and positive errors, not this reachability classification.
- Exact swap counts, minimum top-swap count, minimum arbitrary-swap count,
  and the factor-three bound. The single cost lemma is not a port of these
  complete results.
- Integration tests against the rest of the shuffler. No Lean files or their
  build configuration were changed.
- A C representation and a refinement proof against Rocq Clight. No Clight
  program, VST proof, printer, or ACSL specification is built in this spike.

For planning, I would classify the algorithm translation as low effort, the
shared API and reachability proofs as medium effort, and the complete cycle
and optimality layer as medium to high effort. A provisional budget is 3–5
engineer-days to finish a functional Permute port with the shared API, plus
5–10 days for the count and optimality results. These are estimates for an
engineer familiar with Rocq and MathComp, not measured completion times. They
exclude the rest of the shuffler and C verification. The cycle representation
is the largest source of uncertainty.

## Trust implications

Moving to Rocq does not by itself prove the emitted C correct. It permits
the refinement proof to use CompCert's original Rocq Clight semantics,
without the separate Lean transcription of those semantics. A direct Clight
AST plus a trusted subset printer remains a possible design.

The printer remains trusted unless its output is connected to the semantics
by a proof or a checked certificate. If GCC or Clang compiles the output, that
compiler also remains trusted for a claim about machine code. Using CompCert's
compiler theorem needs a further connection to its compiler path; the theorem
does not automatically apply to any Rocq program. The non-commercial license
boundary for CompCert's compiler components also remains in effect.

The next decision point should be one Rocq Clight function that performs an
array swap, with a proof that it refines `swap_stack`. That would test the
memory representation and proof-library/toolchain fit before a full migration.
