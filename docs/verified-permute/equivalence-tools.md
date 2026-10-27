<!-- SPDX-License-Identifier: GPL-3.0-or-later -->
# Tools for checking C and solc Permute equivalence

Review date: 2026-10-06. This report started as a source and documentation
review. The rankings below are initial engineering estimates. Later trials
are recorded in [the SAW checker](../../spikes/clight-permute/tests/equiv-saw/README.md)
and [the Alive2/KLEE checker](../../spikes/clight-permute/tests/equiv-alive2/README.md).
Their measured results and limits take precedence over these estimates.

## Answer and recommended order

**Yes.** Clang can put the generated C and the solc C++ implementation
into the same LLVM representation. A tool can then compare their behavior
through wrappers with the same interface. This does not make their LLVM
functions easy to compare: the C uses arrays and loops; the C++ oracle
uses vectors, optional values, range-v3, sorting, and allocation.

For this exact source, start with **SAW/Crucible and small fixed sizes**.
It has memory specifications and function contracts that can support the
C++ library boundary. Use the actual pinned solc code. Do not replace its
sort with a new algorithm and call that a proof about solc. If the initial
translation works, assess the cost of contracts and loop invariants before
attempting all sizes through 1024.

Alive2 can compare separately written LLVM functions. It is less suited
to this first trial because it checks refinement, uses bounded loop
unrolling, and does not support general interprocedural transformations.
CBMC is a useful second route if its C++ frontend accepts the actual
oracle. KLEE is useful for symbolic counterexamples. None is a documented
one-command proof of this complete C/C++ pair.

| Tool | Fit for this Permute pair | Main limit |
| --- | --- | --- |
| SAW/Crucible | First LLVM trial; verify matching observations through memory and function contracts | C++ library code, heap behavior, and loops need work; LLVM semantics has documented limits |
| CBMC | Second trial; assert equality after two calls with symbolic inputs | Own frontend must accept the C++20/range-v3 code; large loop bounds can be costly |
| Alive2 | Try after calls are inlined or have justified models; useful for compiler transformations too | Refinement, bounded loops, no general interprocedural proof |
| KLEE | Find counterexamples with symbolic values and small sizes | Path growth and external calls can prevent complete exploration |
| SeaHorn | Research route for invariants over the LLVM program | Framework integration and memory reasoning; documented LLVM 14 toolchain |
| SMACK | Possible after substantial source/toolchain work | Current README supports C only; unbounded mode is experimental |
| Symbiotic | Additional safety/counterexample route | Tool pipeline and supported properties need review; no automatic relational proof |
| llreve | Relevant relational verification design | Old LLVM 5/Z3 4.5 toolchain, partial LLVM coverage, strong safety assumptions |

## State the comparison before selecting a tool

The C function has seven arguments. The oracle in
[`oracle.cpp`](../../spikes/clight-permute/tests/oracle.cpp) has five.
The C function's two extra scratch arrays are private implementation
state. Equal argument counts are not required in the source. Matching
verification wrappers must expose one common contract.

Use the existing comparison in
[`check_case.c`](../../spikes/clight-permute/tests/check_case.c) as the
observation boundary:

* `1 <= n <= 1024`; each data element is an arbitrary 32-bit unsigned
  value. Equal values are allowed. Restrict the second input to a valid
  permutation of `0 .. n-1`.
* Give both calls equal input values and separate private storage. Meet
  the C buffer size, lifetime, alignment, and separation requirements.
* Compare the status, final or partial `data[0:n]`, trace length, written
  trace prefix, blocked position, and excess depth.
* Do not compare private scratch arrays, allocation addresses, object
  padding, or the unwritten trace suffix. Reading an unwritten element
  can itself invalidate a proposed verification harness.
* Prove that the trace length is in range before using it as a comparison
  bound. Keep oracle assertions active and prove that none fails.

The full unsigned domain matters: a test restricted to small distinct
values omits both high-bit behavior and duplicate normalization.
Equivalence here means the exact trace and blocked result, not only an
equal final permutation.

The solc operation requires a valid nonempty permutation. Empty,
oversized, and invalid C inputs have a separate C API contract. They must
not be passed to the oracle to extend the comparison domain.

C++ vector allocation can fail and throw. The C function does not
allocate. Either include exceptional behavior in the observations, or
state and justify a successful-allocation/no-exception condition for the
comparison. A verifier override for an allocator or a library function is
an assumption until its required contract is proved. It must not silently
remove relevant behavior.

### Refinement, equivalence, and bounds

Alive2 checks that the target refines the source. A source execution with
undefined behavior does not impose the same requirements as a defined
execution. Thus, a refinement result alone is not symmetric equivalence.
Check both directions, or prove safety and termination for both programs
on the common domain and compare their deterministic observations.

A result for `n <= 5` does not prove a result for `n <= 1024`. However,
bounded checking can prove the entire supported domain if the bounds are
complete and their sufficiency is established. For CBMC, this includes
successful unwinding assertions. A timeout, an unknown solver result, or
a dropped path is not a proof. Invariant proofs can avoid full unrolling,
but must still cover the memory relation and all required observations.

## Tool details from primary sources

### Alive2

The [README][alive-readme] describes the standalone `alive-tv` tool and
states that it does not support interprocedural transformations. This
does not ban every call: Alive2 has call models. It means that a call to
the C++ library does not cause Alive2 to prove that library body equal to
the C array code.

Current [command options][alive-options] include `--src-unroll` and
`--tgt-unroll`, both defaulting to zero. The
[implementation][alive-unroll] returns without unrolling for zero. The
[validator][alive-validator] detects some insufficient bounds and has
checks intended to prevent false positives from bounded unrolling.
These checks do not establish a user-selected maximum size by themselves.
The [PLDI 2021 paper][alive-paper] explains the bounded validation design.

The current project targets LLVM main. Select compatible LLVM and Alive2
commits together. First compare a small wrapper whose relevant callees
are visible and inlined. Inspect remaining calls, loop bounds, and the
reported result before making an equivalence claim.

### SAW and Crucible

SAW's [verification manual][saw-verify] supports LLVM memory specifications,
symbolic allocation, array prefixes, and compositional function contracts.
These features make it a plausible fit for equal inputs and observations
with different private representations. They do not supply verified
contracts for this oracle's vector, optional, and sorting operations.

The current manual also describes experimental **cutpoints** for loop
invariants. They require inserted `__cutpoint__...` calls and an inductive
contract proof. The manual states that this gives **partial correctness**,
not termination. Without invariants, symbolic execution can require
concrete bounds and can suffer path growth.

Crucible documents [LLVM limitations][crucible-limits], including limited
poison handling and inaccurate `freeze` behavior in some cases. Start with
lightly optimized LLVM and check which instructions occur. Do not disable
memory checks to make verification pass. A result applies to the modeled
LLVM semantics and stated contracts, not automatically every LLVM feature.

There is a version mismatch to resolve: the pinned Nix package is SAW
**1.5**, whose [release README][saw-release] lists LLVM support through
20.0. This workspace uses Clang 21.1.8. The reviewed
[current README][saw-readme] lists support through 23.0. Pin a compatible
source build or use a documented compiler version for the experiment.

### CBMC

CBMC supports [C and C++][cbmc-readme] and can check a harness which calls
both functions and asserts equality. It does not use Clang's LLVM as its
main input route. Acceptance of this exact C++20/range-v3 program remains
untested. Parsing a smaller reimplementation would answer a different
question.

Use [unwinding assertions][cbmc-unwind] to establish loop-bound sufficiency.
Do not treat `--partial-loops` as a complete proof. Include pointer,
bounds, and arithmetic checks suited to the actual source. For fixed
small sizes, all values can remain symbolic; the value space need not be
enumerated explicitly. Feasibility for all sizes through 1024 is unknown.

### Other symbolic and relational tools

[SeaHorn][seahorn-readme] offers bounded checking and Horn-clause invariant
reasoning. Its current README uses LLVM 14 and describes a research
framework. This pair needs memory reasoning; scalar-only analysis cannot
prove array or trace equality. Its memory tracking options and C++ input
support need a concrete trial.

[SMACK][smack-readme] defaults to bounded verification. Its unbounded mode
is experimental, and the README says only C is currently supported.
Its [installation guide][smack-install] lists LLVM/Clang 12.0.1. A common
LLVM format alone does not remove those frontend and runtime limits.

[KLEE][klee-readme] can execute a two-call assertion harness with symbolic
data and permutation constraints. Keep relevant callees in bitcode and
audit [external-call policies][klee-options]. Concretized calls and paths
lost to time or memory limits prevent a general conclusion. Complete
exploration with no errors can establish the chosen finite case, provided
the modeled runtime and all assumptions are adequate.

[Symbiotic][symbiotic-readme] combines instrumentation, slicing, and
verification, with KLEE as its default engine. It can check a relational
assertion if the full harness is supported. Its current build instructions
show a much older default LLVM toolchain. Do not assume it accepts the
workspace's LLVM 21 output unchanged.

[llreve][llreve-readme] is designed for relational verification of LLVM
programs, with matching points and relational specifications. It is a
useful reference for a loop relation between the two implementations.
Its [tool guide][llreve-guide] requires LLVM 5.0 and Z3 4.5 and reports
problems with newer versions. It supports only part of LLVM and assumes
memory safety and absence of integer overflow/underflow. Those assumptions
need separate evidence; they are not results of an equivalence check.

## ACSL, Frama-C, and the printer

[Frama-C WP][frama-wp] can prove ACSL function contracts and loop invariants
for the small generated C. [Eva][frama-eva] can analyze runtime errors.
This is a useful independent check of the printed C. Frama-C does not
directly handle the full solc C++ source in this plan.

WP contracts could state bounds, separation, trace validity, and the
functional relation to a mathematical Permute specification. Exact trace
equivalence needs that stronger specification; a contract about the final
array alone is insufficient. Use Why3 with explicitly selected permitted
provers, such as Z3. **Do not use Alt-Ergo.**

These checks do not prove that the printer preserves Clight semantics.
That link needs a theorem about the printer and a C semantics, or an
independent proof that each emitted program meets the intended contract.
If the same printer emits both C and ACSL, a common error can affect both;
review the specification independently. Neither path supplies CompCert's
compiler theorem for GCC or Clang. An LLVM comparison also trusts the
translation from both source programs to that LLVM input.

## License boundary

The initial review did not add these tools to the build. The later SAW
selection has a [separate dependency review](../../spikes/clight-permute/tests/equiv-saw/LICENSES.md).
Do not extend that review to every tool or optional configuration in this
table. A project's top-level
license or Nix metadata is not a license check of all bundled binaries,
solvers, source downloads, and build dependencies.

| Tool | Reviewed top-level terms | Dependency condition before use |
| --- | --- | --- |
| Alive2 | [MIT][alive-license] | Audit matching LLVM/Clang (Apache-2.0 with LLVM exception), Z3 (MIT), and build tools; omit optional Redis caching |
| SAW/Crucible | [SAW][saw-license] and [Crucible][crucible-license]: BSD-3-Clause | Audit Cryptol, What4, Haskell packages, ABC, solver binaries, and runtime; the Nix package is a prebuilt bundle |
| CBMC | [BSD-4-Clause][cbmc-license] | Use a source selection without restricted Glucose-Syrup; CaDiCaL is MIT; retain required acknowledgements |
| SeaHorn | [BSD-style terms][seahorn-license] permitting commercial use | Audit LLVM, Z3, Boost, sea-dsa, clam/crab, and selected fetched components |
| SMACK | [MIT plus third-party notices][smack-license] | Audit LLVM, sea-dsa, Boogie, Corral, Z3, and .NET/Mono as selected |
| KLEE | [NCSA][klee-license] | Prefer an audited Z3 backend; inventory selected libc/libc++, runtime, and solver components |
| Symbiotic | [MIT][symbiotic-license] | Inventory its KLEE, LLVM, slicing, instrumentation, and solver components |
| llreve | [BSD-3-Clause][llreve-license] | Audit old LLVM/Z3 dependencies; avoid unaudited binary images |
| Frama-C / Why3 / Z3 | Pinned package metadata: LGPL-2.1 / LGPL-2.1 / MIT | Select permitted provers explicitly; exclude Alt-Ergo |

The following package facts were checked against Nixpkgs commit
[`c7def046b9a883d46974757852106483d741586f`][nix-pin]:

* **Alt-Ergo 2.6.3 is non-commercial.** Its [package definition][nix-alt]
  selects `ocamlpro_nc`. Nix evaluation reports `free = false` and
  `redistributable = false`. Do not infer permission from generic lists of
  recommended Why3 provers. The [Frama-C 33.0 recipe][nix-frama] does not
  require Alt-Ergo. [Why3's prover wrapper][nix-why3] takes an explicit list.
* **CBMC 6.11.0 fetches a restricted optional source.** Its
  [package recipe][nix-cbmc] selects CaDiCaL but also fetches and copies
  Glucose-Syrup commit `0bb2afd3b9baace6981cbb8b4a1c7683c44968b7`.
  That source's [license][glucose-license] restricts competition use of
  the parallel version. This is not a non-commercial restriction, but it
  is not plain MIT or BSD either. Build CBMC without that fetch and source
  to keep this additional restriction out of the dependency set.
* **SAW's BSD metadata does not describe every bundled file.** The
  [Nix recipe][nix-saw] downloads a release binary bundle and adds its `bin`
  directory to `PATH`. Audit that bundle or use an audited source build.
  SAW documents Z3 and Yices requirements. Yices 2 uses
  [GPL-3.0-or-later][yices-license], which permits commercial use; verify
  the exact chosen version and obligations.

CBMC's advertising-clause BSD license permits commercial use but is
generally incompatible with GPL for combined code. Running CBMC as a
separate checker does not change the input program's license. Do not link
CBMC code into the GPL generated implementation. Keep `allowUnfree = false`
and retain an explicit dependency inventory; that setting alone cannot
detect a restricted file fetched inside a nominally free package.

## A small trial with a clear result

1. Pin a supported Clang/SAW pair and audit its selected dependencies.
   Compile the actual generated C and pinned oracle, with the same target
   layout, into LLVM. Preserve assertions. Record all remaining external
   calls and relevant unsupported instructions.
2. For each fixed `n` from 1 through 5, use symbolic full-width data and
   symbolic valid permutations. Compare all observations above. Require
   memory safety, no oracle assertion failure, and complete path coverage
   for that fixed case. Keep every allocator or library assumption visible.
3. Exercise the swap-depth boundary with sizes 17, 18, and 19. These cases
   can reach blocked results which the smallest cases cannot cover. Record
   the solver result, time, path limits, and any incomplete obligations.
4. Use those results to estimate the work for all `n <= 1024`. A scalable
   proof will probably need library contracts and loop invariants for the
   duplicate-aware ordering and trace relation. Prove termination separately
   if the selected invariant method establishes only partial correctness.

Keep the existing Rocq/Clight theorem as the main proof of the generated
algorithm. A successful LLVM comparison would add evidence connecting the
two compiled implementations. It would not by itself remove the trusted
printer or the source compiler from the end-to-end trust boundary.

[alive-readme]: https://github.com/AliveToolkit/alive2/blob/5d0eb277235b73f71000501c3a4f5ab9b2586915/README.md
[alive-options]: https://github.com/AliveToolkit/alive2/blob/5d0eb277235b73f71000501c3a4f5ab9b2586915/llvm_util/cmd_args_list.h
[alive-unroll]: https://github.com/AliveToolkit/alive2/blob/5d0eb277235b73f71000501c3a4f5ab9b2586915/ir/function.cpp
[alive-validator]: https://github.com/AliveToolkit/alive2/blob/5d0eb277235b73f71000501c3a4f5ab9b2586915/tools/transform.cpp
[alive-paper]: https://web.ist.utl.pt/nuno.lopes/pubs/alive2-pldi21.pdf
[alive-license]: https://github.com/AliveToolkit/alive2/blob/5d0eb277235b73f71000501c3a4f5ab9b2586915/LICENSE
[saw-verify]: https://github.com/GaloisInc/saw-script/blob/75dbf246aaf64a63f5316af14d4d085765a3fe67/doc/saw-user-manual/verifying-code.md
[saw-readme]: https://github.com/GaloisInc/saw-script/blob/75dbf246aaf64a63f5316af14d4d085765a3fe67/README.md
[saw-release]: https://github.com/GaloisInc/saw-script/blob/v1.5/README.md
[saw-license]: https://github.com/GaloisInc/saw-script/blob/75dbf246aaf64a63f5316af14d4d085765a3fe67/LICENSE
[crucible-limits]: https://github.com/GaloisInc/crucible/blob/3ca9ff715377c063197dff4be085544ebf2bf726/crucible-llvm/doc/limitations.md
[crucible-license]: https://github.com/GaloisInc/crucible/blob/3ca9ff715377c063197dff4be085544ebf2bf726/LICENSE
[cbmc-readme]: https://github.com/diffblue/cbmc/blob/4b26409ce19d4311eb928586f8f363990b5ea495/README.md
[cbmc-unwind]: https://github.com/diffblue/cbmc/blob/4b26409ce19d4311eb928586f8f363990b5ea495/doc/cprover-manual/cbmc-unwinding.md
[cbmc-license]: https://github.com/diffblue/cbmc/blob/4b26409ce19d4311eb928586f8f363990b5ea495/LICENSE
[seahorn-readme]: https://github.com/seahorn/seahorn/blob/892780176731ec8e97bbb9f6b172fcacd77a8ff4/README.md
[seahorn-license]: https://github.com/seahorn/seahorn/blob/892780176731ec8e97bbb9f6b172fcacd77a8ff4/license.txt
[smack-readme]: https://github.com/smackers/smack/blob/0a64471206645c250164e8df6027f5a5193e5e85/README.md
[smack-install]: https://github.com/smackers/smack/blob/0a64471206645c250164e8df6027f5a5193e5e85/docs/installation.md
[smack-license]: https://github.com/smackers/smack/blob/0a64471206645c250164e8df6027f5a5193e5e85/LICENSE
[klee-readme]: https://github.com/klee/klee/blob/9a36a6782b814fe1fa37439652b875114faa0e20/README.md
[klee-options]: https://klee-se.org/releases/docs/v3.1/docs/options/
[klee-license]: https://github.com/klee/klee/blob/9a36a6782b814fe1fa37439652b875114faa0e20/LICENSE.TXT
[symbiotic-readme]: https://github.com/staticafi/symbiotic/blob/4474bb949b1e56e028dd12fef7dff8a2d01937b5/README.md
[symbiotic-license]: https://github.com/staticafi/symbiotic/blob/4474bb949b1e56e028dd12fef7dff8a2d01937b5/LICENSE.txt
[llreve-readme]: https://github.com/mattulbrich/llreve/blob/master/reve/README.md
[llreve-guide]: https://github.com/mattulbrich/llreve/blob/master/reve/reve/README.md
[llreve-license]: https://github.com/mattulbrich/llreve/blob/master/LICENSE
[frama-wp]: https://frama-c.com/fc-plugins/wp.html
[frama-eva]: https://frama-c.com/fc-plugins/eva.html
[nix-pin]: https://github.com/NixOS/nixpkgs/tree/c7def046b9a883d46974757852106483d741586f
[nix-alt]: https://github.com/NixOS/nixpkgs/blob/c7def046b9a883d46974757852106483d741586f/pkgs/by-name/al/alt-ergo/package.nix
[nix-frama]: https://github.com/NixOS/nixpkgs/blob/c7def046b9a883d46974757852106483d741586f/pkgs/by-name/fr/frama-c/package.nix
[nix-why3]: https://github.com/NixOS/nixpkgs/blob/c7def046b9a883d46974757852106483d741586f/pkgs/applications/science/logic/why3/with-provers.nix
[nix-cbmc]: https://github.com/NixOS/nixpkgs/blob/c7def046b9a883d46974757852106483d741586f/pkgs/by-name/cb/cbmc/package.nix
[glucose-license]: https://github.com/brunodutertre/glucose-syrup/blob/0bb2afd3b9baace6981cbb8b4a1c7683c44968b7/LICENCE
[nix-saw]: https://github.com/NixOS/nixpkgs/blob/c7def046b9a883d46974757852106483d741586f/pkgs/by-name/sa/saw-tools/package.nix
[yices-license]: https://github.com/SRI-CSL/yices2/blob/master/copyright.txt
