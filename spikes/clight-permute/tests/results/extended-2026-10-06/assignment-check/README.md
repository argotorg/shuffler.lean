<!-- SPDX-License-Identifier: GPL-3.0-or-later -->
# Candidate assignment analysis evidence

This archive records the initial checker result. Later
[path](../assignment-path-proof/README.md) and
[execution](../assignment-execution-proof/README.md) archives add the
statement-level proof and its link to terminating Clight execution.

The actual Permute AST passes the candidate check. The known uninitialized
self-copy prefix fails. All 21 examples compile, and all nine baseline
and mutation controls have their expected results.

[results.json](results.json) lists the controls. Seven weakened decisions
fail their named negative example. The unchanged checker and the control
that duplicates assignment-list entries pass. Each directory retains its
exact source and diagnostic. Compilation errors at an unrelated statement
do not count as successful detection.

The [kernel check](baseline/kernel.log) and
[kernel policy](baseline/kernel-policy.log) pass. The
[assumption report](baseline/compile.log) says both `uses_covers_reads`
and `permute_passes_assignment_check` are closed under the global context.

This establishes the stated expression-read property and a computed fact
about this checker on the actual AST. A full statement-level soundness
theorem remains open. Initialized memory bytes, valid addresses, and the
Clight-to-C translation also require separate arguments. The known printer
gap remains open; this checker is not installed in the production pipeline.

Read the [check contract](../../../initialization/README.md) and
[source](sources/AssignmentCheck.v) for the scope and flow rules.
[archive.json](archive.json) records the retained hashes. The original
build is under `spikes/clight-permute/build/initialization/assignment-checked/`.
