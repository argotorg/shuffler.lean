#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0-or-later
"""Check full Clight and LLVM calls, their assumptions, and LLVM mutations."""
from pathlib import Path
import sys

import check
import check_prefix
import check_fixed
import check_main

PROOFS = check_main.PROOFS + (
    'BodySyntax', 'BodyFrame', 'NoException', 'CallBoundary', 'BodyNoException',
    'FullCall', 'ModuleCall', 'FullEquivalence', 'FullContract',
)
CLAIMS = check_main.CLAIMS + (
    'BodySyntax.body_plain',
    'BodyFrame.full_block_path_frame',
    'BodyFrame.full_block_steps_frame',
    'NoException.run_exc_free',
    'NoException.exception_free_bind',
    'NoException.exception_free_iter',
    'NoException.runs_run_exc',
    'CallBoundary.memory_push_correct',
    'CallBoundary.memory_pop_empty_correct',
    'CallBoundary.empty_struct_store',
    'CallBoundary.empty_struct_allocation',
    'CallBoundary.push_call_runs',
    'CallBoundary.call_state_related',
    'CallBoundary.call_state_bindings',
    'CallBoundary.call_state_structure',
    'CallBoundary.pop_call_runs',
    'CallBoundary.returned_state_related',
    'CallBoundary.call_denotation_runs',
    'BodyNoException.full_body_exception_free',
    'FullCall.full_call_from_path',
    'FullCall.permute_call_refines',
    'FullCall.empty_call_refines',
    'FullCall.oversized_call_refines',
    'ModuleCall.permute_function_lookup',
    'ModuleCall.permute_module_call',
    'FullEquivalence.permute_calls_agree',
    'FullEquivalence.empty_calls_agree',
    'FullEquivalence.oversized_calls_agree',
    'FullContract.full_module_equivalence',
)

BLOCK_PROOFS = ('Entry', 'Index', 'Initialize', 'Prefix', 'Cleanup', 'CallBoundary')
MUTATIONS = (
    ('argument_order', 'ptr nocapture noundef %v2, ptr nocapture noundef %v3,',
     'ptr nocapture noundef %v3, ptr nocapture noundef %v2,', 'CallBoundary'),
    ('empty_compare', '%cmp3 = icmp eq i32 %v1, 0',
     '%cmp3 = icmp ne i32 %v1, 0', 'Prefix'),
    ('empty_return', '[ 0, %if.end ]', '[ 1, %if.end ]', 'Cleanup'),
    ('done_return', '[ 0, %while.end125 ]', '[ 1, %while.end125 ]', 'Cleanup'),
    ('oversized_return', '[ 2, %entry ]', '[ 1, %entry ]', 'Cleanup'),
    ('return_value', 'ret i32 %retval.0', 'ret i32 0', 'Cleanup'),
)


if __name__ == '__main__':
    if len(sys.argv) != 4:
        sys.exit('usage: check_call.py COMPCERT ASSUMPTION_POLICY IMPORTER')
    compcert, policy, importer = (Path(arg).resolve() for arg in sys.argv[1:])
    dependencies = check.MODULES + check_fixed.CLIGHT
    check.check(compcert, policy, dependencies + check_prefix.CANDIDATE + PROOFS,
                CLAIMS, 'kernel-axioms-clight.txt')
    check_prefix.mutations(compcert, importer, BLOCK_PROOFS, MUTATIONS, dependencies)
