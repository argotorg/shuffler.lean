#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0-or-later
"""Check both LLVM normalization passes and their composition with entry."""
from pathlib import Path
import sys

import check
import check_prefix
import check_fixed

PROOFS = check_fixed.PROOFS + ('FillBlocks', 'Fill', 'FillLoop', 'NormalizedPrefix')
CLAIMS = check_fixed.CLAIMS + (
    'Entry.entry_output_registers',
    'CheckedPrefix.output_stores_zero',
    'ModelProofs.raw_normalize_complete',
    'ClightNormalization.normalize_correct',
    'FillBlocks.fill_preheader_runs',
    'FillBlocks.fill_phi',
    'FillBlocks.fill_compare_runs',
    'FillBlocks.fill_assign_runs',
    'FillBlocks.fill_next_runs',
    'Fill.fill_assignment',
    'Fill.fill_branch',
    'FillLoop.fill_iteration',
    'FillLoop.fill_loop',
    'FillLoop.fill_pass',
    'FillLoop.fill_pass_semantics',
    'NormalizedPrefix.normalized_prefix',
    'NormalizedPrefix.normalized_prefix_semantics',
)
MUTATIONS = (
    ('output_field', '%arrayidx1 = getelementptr inbounds nuw i8, ptr %v7, i64 4',
     '%arrayidx1 = getelementptr inbounds nuw i8, ptr %v7, i64 8', 'Entry'),
    ('fill_compare', '%cmp70.not = icmp eq i32 %6, %7',
     '%cmp70.not = icmp ne i32 %6, %7', 'FillBlocks'),
    ('fill_assignment', 'store i32 %v9.0.lcssa, ptr %arrayidx99,',
     'store i32 0, ptr %arrayidx99,', 'FillBlocks'),
    ('fill_flag', 'store i32 1, ptr %arrayidx101,',
     'store i32 0, ptr %arrayidx101,', 'FillBlocks'),
    ('fill_phi', 'phi i64 [ 0, %if.end65.preheader ]',
     'phi i64 [ 1, %if.end65.preheader ]', 'FillBlocks'),
    ('fill_increment', '%indvars.iv.next312 = add nuw nsw i64 %indvars.iv311, 1',
     '%indvars.iv.next312 = add nuw nsw i64 %indvars.iv311, 2', 'FillBlocks'),
    ('fill_count', '%wide.trip.count314 = zext nneg i32 %v1 to i64',
     '%wide.trip.count314 = zext nneg i32 1 to i64', 'FillBlocks'),
)


if __name__ == '__main__':
    if len(sys.argv) != 4:
        sys.exit('usage: check_normalization.py COMPCERT ASSUMPTION_POLICY IMPORTER')
    compcert, policy, importer = (Path(arg).resolve() for arg in sys.argv[1:])
    dependencies = check.MODULES + check_fixed.CLIGHT
    check.check(compcert, policy, dependencies + check_prefix.CANDIDATE + PROOFS,
                CLAIMS, 'kernel-axioms-clight.txt')
    check_prefix.mutations(compcert, importer, PROOFS, MUTATIONS, dependencies)
