#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0-or-later
"""Check the first LLVM normalization pass against PR #6's array invariant."""
from pathlib import Path
import sys

import check
import check_prefix
import check_validation

CLIGHT = check_validation.CLIGHT + (
    'ClightSwap', 'ClightExchangeSuccess', 'Legacy.Permute', 'ModelArrays',
    'ClightNormalize',
    'Legacy.Proofs', 'SolcModel', 'ModelSpec', 'ModelProofs', 'ClightCall',
    'ClightChoose', 'ChooseModel', 'ClightExchange', 'PermuteSpec', 'ClightMain',
    'ClightSearch', 'FirstFree', 'ClightFill', 'ClightFillLoop',
    'ClightNormalization', 'ClightCorrect',
)
PROOFS = check_validation.PROOFS + (
    'FixedBlocks', 'Fixed', 'FixedPrefix', 'SearchBlocks', 'Search', 'SearchModel',
)
CLAIMS = check_validation.CLAIMS + (
    'Index.truncate_index',
    'ClightNormalize.fixed_assignment_step',
    'ClightNormalize.fixed_pass_correct',
    'FixedBlocks.fixed_phi',
    'FixedBlocks.fixed_compare_runs',
    'FixedBlocks.fixed_assign_runs',
    'FixedBlocks.fixed_flag_phi',
    'FixedBlocks.fixed_merge_runs',
    'Fixed.natural_word_equal',
    'Fixed.fixed_branch',
    'Fixed.fixed_iteration',
    'Fixed.fixed_loop',
    'Fixed.fixed_preheader_runs',
    'Fixed.fixed_pass',
    'Fixed.fixed_pass_semantics',
    'ClightCorrect.target_array_from_destinations',
    'FixedPrefix.fixed_prefix',
    'FixedPrefix.fixed_prefix_semantics',
    'SearchBlocks.search_phi',
    'SearchBlocks.search_used_runs',
    'SearchBlocks.search_target_runs',
    'SearchBlocks.search_next_runs',
    'SearchBlocks.search_exit_runs',
    'SearchBlocks.search_result_runs',
    'Search.search_probe',
    'Search.search_found',
    'SearchModel.first_free_search',
)
MUTATIONS = (
    ('fixed_compare', '%cmp48 = icmp eq i32 %3, %4',
     '%cmp48 = icmp ne i32 %3, %4', 'FixedBlocks'),
    ('fixed_assignment', 'store i32 %5, ptr %arrayidx51,',
     'store i32 0, ptr %arrayidx51,', 'FixedBlocks'),
    ('fixed_flag', 'phi i32 [ 1, %if.then49 ], [ 0, %if.end43 ]',
     'phi i32 [ 0, %if.then49 ], [ 0, %if.end43 ]', 'FixedBlocks'),
    ('fixed_phi', 'phi i64 [ 0, %if.end43.preheader ]',
     'phi i64 [ 1, %if.end43.preheader ]', 'FixedBlocks'),
    ('fixed_increment', '%indvars.iv.next302 = add nuw nsw i64 %indvars.iv301, 1',
     '%indvars.iv.next302 = add nuw nsw i64 %indvars.iv301, 2', 'FixedBlocks'),
    ('fixed_count', '%wide.trip.count304 = zext nneg i32 %v1 to i64',
     '%wide.trip.count304 = zext nneg i32 1 to i64', 'Fixed'),
    ('search_flag', '%cmp80 = icmp eq i32 %8, 0',
     '%cmp80 = icmp eq i32 %8, 1', 'SearchBlocks'),
    ('search_match', '%cmp86 = icmp eq i32 %6, %9',
     '%cmp86 = icmp ne i32 %6, %9', 'SearchBlocks'),
    ('search_increment', '%indvars.iv.next307 = add nuw nsw i64 %indvars.iv306, 1',
     '%indvars.iv.next307 = add nuw nsw i64 %indvars.iv306, 2', 'SearchBlocks'),
    ('search_result', '%cmp94 = icmp eq i32 %v9.0.lcssa, %v1',
     '%cmp94 = icmp ne i32 %v9.0.lcssa, %v1', 'SearchBlocks'),
)


if __name__ == '__main__':
    if len(sys.argv) != 4:
        sys.exit('usage: check_fixed.py COMPCERT ASSUMPTION_POLICY IMPORTER')
    compcert, policy, importer = (Path(arg).resolve() for arg in sys.argv[1:])
    check.check(compcert, policy,
                check.MODULES + CLIGHT + check_prefix.CANDIDATE + PROOFS, CLAIMS,
                'kernel-axioms-clight.txt')
    check_prefix.mutations(compcert, importer, PROOFS, MUTATIONS, check.MODULES + CLIGHT)
