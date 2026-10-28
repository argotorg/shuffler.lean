#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0-or-later
"""Check the LLVM main-loop setup and position choice against PR #6's model."""
from pathlib import Path
import sys

import check
import check_prefix
import check_fixed
import check_normalization

PROOFS = check_normalization.PROOFS + (
    'WordArithmetic', 'MainSetup', 'ChooseBlocks', 'ChooseScan', 'Choose', 'ChoosePermutation',
)
CLAIMS = check_normalization.CLAIMS + (
    'WordArithmetic.word_repr',
    'WordArithmetic.word_add',
    'WordArithmetic.word_sub',
    'WordArithmetic.word_double',
    'WordArithmetic.word_gt',
    'WordArithmetic.index_decrement',
    'WordArithmetic.boolean_and',
    'WordArithmetic.index_ne',
    'MainSetup.main_preheader_runs',
    'MainSetup.main_preheader_bindings',
    'ChooseBlocks.choose_head_runs',
    'ChooseBlocks.choose_zero_runs',
    'ChooseBlocks.choose_preheader_runs',
    'ChooseBlocks.choose_scan_phi',
    'ChooseBlocks.choose_scan_runs',
    'ChooseBlocks.choose_exit_runs',
    'ChooseBlocks.choose_result_phi',
    'ChooseBlocks.choose_result_runs',
    'ChooseScan.choose_scan_loop',
    'ChooseScan.choose_descending',
    'Choose.choose_observation_eq',
    'Choose.choose_array',
    'ChoosePermutation.choose_permutation',
)
# The complete prefix is checked above. Choice mutations need only these
# blocks and their dependencies, all recompiled against each changed AST.
BLOCK_PROOFS = (
    'Entry', 'Index', 'WordArithmetic', 'MainSetup', 'FixedBlocks',
    'ChooseBlocks', 'ChooseScan', 'Choose', 'ChoosePermutation',
)
MUTATIONS = (
    ('top_index', '%sub = add nsw i32 %v1, -1',
     '%sub = add nsw i32 %v1, -2', 'MainSetup'),
    ('trace_capacity', '%add149 = shl nuw nsw i32 %v1, 1',
     '%add149 = shl nuw nsw i32 %v1, 2', 'MainSetup'),
    ('choose_head', '%cmp110 = icmp eq i32 %11, %sub',
     '%cmp110 = icmp ne i32 %11, %sub', 'ChooseBlocks'),
    ('choose_zero', '%cmp114.old.not = icmp eq i32 %11, 0',
     '%cmp114.old.not = icmp eq i32 %11, 1', 'ChooseBlocks'),
    ('choose_phi', 'phi i64 [ %12, %if.end117.preheader ]',
     'phi i64 [ 0, %if.end117.preheader ]', 'ChooseBlocks'),
    ('choose_decrement', '%13 = add nsw i64 %indvars.iv316, -1',
     '%13 = add nsw i64 %indvars.iv316, -2', 'ChooseBlocks'),
    ('choose_next', '%indvars.iv.next317 = add nsw i64 %indvars.iv316, -1',
     '%indvars.iv.next317 = add nsw i64 %indvars.iv316, -2', 'ChooseBlocks'),
    ('choose_compare', '%cmp121.wide = icmp eq i64 %13, %15',
     '%cmp121.wide = icmp ne i64 %13, %15', 'ChooseBlocks'),
    ('choose_stop', '%cmp114.wide = icmp ne i64 %13, 0',
     '%cmp114.wide = icmp eq i64 %13, 0', 'ChooseBlocks'),
    ('choose_and', '%or.cond = and i1 %cmp121.wide, %cmp114.wide',
     '%or.cond = and i1 %cmp121.wide, true', 'ChooseBlocks'),
    # OR is outside the accepted syntax. Keep that rejection as a separate
    # control; the accepted but incorrect AND operand above tests the proof.
    ('choose_or', '%or.cond = and i1 %cmp121.wide, %cmp114.wide',
     '%or.cond = or i1 %cmp121.wide, %cmp114.wide', 'FullProgram'),
    ('choose_result', '%cmp128 = icmp eq i32 %17, %v11.1',
     '%cmp128 = icmp ne i32 %17, %v11.1', 'ChooseBlocks'),
)


if __name__ == '__main__':
    if len(sys.argv) != 4:
        sys.exit('usage: check_choice.py COMPCERT ASSUMPTION_POLICY IMPORTER')
    compcert, policy, importer = (Path(arg).resolve() for arg in sys.argv[1:])
    dependencies = check.MODULES + check_fixed.CLIGHT
    check.check(compcert, policy, dependencies + check_prefix.CANDIDATE + PROOFS,
                CLAIMS, 'kernel-axioms-clight.txt')
    check_prefix.mutations(compcert, importer, BLOCK_PROOFS, MUTATIONS, dependencies)
