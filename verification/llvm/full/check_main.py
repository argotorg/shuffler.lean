#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0-or-later
"""Check the complete permute body and mutations of its exchange and return blocks."""
from pathlib import Path
import sys

import check
import check_prefix
import check_fixed
import check_choice

PROOFS = check_choice.PROOFS + (
    'MainPrefix', 'ExchangeBlocks', 'MainInvariant', 'ExchangePermutation',
    'ExchangeData', 'ExchangeSuccess', 'Cleanup', 'ExchangeBlocked', 'EarlyExit',
    'MainLoopCore', 'MainLoop', 'MainBody', 'BodyEquivalence',
)
CLAIMS = check_choice.CLAIMS + (
    'MainPrefix.main_prefix',
    'MainInvariant.main_registers_frame',
    'MainInvariant.main_choose',
    'MainInvariant.main_selected_bounds',
    'ExchangeBlocks.exchange_compare_phi',
    'ExchangeBlocks.exchange_compare_runs',
    'ExchangeBlocks.exchange_depth_runs',
    'ExchangeBlocks.exchange_blocked_runs',
    'ExchangeBlocks.exchange_capacity_runs',
    'ExchangeBlocks.exchange_permutation_runs',
    'ExchangePermutation.exchange_permutation_array',
    'ExchangePermutation.exchange_equal_choice',
    'ExchangeData.trace_unsigned',
    'ExchangeData.trace_gep',
    'ExchangeData.exchange_data_runs',
    'ExchangeSuccess.exchange_data_array',
    'ExchangeSuccess.successful_exchange',
    'Cleanup.cleanup_runs',
    'Cleanup.cleanup_path',
    'Cleanup.block_steps_return',
    'Cleanup.cleanup_after_steps',
    'ExchangeBlocked.exchange_blocked_fields',
    'ExchangeBlocked.exchange_blocked_choice',
    'EarlyExit.check_empty_zero',
    'EarlyExit.oversized_path',
    'EarlyExit.empty_path',
    'MainLoopCore.main_loop_from_exchanges',
    'MainLoop.main_blocked_exchange',
    'MainLoop.main_loop_refines',
    'MainLoop.main_loop_nonempty',
    'MainBody.permute_body_path',
    'MainBody.permute_body_refines',
    'BodyEquivalence.result_return_equal',
    'BodyEquivalence.related_writable',
    'BodyEquivalence.permute_body_clight',
)

# Recompile each affected block and its dependencies against the changed AST.
# The complete body proof is checked above. These blocks do not import the
# normalization proofs, so mutations need not compile those unrelated files.
BLOCK_PROOFS = (
    'Entry', 'Index', 'WordArithmetic', 'FixedBlocks',
    'ChooseBlocks', 'ChooseScan', 'Choose', 'ExchangeBlocks', 'ExchangeData', 'Cleanup',
)
MUTATIONS = (
    ('exchange_phi', 'phi i32 [ %v11.1, %while.end125 ]',
     'phi i32 [ 0, %while.end125 ]', 'ExchangeBlocks'),
    ('exchange_compare', '%cmp138.not = icmp eq i32 %18, %19',
     '%cmp138.not = icmp ne i32 %18, %19', 'ExchangeBlocks'),
    ('exchange_depth', '%sub140 = sub i32 %sub, %v11.2',
     '%sub140 = sub i32 %v11.2, %sub', 'ExchangeBlocks'),
    ('depth_limit', '%cmp141 = icmp ugt i32 %sub140, 16',
     '%cmp141 = icmp ugt i32 %sub140, 17', 'ExchangeBlocks'),
    ('blocked_position', 'store i32 %v11.2, ptr %arrayidx1,',
     'store i32 0, ptr %arrayidx1,', 'ExchangeBlocks'),
    ('blocked_excess', '%sub144 = add i32 %sub140, -16',
     '%sub144 = add i32 %sub140, -15', 'ExchangeBlocks'),
    ('trace_limit', '%cmp150.not = icmp ult i32 %20, %add149',
     '%cmp150.not = icmp ule i32 %20, %add149', 'ExchangeBlocks'),
    ('data_selected', 'store i32 %19, ptr %arrayidx135,',
     'store i32 %18, ptr %arrayidx135,', 'ExchangeData'),
    ('data_top', 'store i32 %18, ptr %arrayidx137,',
     'store i32 %19, ptr %arrayidx137,', 'ExchangeData'),
    ('trace_index', '%idxprom163 = zext i32 %21 to i64',
     '%idxprom163 = zext i32 0 to i64', 'ExchangeData'),
    ('trace_depth', 'store i32 %sub140, ptr %arrayidx164,',
     'store i32 0, ptr %arrayidx164,', 'ExchangeData'),
    ('trace_increment', '%add166 = add i32 %22, 1',
     '%add166 = add i32 %22, 2', 'ExchangeData'),
    ('permutation_selected', 'store i32 %24, ptr %arrayidx171,',
     'store i32 %23, ptr %arrayidx171,', 'ExchangeBlocks'),
    ('permutation_top', 'store i32 %23, ptr %arrayidx109,',
     'store i32 %24, ptr %arrayidx109,', 'ExchangeBlocks'),
    ('blocked_return', 'phi i32 [ 1, %if.then142 ]',
     'phi i32 [ 2, %if.then142 ]', 'Cleanup'),
)


if __name__ == '__main__':
    if len(sys.argv) != 4:
        sys.exit('usage: check_main.py COMPCERT ASSUMPTION_POLICY IMPORTER')
    compcert, policy, importer = (Path(arg).resolve() for arg in sys.argv[1:])
    dependencies = check.MODULES + check_fixed.CLIGHT
    check.check(compcert, policy, dependencies + check_prefix.CANDIDATE + PROOFS,
                CLAIMS, 'kernel-axioms-clight.txt')
    check_prefix.mutations(compcert, importer, BLOCK_PROOFS, MUTATIONS, dependencies)
