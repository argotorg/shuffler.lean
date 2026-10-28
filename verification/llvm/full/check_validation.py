#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0-or-later
"""Check the LLVM validation loop against PR #6's memory invariant."""
from pathlib import Path
import sys

import check
import check_prefix

CLIGHT = ('Permute', 'ClightEval', 'ClightEvalProofs', 'ClightMemory',
          'ClightScalar', 'ClightLoop', 'ClightInitialize', 'ClightEntry',
          'ClightValidation')
PROOFS = check_prefix.PROOFS + ('ValidationBlocks', 'Validation', 'CheckedPrefix')
CLAIMS = check_prefix.CLAIMS + (
    'Index.word_lt',
    'ClightValidation.validation_memory_step',
    'ValidationBlocks.validation_range_runs',
    'ValidationBlocks.validation_unused_runs',
    'ValidationBlocks.validation_store_runs',
    'Validation.validation_iteration',
    'Validation.validation_loop',
    'Validation.validation_pass',
    'CheckedPrefix.checked_prefix',
    'CheckedPrefix.checked_prefix_semantics',
)
MUTATIONS = check_prefix.MUTATIONS + (
    ('validation_range', 'icmp ult i32 %0, %v1',
     'icmp eq i32 %0, %v1', 'ValidationBlocks'),
    ('validation_used', 'store i32 1, ptr %arrayidx25,',
     'store i32 0, ptr %arrayidx25,', 'ValidationBlocks'),
    ('validation_data', 'load i32, ptr %arrayidx33,',
     'load i32, ptr %arrayidx19,', 'ValidationBlocks'),
    ('validation_target', 'store i32 %2, ptr %arrayidx35,',
     'store i32 %2, ptr %arrayidx25,', 'ValidationBlocks'),
)


if __name__ == '__main__':
    if len(sys.argv) != 4:
        sys.exit('usage: check_validation.py COMPCERT ASSUMPTION_POLICY IMPORTER')
    compcert, policy, importer = (Path(arg).resolve() for arg in sys.argv[1:])
    check.check(compcert, policy,
                check.MODULES + CLIGHT + check_prefix.CANDIDATE + PROOFS, CLAIMS,
                'kernel-axioms-clight.txt')
    check_prefix.mutations(compcert, importer, PROOFS, MUTATIONS, check.MODULES + CLIGHT)
