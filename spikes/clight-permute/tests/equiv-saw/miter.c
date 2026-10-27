/* SPDX-License-Identifier: GPL-3.0-or-later */
#include "../../permute.h"
#include "../test.h"

#ifndef CASE_N
#error "CASE_N is required"
#endif
#ifndef CASE_PERMUTATION
#error "CASE_PERMUTATION is required"
#endif

/* Both algorithms receive separate arrays with equal input values.
 * Only the written trace prefix is an output of the operation. */
unsigned equivalence(const unsigned *input)
{
    unsigned data[CASE_N], reference[CASE_N];
    unsigned permutation[CASE_N] = {CASE_PERMUTATION};
    const unsigned expected_permutation[CASE_N] = {CASE_PERMUTATION};
    unsigned target[CASE_N], used[CASE_N];
    unsigned trace[2 * CASE_N], expected_trace[2 * CASE_N];
    unsigned out[3], expected_out[3];
    for (unsigned i = 0; i < CASE_N; ++i) {
        data[i] = input[i];
        reference[i] = input[i];
    }
    unsigned status = permute(CASE_N, data, permutation, target, used,
        trace, out);
    unsigned expected = solc_permute(CASE_N, reference, expected_permutation,
        expected_trace, expected_out);
#ifdef NEGATIVE_CONTROL
    /* This separate wrapper build must fail the claimed equality. */
    data[0] = data[0] + 1U;
#endif
    if (status != expected || out[0] != expected_out[0] ||
        out[1] != expected_out[1] || out[2] != expected_out[2] ||
        out[0] > 2U * CASE_N)
        return 0U;
    for (unsigned i = 0; i < CASE_N; ++i)
        if (data[i] != reference[i])
            return 0U;
    for (unsigned i = 0; i < out[0]; ++i)
        if (trace[i] != expected_trace[i])
            return 0U;
    return 1U;
}
