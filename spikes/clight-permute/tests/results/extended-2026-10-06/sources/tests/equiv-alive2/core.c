/* SPDX-License-Identifier: GPL-3.0-or-later */
#include "observation.h"
#ifndef EQUIV_CORE_PATH
#define EQUIV_CORE_PATH "../../permute.c"
#endif
#include EQUIV_CORE_PATH

void observe(struct Observation *observed, const unsigned *values)
{
    unsigned data[EQUIV_N];
    unsigned permutation[EQUIV_N] = EQUIV_PERMUTATION;
    unsigned target[EQUIV_N], used[EQUIV_N], trace[2U * EQUIV_N], out[3];
    struct Observation result = {0};
    for (unsigned i = 0; i < EQUIV_N; ++i)
        data[i] = values[i];
    result.status = permute(EQUIV_N, data, permutation, target, used, trace, out);
    for (unsigned i = 0; i < EQUIV_N; ++i)
        result.data[i] = data[i];
    result.count = out[0];
    result.blocked_offset = out[1];
    result.blocked_excess = out[2];
    for (unsigned i = 0; i < out[0]; ++i)
        result.trace[i] = trace[i];
#ifdef EQUIV_NEGATIVE
    result.status ^= 1U;
#endif
    *observed = result;
}
