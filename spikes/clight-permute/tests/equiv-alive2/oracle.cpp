// SPDX-License-Identifier: GPL-3.0-or-later
#include "observation.h"
#include "../oracle.cpp"

extern "C" void observe(Observation *observed, const unsigned *values)
{
    unsigned data[EQUIV_N];
    unsigned permutation[EQUIV_N] = EQUIV_PERMUTATION;
    unsigned trace[2U * EQUIV_N], out[3];
    Observation result = {};
    for (unsigned i = 0; i < EQUIV_N; ++i)
        data[i] = values[i];
    result.status = solc_permute(EQUIV_N, data, permutation, trace, out);
    for (unsigned i = 0; i < EQUIV_N; ++i)
        result.data[i] = data[i];
    result.count = out[0];
    result.blocked_offset = out[1];
    result.blocked_excess = out[2];
    for (unsigned i = 0; i < out[0]; ++i)
        result.trace[i] = trace[i];
    *observed = result;
}
