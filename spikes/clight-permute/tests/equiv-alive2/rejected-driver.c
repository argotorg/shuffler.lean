/* SPDX-License-Identifier: GPL-3.0-or-later */
#include <klee/klee.h>
#include "permute.h"

/* REJECT_N == 0 selects all empty and oversized calls. Otherwise the
 * symbolic input contains permutation, data, and initial output words. */
int main(void)
{
#if REJECT_N == 0
    unsigned input[4], out[3];
    klee_make_symbolic(input, sizeof(input), "size_inputs");
    unsigned n = input[0];
    klee_assume((n == 0U) | (n > 1024U));
    for (unsigned i = 0; i < 3U; ++i)
        out[i] = input[i + 1U];
    unsigned status = permute(n, 0, 0, 0, 0, 0, out);
    klee_assert(status == (n == 0U ? 0U : 2U));
#else
    unsigned input[2U * REJECT_N + 3U];
    unsigned data[REJECT_N], permutation[REJECT_N];
    unsigned target[REJECT_N], used[REJECT_N], trace[2U * REJECT_N], out[3];
    klee_make_symbolic(input, sizeof(input), "reject_inputs");
    unsigned valid = 1U;
    for (unsigned i = 0; i < REJECT_N; ++i) {
        valid &= input[i] < REJECT_N;
        for (unsigned j = 0; j < i; ++j)
            valid &= input[i] != input[j];
        permutation[i] = input[i];
        data[i] = input[REJECT_N + i];
    }
    /* A finite array is a permutation iff all entries are in range and
     * pairwise distinct. This check uses no production validation code. */
    klee_assume(valid == 0U);
    for (unsigned i = 0; i < 3U; ++i)
        out[i] = input[2U * REJECT_N + i];
    unsigned status = permute(REJECT_N, data, permutation, target, used, trace, out);
    klee_assert(status == 2U);
    for (unsigned i = 0; i < REJECT_N; ++i) {
        klee_assert(permutation[i] == input[i]);
        klee_assert(data[i] == input[REJECT_N + i]);
    }
#endif
    for (unsigned i = 0; i < 3U; ++i)
        klee_assert(out[i] == 0U);
    return 0;
}
