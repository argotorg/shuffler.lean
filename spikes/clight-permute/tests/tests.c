/* SPDX-License-Identifier: GPL-3.0-or-later */
#include "test.h"
#include "../permute.h"

#include <assert.h>
#include <limits.h>
#include <stdio.h>
#include <string.h>

static void enumerate(unsigned n, unsigned pos, unsigned *p, unsigned *count)
{
    if (pos == n) {
        unsigned data[5];
        for (unsigned pattern = 0; pattern < (1U << n); pattern++) {
            for (unsigned i = 0; i < n; i++)
                data[i] = (pattern >> i) % 2U == 0U ? 0U : UINT_MAX;
            check_case(n, data, p);
            (*count)++;
        }
        for (unsigned i = 0; i < n; i++)
            data[i] = i;
        check_case(n, data, p);
        (*count)++;
        return;
    }
    for (unsigned i = pos; i < n; i++) {
        unsigned saved = p[pos];
        p[pos] = p[i];
        p[i] = saved;
        enumerate(n, pos + 1U, p, count);
        saved = p[pos];
        p[pos] = p[i];
        p[i] = saved;
    }
}

static void boundaries(void)
{
    const unsigned sizes[] = {1U, 16U, 17U, 18U, TEST_LIMIT};
    unsigned data[TEST_LIMIT], p[TEST_LIMIT];
    for (unsigned k = 0; k < sizeof(sizes) / sizeof(sizes[0]); k++) {
        unsigned n = sizes[k];
        for (unsigned i = 0; i < n; i++) {
            data[i] = i;
            p[i] = i;
        }
        check_case(n, data, p);
        p[0] = n - 1U;
        p[n - 1U] = 0U;
        check_case(n, data, p);
        /* Duplicate normalization removes even an out-of-range swap. */
        data[0] = UINT_MAX;
        data[n - 1U] = UINT_MAX;
        check_case(n, data, p);
    }
    /* A trace has one valid swap before the second swap blocks. */
    for (unsigned i = 0; i < 18U; i++) {
        data[i] = i;
        p[i] = i;
    }
    p[17] = 16U;
    p[16] = 0U;
    p[0] = 17U;
    check_case(18U, data, p);
    /* Equal top values suppress the first exchange, then depth 17 blocks. */
    for (unsigned i = 0; i < 18U; i++)
        p[i] = i;
    data[16] = data[17];
    p[16] = 0U;
    p[0] = 16U;
    check_case(18U, data, p);
    /* A cycle within the top 17 slots of the largest permitted stack. */
    for (unsigned i = 0; i < TEST_LIMIT; i++) {
        data[i] = i;
        p[i] = i;
    }
    for (unsigned i = TEST_LIMIT - 17U; i + 1U < TEST_LIMIT; i++)
        p[i] = i + 1U;
    p[TEST_LIMIT - 1U] = TEST_LIMIT - 17U;
    check_case(TEST_LIMIT, data, p);
}

static void rejected_inputs(void)
{
    unsigned out[3] = {99U, 99U, 99U};
    assert(permute(0U, NULL, NULL, NULL, NULL, NULL, out) == 0U);
    assert(out[0] == 0U && out[1] == 0U && out[2] == 0U);
    const unsigned bad_sizes[] = {TEST_LIMIT + 1U, UINT_MAX};
    for (unsigned i = 0; i < 2U; i++) {
        out[0] = out[1] = out[2] = 99U;
        assert(permute(bad_sizes[i], NULL, NULL, NULL, NULL, NULL, out) == 2U);
        assert(out[0] == 0U && out[1] == 0U && out[2] == 0U);
    }
    const unsigned bad[][3] = {{0U, 0U, 2U}, {0U, 3U, 2U}, {UINT_MAX, 1U, 2U}};
    for (unsigned i = 0; i < 3U; i++) {
        unsigned data[3] = {5U, 6U, 7U}, p[3], target[3], used[3], trace[6];
        memcpy(p, bad[i], sizeof(p));
        out[0] = out[1] = out[2] = 99U;
        assert(permute(3U, data, p, target, used, trace, out) == 2U);
        assert(data[0] == 5U && data[1] == 6U && data[2] == 7U);
        assert(memcmp(p, bad[i], sizeof(p)) == 0);
        assert(out[0] == 0U && out[1] == 0U && out[2] == 0U);
    }
}

int main(void)
{
    unsigned p[5], count = 0;
    rejected_inputs();
    boundaries();
    for (unsigned n = 1; n <= 5U; n++) {
        for (unsigned i = 0; i < n; i++)
            p[i] = i;
        enumerate(n, 0U, p, &count);
    }
    printf("tests: %u exhaustive cases; boundary and invalid-input cases\n", count);
    return 0;
}
