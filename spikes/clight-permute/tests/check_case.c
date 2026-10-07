/* SPDX-License-Identifier: GPL-3.0-or-later */
#include "test.h"
#include "../permute.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static void fail(const char *reason, unsigned n, const unsigned *source,
    const unsigned *permutation)
{
    fprintf(stderr, "FAIL %s\nn = %u\ndata =", reason, n);
    for (unsigned i = 0; i < n; i++)
        fprintf(stderr, " %u", source[i]);
    fputs("\npermutation =", stderr);
    for (unsigned i = 0; i < n; i++)
        fprintf(stderr, " %u", permutation[i]);
    fputc('\n', stderr);
    abort();
}

static unsigned *buffer(unsigned count)
{
    unsigned *result = malloc((size_t)count * sizeof(*result));
    if (result == NULL) {
        fputs("cannot allocate test buffer\n", stderr);
        exit(EXIT_FAILURE);
    }
    return result;
}

void check_case(unsigned n, const unsigned *source, const unsigned *permutation)
{
    if (n == 0U || n > TEST_LIMIT)
        fail("test input size", n, source, permutation);
    unsigned *data = buffer(n), *reference = buffer(n), *p = buffer(n);
    unsigned *target = buffer(n), *used = buffer(n), *replay = buffer(n);
    unsigned *trace = buffer(2U * n), *expected_trace = buffer(2U * n);
    unsigned out[3] = {99U, 99U, 99U}, expected_out[3] = {99U, 99U, 99U};
    size_t bytes = (size_t)n * sizeof(*data);
    memcpy(data, source, bytes);
    memcpy(reference, source, bytes);
    memcpy(replay, source, bytes);
    memcpy(p, permutation, bytes);
    unsigned status = permute(n, data, p, target, used, trace, out);
    unsigned expected = solc_permute(n, reference, permutation,
        expected_trace, expected_out);
    if (status != expected || memcmp(out, expected_out, sizeof(out)) != 0)
        fail("status or result fields", n, source, permutation);
    if (out[0] > 2U * n || memcmp(data, reference, bytes) != 0)
        fail("trace length or final/partial data", n, source, permutation);
    if (memcmp(trace, expected_trace, (size_t)out[0] * sizeof(*trace)) != 0)
        fail("trace differs from solc", n, source, permutation);
    for (unsigned i = 0; i < out[0]; i++) {
        unsigned depth = trace[i];
        if (depth == 0U || depth > 16U || depth >= n)
            fail("invalid trace depth", n, source, permutation);
        unsigned pos = n - 1U - depth;
        unsigned value = replay[pos];
        replay[pos] = replay[n - 1U];
        replay[n - 1U] = value;
    }
    if (memcmp(data, replay, bytes) != 0)
        fail("trace does not reproduce data", n, source, permutation);
    if (status == 0U)
        for (unsigned i = 0; i < n; i++)
            if (data[permutation[i]] != source[i])
                fail("success does not meet input permutation", n, source, permutation);
    free(data);
    free(reference);
    free(p);
    free(target);
    free(used);
    free(replay);
    free(trace);
    free(expected_trace);
}

/* The solc internal operation requires a valid nonempty permutation.
   Exercise the C API's rejection contract without calling that operation. */
void check_rejected(unsigned n, const unsigned *source, const unsigned *permutation)
{
    unsigned out[3] = {99U, 99U, 99U};
    if (n == 0U || n > TEST_LIMIT) {
        unsigned status = permute(n, NULL, NULL, NULL, NULL, NULL, out);
        if (status != (n == 0U ? 0U : 2U) ||
            out[0] != 0U || out[1] != 0U || out[2] != 0U)
            fail("size rejection", 0U, NULL, NULL);
        return;
    }
    unsigned *data = buffer(n), *p = buffer(n), *target = buffer(n);
    unsigned *used = buffer(n), *trace = buffer(2U * n);
    size_t bytes = (size_t)n * sizeof(*data);
    memcpy(data, source, bytes);
    memcpy(p, permutation, bytes);
    unsigned status = permute(n, data, p, target, used, trace, out);
    if (status != 2U || out[0] != 0U || out[1] != 0U || out[2] != 0U ||
        memcmp(data, source, bytes) != 0 || memcmp(p, permutation, bytes) != 0)
        fail("permutation rejection", n, source, permutation);
    free(data);
    free(p);
    free(target);
    free(used);
    free(trace);
}
