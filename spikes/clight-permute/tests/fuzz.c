/* SPDX-License-Identifier: GPL-3.0-or-later */
/* Deterministic differential fuzzing. Usage: fuzz [cases [seed]]. */
#include "test.h"

#include <errno.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>

static unsigned next(unsigned *state)
{
    unsigned x = *state;
    x ^= x << 13U;
    x ^= x >> 17U;
    x ^= x << 5U;
    *state = x;
    return x;
}

static unsigned argument(const char *text)
{
    char *end;
    errno = 0;
    unsigned long value = strtoul(text, &end, 0);
    if (errno != 0 || *text == '\0' || *end != '\0' ||
        value == 0UL || value > UINT_MAX) {
        fputs("arguments must be nonzero unsigned integers\n", stderr);
        exit(EXIT_FAILURE);
    }
    return (unsigned)value;
}

int main(int argc, char **argv)
{
    _Static_assert(UINT_MAX == 4294967295U, "fuzz uses 32-bit unsigned");
    if (argc > 3) {
        fputs("usage: fuzz [cases [seed]]\n", stderr);
        return EXIT_FAILURE;
    }
    unsigned cases = argc > 1 ? argument(argv[1]) : 20000U;
    unsigned seed = argc > 2 ? argument(argv[2]) : 0x9e3779b9U;
    unsigned state = seed, data[TEST_LIMIT], p[TEST_LIMIT];
    const unsigned bounds[] = {1U, 2U, 16U, 17U, 18U, 31U, 64U, 256U, 1024U};
    for (unsigned test = 0; test < cases; test++) {
        unsigned n = test % 64U == 0U ? bounds[(test / 64U) % 9U] :
            1U + next(&state) % 36U;
        unsigned mode = test % 6U;
        for (unsigned i = 0; i < n; i++) {
            unsigned value = next(&state);
            data[i] = mode == 0U ? 0U : mode == 1U ? value % 2U :
                mode == 2U ? value % 4U : mode == 3U ? i :
                mode == 4U ? (value % 2U == 0U ? UINT_MAX : 0U) : value;
            p[i] = i;
        }
        for (unsigned i = n; i > 1U; i--) {
            unsigned j = next(&state) % i;
            unsigned saved = p[i - 1U];
            p[i - 1U] = p[j];
            p[j] = saved;
        }
        check_case(n, data, p);
    }
    printf("fuzz: %u cases, seed %u\n", cases, seed);
    return EXIT_SUCCESS;
}
