/* SPDX-License-Identifier: GPL-3.0-or-later */
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include "permute.h"

_Static_assert(UINT_MAX == 4294967295U, "uint32 ABI required");

static unsigned int *allocate(unsigned int count) {
    unsigned int *result = malloc(sizeof(*result) * count);
    if (!result) exit(3);
    return result;
}

int main(void) {
    unsigned int size, fuel;
    int fields;
    while ((fields = scanf("%u %u", &size, &fuel)) != EOF) {
        if (fields != 2) return 4;
        unsigned int count = size > 0 && size <= 1024 ? size : 0;
        unsigned int *data = count ? allocate(count) : NULL;
        unsigned int *permutation = count ? allocate(count) : NULL;
        unsigned int *target = count ? allocate(count) : NULL;
        unsigned int *used = count ? allocate(count) : NULL;
        unsigned int *trace = count ? allocate(2 * count) : NULL;
        unsigned int out[3];
        for (unsigned int i = 0; i < count; ++i)
            if (scanf("%u", &data[i]) != 1) return 4;
        for (unsigned int i = 0; i < count; ++i)
            if (scanf("%u", &permutation[i]) != 1) return 4;
        unsigned int status = permute(size, data, permutation, target, used, trace, out);
        if (out[0] > 2 * count) return 5;
        printf("%u %u %u %u", status, out[0], out[1], out[2]);
        for (unsigned int i = 0; i < count; ++i) printf(" %u", data[i]);
        for (unsigned int i = 0; i < count; ++i) printf(" %u", permutation[i]);
        for (unsigned int i = 0; i < out[0]; ++i) printf(" %u", trace[i]);
        putchar('\n');
        free(data);
        free(permutation);
        free(target);
        free(used);
        free(trace);
    }
    return 0;
}
