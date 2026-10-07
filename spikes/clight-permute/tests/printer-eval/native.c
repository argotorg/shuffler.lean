/* SPDX-License-Identifier: GPL-3.0-or-later */
#include <limits.h>
#include <stdio.h>
#include "permute.h"

_Static_assert(UINT_MAX == 4294967295U, "uint32 ABI required");

int main(void) {
    unsigned int size, fuel;
    int fields;
    while ((fields = scanf("%u %u", &size, &fuel)) != EOF) {
        if (fields != 2 || size != 8) return 4;
        unsigned int data[8], permutation[8], out[3];
        for (unsigned int i = 0; i < 8; ++i)
            if (scanf("%u", &data[i]) != 1) return 4;
        for (unsigned int i = 0; i < 8; ++i)
            if (scanf("%u", &permutation[i]) != 1) return 4;
        unsigned int status = permute(8, data, permutation, NULL, NULL, NULL, out);
        if (out[0] != 0) return 5;
        printf("%u %u %u %u", status, out[0], out[1], out[2]);
        for (unsigned int i = 0; i < 8; ++i) printf(" %u", data[i]);
        for (unsigned int i = 0; i < 8; ++i) printf(" %u", permutation[i]);
        putchar('\n');
    }
    return 0;
}
