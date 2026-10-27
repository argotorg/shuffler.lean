/* SPDX-License-Identifier: GPL-3.0-or-later */
/* Observe the real decoder, then run the real differential/API checks.
 * Link with --wrap=check_case and --wrap=check_rejected.
 */
#include "test.h"

#include <assert.h>
#include <stdint.h>
#include <stdio.h>

int LLVMFuzzerTestOneInput(const uint8_t *bytes, size_t size);
void __real_check_case(unsigned n, const unsigned *data, const unsigned *p);
void __real_check_rejected(unsigned n, const unsigned *data, const unsigned *p);

static int is_permutation(unsigned n, const unsigned *p)
{
    if (n == 0U || n > TEST_LIMIT)
        return 0;
    for (unsigned destination = 0U; destination < n; destination++) {
        unsigned count = 0U;
        for (unsigned i = 0U; i < n; i++)
            count += p[i] == destination ? 1U : 0U;
        if (count != 1U)
            return 0;
    }
    return 1;
}

static void show(char route, unsigned n, const unsigned *data, const unsigned *p)
{
    printf("%c %u", route, n);
    if (n > 0U && n <= TEST_LIMIT) {
        for (unsigned i = 0U; i < n; i++)
            printf(" %u", data[i]);
        for (unsigned i = 0U; i < n; i++)
            printf(" %u", p[i]);
    }
    putchar('\n');
}

void __wrap_check_case(unsigned n, const unsigned *data, const unsigned *p)
{
    assert(is_permutation(n, p));
    __real_check_case(n, data, p);
    show('V', n, data, p);
}

void __wrap_check_rejected(unsigned n, const unsigned *data, const unsigned *p)
{
    assert(!is_permutation(n, p));
    if (n == 0U || n > TEST_LIMIT)
        assert(data == NULL && p == NULL);
    __real_check_rejected(n, data, p);
    show('R', n, data, p);
}

int main(void)
{
    uint8_t bytes[16384];
    size_t size = fread(bytes, 1U, sizeof(bytes), stdin);
    assert(!ferror(stdin) && fgetc(stdin) == EOF);
    return LLVMFuzzerTestOneInput(bytes, size);
}
