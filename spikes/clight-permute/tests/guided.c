/* SPDX-License-Identifier: GPL-3.0-or-later */
/* libFuzzer entry point. Missing input bytes have value zero.
 * Byte 0: bit 7 selects a 1024-element limit (otherwise 32); low two bits:
 *   0: full unsigned values + shuffle choices; 1: raw permutation;
 *   2: empty/oversized API input; 3: values modulo four + shuffle choices.
 * Bytes 1..2: little-endian n-1 modulo the selected limit.
 * Remaining records: u32 value + u16 shuffle choice, or u32 raw destination.
 */
#include "test.h"

#include <limits.h>
#include <stddef.h>
#include <stdint.h>

static unsigned read_word(const uint8_t *bytes, size_t size, size_t offset,
    unsigned width)
{
    unsigned value = 0U;
    for (unsigned i = 0U; i < width; i++)
        if (offset + i < size)
            value |= (unsigned)bytes[offset + i] << (8U * i);
    return value;
}

int LLVMFuzzerTestOneInput(const uint8_t *bytes, size_t size)
{
    _Static_assert(UINT_MAX == 4294967295U, "32-bit unsigned required");
    if (size == 0U)
        return 0;
    unsigned mode = bytes[0] & 3U;
    if (mode == 2U) {
        unsigned n = read_word(bytes, size, 1U, 4U);
        check_rejected(n <= TEST_LIMIT ? 0U : n, NULL, NULL);
        return 0;
    }
    unsigned limit = (bytes[0] & 128U) != 0U ? TEST_LIMIT : 32U;
    unsigned n = 1U + read_word(bytes, size, 1U, 2U) % limit;
    unsigned data[TEST_LIMIT], p[TEST_LIMIT], seen[TEST_LIMIT] = {0U};
    unsigned stride = mode == 1U ? 8U : 6U;
    unsigned valid = 1U;
    for (unsigned i = 0U; i < n; i++) {
        size_t offset = 3U + (size_t)stride * i;
        unsigned value = read_word(bytes, size, offset, 4U);
        data[i] = mode == 3U ? value % 4U : value;
        p[i] = mode == 1U ? read_word(bytes, size, offset + 4U, 4U) : i;
        if (mode == 1U) {
            if (p[i] >= n || seen[p[i]] != 0U)
                valid = 0U;
            else
                seen[p[i]] = 1U;
        }
    }
    if (mode != 1U)
        for (unsigned i = n; i > 1U; i--) {
            unsigned j = read_word(bytes, size, 3U + 6U * (i - 1U) + 4U, 2U) % i;
            unsigned value = p[i - 1U];
            p[i - 1U] = p[j];
            p[j] = value;
        }
    if (valid != 0U)
        check_case(n, data, p);
    else
        check_rejected(n, data, p);
    return 0;
}
