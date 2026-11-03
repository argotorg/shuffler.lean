// SPDX-License-Identifier: GPL-3.0-or-later
// Demonstrate why a successful-allocation premise is necessary for the oracle.
#include "../../permute.h"
#include "../test.h"
#include <cstdio>
#include <new>

extern "C" void *__real__Znwm(std::size_t);
static bool fail_new;

extern "C" void *__wrap__Znwm(std::size_t size)
{
    if (fail_new)
        throw std::bad_alloc();
    return __real__Znwm(size);
}

int main()
{
    unsigned data[2] = {7, 8}, reference[2] = {7, 8};
    unsigned p[2] = {1, 0}, reference_p[2] = {1, 0};
    unsigned target[2], used[2], trace[4], out[3];
    unsigned reference_trace[4], reference_out[3];
    unsigned status = permute(2, data, p, target, used, trace, out);
    if (status != 0 || data[0] != 8 || data[1] != 7)
        return 1;
    fail_new = true;
    try {
        (void)solc_permute(2, reference, reference_p, reference_trace, reference_out);
    } catch (const std::bad_alloc&) {
        fail_new = false;
        std::puts("C returns success; the unchanged C++ oracle throws bad_alloc.");
        return 0;
    }
    return 1;
}
