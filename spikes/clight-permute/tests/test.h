/* SPDX-License-Identifier: GPL-3.0-or-later */
#ifndef PERMUTE_TEST_H
#define PERMUTE_TEST_H

#ifdef NDEBUG
#error "The oracle and boundary tests require active assertions"
#endif

#define TEST_LIMIT 1024U

#ifdef __cplusplus
extern "C" {
#endif
unsigned solc_permute(unsigned n, unsigned *data,
    const unsigned *permutation, unsigned *trace, unsigned *out);
void check_case(unsigned n, const unsigned *source,
    const unsigned *permutation);
void check_rejected(unsigned n, const unsigned *source,
    const unsigned *permutation);
#ifdef __cplusplus
}
#endif

#endif
