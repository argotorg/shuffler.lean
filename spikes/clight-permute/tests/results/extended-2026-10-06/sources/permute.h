/* SPDX-License-Identifier: GPL-3.0-or-later */
#ifndef CLEAN_PERMUTE_H
#define CLEAN_PERMUTE_H

/* C11, x86-64 Linux, 32-bit unsigned int.
 * Each accessed pointer is the first element of a separate, live, writable unsigned
 * int array object. The six array objects are disjoint.
 * For 0 < n <= 1024: data/permutation/target/used each have n elements;
 * trace has 2*n elements. data and permutation are initialized inputs.
 * out always has 3 writable elements. Other pointers may be null for n==0 or n>1024.
 * Only this call may access these buffers during its execution.
 *
 * Return: 0 success; 1 blocked; 2 invalid input or defensive check failure.
 * out: trace count, blocked position, excess depth (last two zero on success).
 * data and trace retain the completed swaps on a blocked return.
 * permutation, target, and used are scratch outputs; their contents are
 * unspecified on return. Read only the out[0] written trace elements.
 * On a rejected input permutation, data and permutation are unchanged.
 */
#ifdef __cplusplus
extern "C" {
#endif
unsigned int permute(unsigned int n, unsigned int *data,
    unsigned int *permutation, unsigned int *target, unsigned int *used,
    unsigned int *trace, unsigned int *out);
#ifdef __cplusplus
}
#endif
#endif
