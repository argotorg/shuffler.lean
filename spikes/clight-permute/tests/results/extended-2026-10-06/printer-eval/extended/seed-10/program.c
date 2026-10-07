/* SPDX-License-Identifier: GPL-3.0-or-later */
/* Generated from Permute.permute by printer.ml. Do not edit. */
#include <limits.h>
#include "permute.h"
_Static_assert(CHAR_BIT == 8, "8-bit bytes required");
_Static_assert(sizeof(unsigned int) == 4, "32-bit unsigned int required");
_Static_assert(UINT_MAX == 4294967295U, "32-bit unsigned int required");
_Static_assert(INT_MAX == 2147483647, "32-bit int required");
_Static_assert(_Alignof(unsigned int) == 4, "4-byte alignment required");
_Static_assert(sizeof(void *) == 8, "64-bit pointers required");

unsigned int permute(unsigned int v3, unsigned int *v5, unsigned int *v7, unsigned int *v9, unsigned int *v11, unsigned int *v13, unsigned int *v15)
{
  unsigned int v17;
  unsigned int v19;
  unsigned int v21;
  unsigned int v23;
  unsigned int v25;
  unsigned int v27;
  v17 = 1U;
  v19 = 4294967295U;
  v21 = 0U;
  v23 = 4294967295U;
  v25 = 0U;
  v27 = 7U;
  v15[0U] = 0U;
  v15[1U] = 0U;
  v15[2U] = 0U;
  v7[(0U + (4294967295U - 4294967295U))] = (((v7[(4294967295U + 5U)] - v21) + (16U + v27)) + ((v5[(2147483651U - 2147483648U)] - v15[2U]) + (v15[2U] - 0U)));
  v17 = 0U;
  while (1) {
    if (v17 < 4U) {
    } else {
      break;
    }
    v19 = 0U;
    while (1) {
      if (v19 < 3U) {
      } else {
        break;
      }
      if (((v5[(2147483650U - 2147483648U)] - v5[(2147483655U - 2147483648U)]) + (v7[(2147483651U - 2147483648U)] - v5[(2147483651U - 2147483648U)])) < ((v5[3U] - v3) + (2147483648U + 0U))) {
        v7[(9U - 8U)] = (((v15[2U] - v15[2U]) - (0U - v7[(2147483648U - 2147483648U)])) + ((v23 + v7[4U]) + (v5[4U] + 1U)));
      } else {
        if (((v15[1U] - v5[2U]) - (v7[(4294967295U + 7U)] - v27)) == ((v7[(9U - 8U)] + v15[2U]) - (0U + v15[2U]))) {
          v15[1U] = (((v5[(13U - 8U)] + v15[1U]) + (v23 - 4294967294U)) + ((v5[(3U + (4294967295U - 4294967295U))] - v15[1U]) + (4294967295U + v7[(2147483651U - 2147483648U)])));
        } else {
          v23 = (((v5[(2147483651U - 2147483648U)] + 2147483647U) + (v7[(2147483651U - 2147483648U)] + v15[2U])) - ((7U + v7[(4294967295U + 6U)]) - (v5[(4294967295U + 6U)] - v21)));
        }
      }
      v19 = (v19 + 1U);
      if (((v5[(10U - 8U)] - 2147483648U) - (v5[0U] + v7[6U])) < ((v3 - v15[1U]) - (4294967295U - 1U))) {
        break;
      } else {
      }
      if (((v7[5U] - v7[(2147483651U - 2147483648U)]) + (v7[(2147483648U - 2147483648U)] + v21)) < ((v21 - v23) + (v27 + v5[(12U - 8U)]))) {
        return ((v5[(3U + (4294967295U - 4294967295U))] + v15[2U]) - (v5[(0U + (4294967295U - 4294967295U))] + v7[(2147483649U - 2147483648U)]));
      } else {
      }
    }
    v21 = (((v15[2U] - 0U) + (16U + v15[2U])) - ((v5[(10U - 8U)] + v27) - (v5[(4294967295U + 1U)] + v15[2U])));
    v17 = (v17 + 1U);
  }
  v15[2U] = (((8U + v5[7U]) - (4294967294U - v5[(2147483655U - 2147483648U)])) + ((v21 - v23) - (v25 + v5[(2147483649U - 2147483648U)])));
  return (((2147483648U - v27) + (v15[2U] - v15[2U])) - ((16U - v25) - (v27 - v7[(6U + (4294967295U - 4294967295U))])));
}
