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
  v17 = 16U;
  v19 = 16U;
  v21 = 7U;
  v23 = 4294967295U;
  v25 = 2147483647U;
  v27 = 2147483648U;
  v15[0U] = 0U;
  v15[1U] = 0U;
  v15[2U] = 0U;
  v15[2U] = (((v5[(4294967295U + 5U)] - 1U) - (v7[(2147483653U - 2147483648U)] + v15[2U])) + ((v15[1U] + v15[1U]) - (16U - v5[(4294967295U + 3U)])));
  if (((v3 + v5[4U]) + (4294967295U + v3)) > ((v5[4U] + 1U) - (2147483648U - 2147483647U))) {
    v5[(0U + (4294967295U - 4294967295U))] = (((v23 - v5[(4294967295U + 1U)]) + (v5[(4294967295U + 5U)] + v7[2U])) - ((v5[2U] - v15[2U]) - (v7[1U] + 0U)));
  } else {
    v7[(4294967295U + 7U)] = (((v15[1U] + 8U) - (v7[7U] + v5[7U])) - ((v15[1U] + v5[0U]) + (7U + v5[(6U + (4294967295U - 4294967295U))])));
    v5[(4294967295U + 7U)] = (((v5[(14U - 8U)] - v23) - (v7[3U] - v5[3U])) - ((v21 - v7[(4294967295U + 1U)]) + (v21 - v15[1U])));
  }
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
      v25 = (((v7[(2147483649U - 2147483648U)] - v5[(2147483649U - 2147483648U)]) - (v27 + 16U)) - ((v15[2U] - v15[1U]) + (v15[1U] - v15[2U])));
      v19 = (v19 + 1U);
      if (((v15[2U] - v7[(15U - 8U)]) - (v3 - v5[(7U + (4294967295U - 4294967295U))])) < ((16U - v21) + (v21 - v21))) {
        break;
      } else {
      }
      if (((v25 - 16U) - (v7[(6U + (4294967295U - 4294967295U))] - v5[(6U + (4294967295U - 4294967295U))])) > ((v7[(10U - 8U)] - v15[2U]) - (v5[(4294967295U + 3U)] - 2147483647U))) {
        return ((v5[(4294967295U + 7U)] - v7[(2147483655U - 2147483648U)]) - (v5[(2147483655U - 2147483648U)] + v15[2U]));
      } else {
      }
    }
    if (((v7[(2147483654U - 2147483648U)] - v25) - (v21 + v7[2U])) > ((v3 - 4294967295U) + (1U - v7[(2147483651U - 2147483648U)]))) {
      v7[(7U + (4294967295U - 4294967295U))] = (((v15[1U] - v25) + (v5[0U] + v7[(4294967295U + 5U)])) - ((v5[(4294967295U + 5U)] + 4294967295U) + (v15[2U] + v5[(4294967295U + 2U)])));
    } else {
      v5[(7U + (4294967295U - 4294967295U))] = (((v23 + 8U) - (v5[3U] + v15[2U])) - ((v15[2U] + v3) + (v5[1U] + 7U)));
    }
    v17 = (v17 + 1U);
  }
  v5[(2147483650U - 2147483648U)] = (((v15[2U] + v7[(2147483653U - 2147483648U)]) - (v7[6U] - v15[2U])) - ((v5[(10U - 8U)] - v5[(2147483649U - 2147483648U)]) + (1U + 0U)));
  return (((2147483648U + v5[(9U - 8U)]) - (v3 + v7[4U])) - ((7U + v5[(3U + (4294967295U - 4294967295U))]) + (v15[2U] - v25)));
}
