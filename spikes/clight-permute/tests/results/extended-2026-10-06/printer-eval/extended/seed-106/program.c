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
  v17 = 7U;
  v19 = 7U;
  v21 = 2147483648U;
  v23 = 0U;
  v25 = 7U;
  v27 = 4294967295U;
  v15[0U] = 0U;
  v15[1U] = 0U;
  v15[2U] = 0U;
  v5[(2147483653U - 2147483648U)] = (((2147483648U + v7[(13U - 8U)]) + (v7[(0U + (4294967295U - 4294967295U))] + v3)) - ((v5[(4294967295U + 7U)] - 0U) - (v7[3U] + v15[1U])));
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
      v25 = (((v27 - 16U) + (v15[1U] - v15[2U])) - ((v15[1U] + v23) - (v5[(2U + (4294967295U - 4294967295U))] - v5[(4294967295U + 3U)])));
      v19 = (v19 + 1U);
      if (((v15[2U] + 8U) + (2147483647U + v15[2U])) == ((v23 + v7[(5U + (4294967295U - 4294967295U))]) - (v5[(5U + (4294967295U - 4294967295U))] + v5[(4294967295U + 1U)]))) {
        break;
      } else {
      }
      if (((v15[2U] + 7U) + (v25 + 2147483647U)) > ((v7[(4U + (4294967295U - 4294967295U))] - 4294967294U) - (1U + v3))) {
        return ((v7[0U] - v15[2U]) - (v7[(3U + (4294967295U - 4294967295U))] - v15[2U]));
      } else {
      }
    }
    v21 = (((16U + 8U) - (v5[(12U - 8U)] - 1U)) + ((v7[(9U - 8U)] - v5[(9U - 8U)]) - (v5[(2147483655U - 2147483648U)] - v15[1U])));
    v17 = (v17 + 1U);
  }
  if (((v5[(2147483649U - 2147483648U)] - v5[(5U + (4294967295U - 4294967295U))]) + (v15[1U] + v15[1U])) != ((v7[(14U - 8U)] + v7[(4U + (4294967295U - 4294967295U))]) + (v5[(4U + (4294967295U - 4294967295U))] - v15[1U]))) {
    v7[(1U + (4294967295U - 4294967295U))] = (((v5[(7U + (4294967295U - 4294967295U))] + v7[(14U - 8U)]) - (v21 - v15[1U])) - ((v3 - v25) + (0U + v7[(2147483652U - 2147483648U)])));
    v5[2U] = (((v27 + v5[5U]) - (v15[1U] + v5[(9U - 8U)])) + ((v7[(5U + (4294967295U - 4294967295U))] + 2147483648U) + (v5[(11U - 8U)] - v5[0U])));
    v21 = (((v5[(4294967295U + 1U)] + 8U) + (v5[7U] - v5[7U])) + ((v5[(4294967295U + 6U)] + v15[1U]) - (7U + v25)));
  } else {
    if (((v7[(15U - 8U)] - v25) - (v5[(4294967295U + 1U)] + v7[(2147483654U - 2147483648U)])) < ((v15[2U] + v5[0U]) - (v5[5U] + v7[(8U - 8U)]))) {
      v3 = (((v5[(11U - 8U)] - v7[(2147483655U - 2147483648U)]) - (v25 - v15[1U])) + ((v7[(4294967295U + 3U)] + v7[(15U - 8U)]) - (v15[1U] + v5[(2147483652U - 2147483648U)])));
    } else {
      v7[(2147483654U - 2147483648U)] = (((v27 + v7[(2147483655U - 2147483648U)]) - (v15[2U] + 16U)) - ((2147483647U + v7[(11U - 8U)]) + (v15[1U] - v15[2U])));
    }
    if (((v15[2U] + v5[0U]) - (v5[5U] + v7[(8U - 8U)])) != ((v15[2U] + v5[6U]) + (v7[(2147483654U - 2147483648U)] + v23))) {
      v15[1U] = (((v27 - v7[(2147483655U - 2147483648U)]) + (v15[1U] + v5[(9U - 8U)])) + ((v15[1U] + v7[(2147483652U - 2147483648U)]) - (v5[(2147483652U - 2147483648U)] - v7[(8U - 8U)])));
    } else {
      v21 = (((4294967295U + v7[(2147483651U - 2147483648U)]) - (v27 + v7[(4294967295U + 4U)])) + ((v15[2U] - v7[(7U + (4294967295U - 4294967295U))]) + (16U + v7[(6U + (4294967295U - 4294967295U))])));
    }
  }
  return (((v7[(2147483651U - 2147483648U)] - v15[1U]) - (v5[(4U + (4294967295U - 4294967295U))] - 2147483648U)) + ((v7[(8U - 8U)] - v23) + (4294967295U + v5[(12U - 8U)])));
}
