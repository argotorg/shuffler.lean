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
  v17 = 8U;
  v19 = 4294967294U;
  v21 = 7U;
  v23 = 4294967294U;
  v25 = 2147483647U;
  v27 = 2147483647U;
  v15[0U] = 0U;
  v15[1U] = 0U;
  v15[2U] = 0U;
  if (((v15[2U] - v5[(3U + (4294967295U - 4294967295U))]) + (v7[(2147483652U - 2147483648U)] + v15[1U])) >= ((v7[2U] + 16U) - (v7[(4294967295U + 3U)] + v15[1U]))) {
    v7[(4294967295U + 4U)] = (((0U - 1U) - (v7[4U] - v7[(4294967295U + 5U)])) - ((v7[(5U + (4294967295U - 4294967295U))] - v27) - (v15[1U] + v15[2U])));
    v15[2U] = (((v3 - v5[(7U + (4294967295U - 4294967295U))]) + (2147483648U - 4294967294U)) - ((v23 + v5[(15U - 8U)]) - (v5[(2147483651U - 2147483648U)] + v5[(6U + (4294967295U - 4294967295U))])));
    v5[(0U + (4294967295U - 4294967295U))] = (((v15[1U] + v7[(2147483650U - 2147483648U)]) + (v3 + 8U)) + ((1U - 16U) + (v27 - v5[2U])));
    v7[6U] = (((v15[1U] + v5[(2147483648U - 2147483648U)]) - (v5[(12U - 8U)] + 16U)) - ((v25 - v7[(8U - 8U)]) + (v7[0U] + v5[0U])));
  } else {
    v5[0U] = (((v7[2U] - v3) - (v21 + 1U)) - ((v23 + v25) - (v5[(4294967295U + 7U)] + v7[(10U - 8U)])));
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
      if (((7U + v15[2U]) - (v15[1U] - v5[(1U + (4294967295U - 4294967295U))])) < ((v15[1U] + v7[(2147483652U - 2147483648U)]) - (v5[(2147483652U - 2147483648U)] + v25))) {
        v5[(2147483651U - 2147483648U)] = (((v5[6U] - 0U) - (v25 - v15[1U])) - ((v7[(4294967295U + 5U)] + v5[(4294967295U + 5U)]) + (16U - v7[(2U + (4294967295U - 4294967295U))])));
      } else {
        v15[2U] = (((0U - v7[5U]) + (v7[(2147483649U - 2147483648U)] - v15[2U])) + ((16U - v7[(4294967295U + 8U)]) - (7U - v5[0U])));
      }
      v19 = (v19 + 1U);
      if (((16U + v7[(2147483649U - 2147483648U)]) + (v3 - v5[(4294967295U + 6U)])) != ((7U - v15[2U]) - (v25 + 2147483648U))) {
        break;
      } else {
      }
      if (((v15[2U] + v15[1U]) - (v15[2U] + v7[7U])) >= ((v7[1U] - v7[(3U + (4294967295U - 4294967295U))]) - (v5[(3U + (4294967295U - 4294967295U))] + v5[7U]))) {
        return ((v7[1U] - v15[2U]) - (1U + v7[(4294967295U + 8U)]));
      } else {
      }
    }
    v15[2U] = (((1U + v7[(4294967295U + 5U)]) + (8U + 0U)) + ((v7[(2147483651U - 2147483648U)] - v25) - (v15[1U] + v7[(4294967295U + 3U)])));
    v17 = (v17 + 1U);
  }
  if (((v7[(2U + (4294967295U - 4294967295U))] - v15[2U]) + (v7[(7U + (4294967295U - 4294967295U))] + v15[1U])) > ((v7[2U] + v15[2U]) - (v5[(1U + (4294967295U - 4294967295U))] - 4294967295U))) {
    v5[4U] = (((7U + 4294967294U) - (v25 - v15[1U])) - ((v7[(8U - 8U)] + v7[2U]) - (2147483648U + v7[(14U - 8U)])));
  } else {
    v5[0U] = (((v5[(14U - 8U)] - v3) - (v5[(2147483649U - 2147483648U)] + 16U)) - ((v5[6U] - 2147483648U) + (4294967295U - 2147483648U)));
  }
  return (((8U - v15[1U]) - (v7[(10U - 8U)] - v5[(10U - 8U)])) - ((v5[(13U - 8U)] - v7[(2147483654U - 2147483648U)]) + (4294967295U + v27)));
}
