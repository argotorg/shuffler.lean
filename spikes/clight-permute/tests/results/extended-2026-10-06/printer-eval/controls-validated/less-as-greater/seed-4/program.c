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
  v19 = 7U;
  v21 = 0U;
  v23 = 16U;
  v25 = 0U;
  v27 = 2147483647U;
  v15[0U] = 0U;
  v15[1U] = 0U;
  v15[2U] = 0U;
  v5[5U] = (((v7[(10U - 8U)] - 1U) + (1U - v7[(4294967295U + 6U)])) - ((v5[(4294967295U + 6U)] + v5[6U]) + (v5[(4294967295U + 3U)] - v15[1U])));
  if (((v5[(4294967295U + 6U)] + v5[6U]) + (v5[(4294967295U + 3U)] - v15[1U])) != ((4294967295U + v23) - (v7[(14U - 8U)] + v5[(14U - 8U)]))) {
    v5[(1U + (4294967295U - 4294967295U))] = (((v15[2U] - v23) - (v15[2U] - v5[(4294967295U + 1U)])) - ((v7[(2147483653U - 2147483648U)] - v15[2U]) + (v15[2U] - 4294967294U)));
  } else {
    v15[1U] = (((v7[3U] - v7[(4294967295U + 3U)]) + (4294967294U - 0U)) + ((1U - v25) - (v7[(4294967295U + 1U)] - v7[6U])));
  }
  if (((4294967295U + v23) - (v7[(14U - 8U)] + v5[(14U - 8U)])) >= ((v15[2U] + v27) + (v7[(2147483652U - 2147483648U)] + v15[2U]))) {
    v7[(4294967295U + 3U)] = (((v15[1U] - v25) + (v15[1U] + v7[(2147483654U - 2147483648U)])) - ((v7[(1U + (4294967295U - 4294967295U))] - 2147483647U) - (v5[(4294967295U + 7U)] + v15[2U])));
  } else {
    v5[(4294967295U + 3U)] = (((v7[(15U - 8U)] - v7[(2U + (4294967295U - 4294967295U))]) + (8U + v15[2U])) + ((16U + v7[(7U + (4294967295U - 4294967295U))]) + (v7[(2147483651U - 2147483648U)] - v15[1U])));
  }
  v17 = 0U;
  while (1) {
    if (v17 > 4U) {
    } else {
      break;
    }
    v19 = 0U;
    while (1) {
      if (v19 > 3U) {
      } else {
        break;
      }
      v7[5U] = (((v5[(9U - 8U)] - v27) - (v15[1U] + v15[2U])) - ((v5[(8U - 8U)] - v7[4U]) + (v25 - 2147483647U)));
      v19 = (v19 + 1U);
      if (((7U - v27) + (v27 - v15[1U])) > ((v15[1U] - v15[2U]) - (v23 + v15[1U]))) {
        break;
      } else {
      }
      if (((v23 - v15[2U]) + (v5[1U] - v5[(9U - 8U)])) >= ((0U + v5[6U]) - (v5[(2147483648U - 2147483648U)] + v5[(7U + (4294967295U - 4294967295U))]))) {
        return ((8U - v7[(6U + (4294967295U - 4294967295U))]) - (v5[(6U + (4294967295U - 4294967295U))] + v7[5U]));
      } else {
      }
    }
    v5[(2147483651U - 2147483648U)] = (((v27 + 8U) - (v15[2U] - v27)) + ((v23 - v15[1U]) + (v5[(2147483651U - 2147483648U)] + v15[1U])));
    v7[7U] = (((v21 - v5[(2147483654U - 2147483648U)]) + (v21 + 8U)) + ((v21 + v5[(4294967295U + 1U)]) - (v23 + v15[2U])));
    if (((v7[(2147483653U - 2147483648U)] - v7[(2147483655U - 2147483648U)]) - (v5[(2147483655U - 2147483648U)] - v23)) > ((v7[(3U + (4294967295U - 4294967295U))] - v5[(3U + (4294967295U - 4294967295U))]) + (v15[2U] - v15[2U]))) {
      v3 = (((v5[(5U + (4294967295U - 4294967295U))] - 2147483647U) + (4294967294U - v5[(6U + (4294967295U - 4294967295U))])) - ((4294967295U + v3) + (v7[(2147483651U - 2147483648U)] + 7U)));
    } else {
      v15[1U] = (((v15[2U] + 8U) + (1U - v15[2U])) - ((v5[6U] - v15[2U]) - (v7[3U] - v5[3U])));
    }
    v17 = (v17 + 1U);
  }
  v7[(2147483651U - 2147483648U)] = (((v7[5U] - 16U) + (v15[2U] - 2147483647U)) + ((v7[(3U + (4294967295U - 4294967295U))] - v25) + (v7[(2147483650U - 2147483648U)] - v7[(4294967295U + 6U)])));
  return (((16U + v5[(4294967295U + 8U)]) - (v7[(2U + (4294967295U - 4294967295U))] - 2147483648U)) + ((2147483647U - v3) + (2147483648U - 2147483647U)));
}
