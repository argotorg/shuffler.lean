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

unsigned int permute(unsigned int v1, unsigned int *v2, unsigned int *v3, unsigned int *v4, unsigned int *v5, unsigned int *v6, unsigned int *v7)
{
  unsigned int v8;
  unsigned int v9;
  unsigned int v10;
  unsigned int v11;
  unsigned int v12;
  unsigned int v13;
  v8 = 2147483648U;
  v9 = 8U;
  v10 = 1U;
  v11 = 1U;
  v12 = 0U;
  v13 = 16U;
  v7[0U] = 0U;
  v7[1U] = 0U;
  v7[2U] = 0U;
  v12 = (((v7[1U] - v7[2U]) + (v2[(10U - 8U)] - v10)) + ((v7[2U] + v12) + (2147483647U + v3[(4294967295U + 6U)])));
  v8 = 0U;
  while (1) {
    if (v8 < 4U) {
    } else {
      break;
    }
    v9 = 0U;
    while (1) {
      if (v9 < 3U) {
      } else {
        break;
      }
      v3[6U] = (((v7[2U] - 2147483648U) - (v7[1U] - v2[1U])) + ((4294967294U + v2[(4294967295U + 2U)]) - (v11 - 2147483648U)));
      v9 = (v9 + 1U);
      if (((v13 - v7[1U]) + (v7[1U] + v7[2U])) >= ((4294967295U + v3[3U]) + (v3[(1U + (4294967295U - 4294967295U))] + v12))) {
        break;
      } else {
      }
      if (((2147483647U - 2147483647U) + (v3[(2147483652U - 2147483648U)] + 4294967294U)) == ((v7[2U] + v2[(4294967295U + 6U)]) + (v3[(4294967295U + 6U)] - v7[2U]))) {
        return ((v12 - v7[1U]) - (v3[(4294967295U + 3U)] - 2147483648U));
      } else {
      }
    }
    if (((2147483647U + 0U) + (v2[(12U - 8U)] - v2[(3U + (4294967295U - 4294967295U))])) < ((v2[(4294967295U + 4U)] + v7[1U]) + (7U + v11))) {
      v2[(9U - 8U)] = (((v2[(2U + (4294967295U - 4294967295U))] + 2147483648U) + (v3[6U] - v3[5U])) - ((0U + v7[1U]) - (v3[(2147483650U - 2147483648U)] + v2[(2147483650U - 2147483648U)])));
    } else {
      v7[2U] = (((v11 - 2147483648U) + (v2[(4294967295U + 7U)] + v3[5U])) + ((v7[2U] - 0U) - (v10 - v7[2U])));
    }
    v10 = (((v3[(8U - 8U)] + v2[(8U - 8U)]) + (v3[(4294967295U + 1U)] + 0U)) + ((7U - v10) + (v3[5U] - v13)));
    v8 = (v8 + 1U);
  }
  v7[2U] = (((v3[(2147483648U - 2147483648U)] - 2147483647U) - (v10 + v3[4U])) - ((v1 - v10) - (16U + v11)));
  if (((v13 - v2[(13U - 8U)]) + (v7[2U] + v11)) != ((v2[(4294967295U + 2U)] + v2[(4294967295U + 8U)]) + (v2[6U] + v7[1U]))) {
    v2[(0U + (4294967295U - 4294967295U))] = (((v3[2U] - 4294967295U) - (2147483647U - v7[2U])) + ((v3[(4294967295U + 4U)] - v3[(4294967295U + 1U)]) - (v7[2U] + v11)));
    v11 = (((8U + v2[(4294967295U + 6U)]) + (v7[1U] + 16U)) - ((16U - v7[2U]) + (v3[1U] - v2[1U])));
  } else {
    if (((v2[(4294967295U + 5U)] - v2[(2147483652U - 2147483648U)]) - (7U + 16U)) == ((v3[5U] - 8U) + (v3[7U] + 2147483647U))) {
      v7[1U] = (((v2[4U] - 1U) + (v2[(8U - 8U)] - v1)) + ((1U + 2147483647U) + (v1 - v3[(4294967295U + 3U)])));
    } else {
      v11 = (((2147483648U + v7[1U]) + (v7[2U] - v2[(6U + (4294967295U - 4294967295U))])) - ((v7[2U] - v3[(9U - 8U)]) - (2147483648U - v12)));
    }
  }
  return (((v3[(2147483649U - 2147483648U)] + v2[(2147483649U - 2147483648U)]) - (v13 - v2[(12U - 8U)])) - ((v7[2U] + v2[(9U - 8U)]) + (v3[(2147483649U - 2147483648U)] + v2[(2147483649U - 2147483648U)])));
}
