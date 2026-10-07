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
  v8 = 4294967294U;
  v9 = 8U;
  v10 = 4294967294U;
  v11 = 1U;
  v12 = 16U;
  v13 = 4294967295U;
  v7[0U] = 0U;
  v7[1U] = 0U;
  v7[2U] = 0U;
  v7[1U] = (((v1 + v7[1U]) + (7U + 0U)) - ((v3[(8U - 8U)] + v1) - (v7[1U] + 1U)));
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
      v2[(12U - 8U)] = (((v2[4U] + v3[(2147483655U - 2147483648U)]) + (1U - v1)) + ((v7[1U] - 8U) + (v3[(8U - 8U)] - v7[1U])));
      v3[(2147483654U - 2147483648U)] = (((v2[(12U - 8U)] + v3[6U]) - (4294967295U - v3[4U])) + ((0U + v2[3U]) + (v10 + v2[(2147483653U - 2147483648U)])));
      v9 = (v9 + 1U);
      if (((8U + v2[(2147483649U - 2147483648U)]) + (v2[(2147483653U - 2147483648U)] + v7[1U])) < ((v3[(4294967295U + 1U)] + v12) + (v11 - v3[(4294967295U + 3U)]))) {
        break;
      } else {
      }
      if (((v7[2U] - v7[2U]) - (v11 - v7[1U])) == ((v2[(2147483653U - 2147483648U)] + v2[(4294967295U + 1U)]) + (v2[(5U + (4294967295U - 4294967295U))] + 2147483647U))) {
        return ((v3[(2147483648U - 2147483648U)] + v2[(2147483648U - 2147483648U)]) - (v2[3U] - v2[(2147483654U - 2147483648U)]));
      } else {
      }
    }
    v12 = (((v2[(12U - 8U)] + v2[(4294967295U + 3U)]) + (16U - v3[(10U - 8U)])) - ((v2[(10U - 8U)] - v2[(4294967295U + 6U)]) + (v7[1U] - v7[2U])));
    v1 = (((v2[(11U - 8U)] + v12) - (v3[(11U - 8U)] + v3[(15U - 8U)])) + ((v1 - v7[2U]) - (4294967295U + v11)));
    v11 = (((v11 - v2[(2147483655U - 2147483648U)]) - (v2[(14U - 8U)] + v2[6U])) + ((v7[2U] - 16U) - (v3[(4294967295U + 4U)] + 8U)));
    v8 = (v8 + 1U);
  }
  if (((v7[1U] + 7U) + (v7[2U] + v3[(3U + (4294967295U - 4294967295U))])) != ((v2[(3U + (4294967295U - 4294967295U))] - v7[1U]) + (v10 - v3[(2147483649U - 2147483648U)]))) {
    v3[(2147483649U - 2147483648U)] = (((v12 - v7[2U]) + (v3[7U] + v2[7U])) - ((v7[2U] - v13) + (v12 - v7[1U])));
  } else {
    v7[1U] = (((v3[(4294967295U + 3U)] - 2147483648U) + (v7[2U] - v7[2U])) + ((2147483648U + v7[2U]) + (v2[(4294967295U + 2U)] + v10)));
  }
  return (((v12 - 16U) - (v3[(4294967295U + 6U)] - v7[2U])) + ((v7[2U] - v7[1U]) - (v7[2U] + v3[(1U + (4294967295U - 4294967295U))])));
}
