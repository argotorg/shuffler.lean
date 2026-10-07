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
  v8 = 16U;
  v9 = 16U;
  v10 = 4294967295U;
  v11 = 4294967295U;
  v12 = 4294967294U;
  v13 = 2147483647U;
  v7[0U] = 0U;
  v7[1U] = 0U;
  v7[2U] = 0U;
  v2[(2147483650U - 2147483648U)] = (((v3[(4294967295U + 8U)] + v3[(2147483650U - 2147483648U)]) - (8U - 4294967294U)) + ((v7[1U] + v7[1U]) - (7U + v3[(14U - 8U)])));
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
      if (((7U + v3[3U]) - (v7[2U] - 2147483648U)) == ((0U + v2[(4294967295U + 4U)]) + (v7[2U] - v11))) {
        v7[2U] = (((v2[5U] + v2[(3U + (4294967295U - 4294967295U))]) + (v3[(4294967295U + 1U)] - v2[(4294967295U + 1U)])) - ((v3[(12U - 8U)] - v7[2U]) - (4294967294U + v3[(4294967295U + 4U)])));
      } else {
        v7[2U] = (((v2[(4294967295U + 4U)] - v13) + (v2[(2147483654U - 2147483648U)] + v7[1U])) + ((4294967294U - 7U) + (v10 - v1)));
      }
      v1 = (((v1 - 7U) - (2147483648U - v1)) - ((v3[(5U + (4294967295U - 4294967295U))] - 7U) - (v7[2U] - v7[2U])));
      v2[(3U + (4294967295U - 4294967295U))] = (((v7[2U] + v3[(4294967295U + 2U)]) + (v3[(15U - 8U)] - v10)) + ((v3[(9U - 8U)] - v11) - (v1 + v2[(13U - 8U)])));
      v9 = (v9 + 1U);
      if (((16U + v11) - (v7[2U] + v2[(2147483653U - 2147483648U)])) >= ((v2[(4294967295U + 4U)] + v13) + (v7[1U] + v7[2U]))) {
        break;
      } else {
      }
      if (((16U - v10) - (v7[2U] - v12)) >= ((7U + v3[3U]) - (v7[2U] - 2147483648U))) {
        return ((v7[2U] + v1) + (v2[(9U - 8U)] + 2147483647U));
      } else {
      }
    }
    if (((v7[2U] + v10) + (v3[(2147483655U - 2147483648U)] + v1)) >= ((v3[6U] - 4294967295U) - (v2[(2147483649U - 2147483648U)] + v2[(10U - 8U)]))) {
      v10 = (((v7[1U] + v10) + (8U + v12)) + ((v3[7U] + v3[(4U + (4294967295U - 4294967295U))]) - (v7[2U] + v10)));
    } else {
      v3[(2147483652U - 2147483648U)] = (((2147483648U - v11) - (1U - v2[5U])) + ((v7[1U] - v3[(14U - 8U)]) - (v2[(14U - 8U)] + v3[(2147483652U - 2147483648U)])));
    }
    v3[(2147483651U - 2147483648U)] = (((v2[(2147483652U - 2147483648U)] + 0U) + (16U - v11)) + ((v10 + v2[(1U + (4294967295U - 4294967295U))]) + (v13 - v3[(4294967295U + 3U)])));
    v13 = (((v7[2U] + v3[(4294967295U + 6U)]) - (v11 + 4294967295U)) - ((v2[(2147483650U - 2147483648U)] - v11) - (v13 + v2[(2U + (4294967295U - 4294967295U))])));
    v8 = (v8 + 1U);
  }
  v3[0U] = (((v2[(14U - 8U)] + 0U) + (v7[2U] + v10)) - ((7U + v13) - (v13 - v7[2U])));
  return (((v11 - v7[1U]) + (v2[(2147483652U - 2147483648U)] - v7[2U])) - ((1U + v3[0U]) + (v2[0U] + v3[(2147483652U - 2147483648U)])));
}
