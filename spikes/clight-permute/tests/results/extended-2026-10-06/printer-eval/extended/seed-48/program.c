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
  v8 = 7U;
  v9 = 2147483648U;
  v10 = 8U;
  v11 = 1U;
  v12 = 4294967295U;
  v13 = 0U;
  v7[0U] = 0U;
  v7[1U] = 0U;
  v7[2U] = 0U;
  v13 = (((v2[1U] + 2147483647U) - (v7[1U] - v7[1U])) - ((v3[0U] - v10) - (v3[(7U + (4294967295U - 4294967295U))] - v12)));
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
      if (((v7[2U] + 0U) + (v7[1U] - v2[(9U - 8U)])) < ((v7[1U] - v2[(4U + (4294967295U - 4294967295U))]) - (16U - v3[(2147483651U - 2147483648U)]))) {
        v7[2U] = (((v2[3U] - v2[(7U + (4294967295U - 4294967295U))]) + (4294967295U - v2[(4294967295U + 7U)])) - ((v1 + v2[(15U - 8U)]) - (2147483648U + v2[(2147483654U - 2147483648U)])));
      } else {
        v7[2U] = (((v13 - v2[(3U + (4294967295U - 4294967295U))]) - (v7[2U] - v7[1U])) + ((v11 - v3[(4294967295U + 1U)]) + (v2[(4294967295U + 1U)] - 1U)));
      }
      if (((v7[1U] - v2[(4U + (4294967295U - 4294967295U))]) - (16U - v3[(2147483651U - 2147483648U)])) >= ((v2[(2147483651U - 2147483648U)] - v10) + (v1 + v1))) {
        v11 = (((8U + v12) + (v7[2U] + v3[(7U + (4294967295U - 4294967295U))])) - ((1U + v7[2U]) - (v10 + 7U)));
      } else {
        v7[1U] = (((v1 + v7[2U]) - (4294967295U - 4294967294U)) - ((16U + 4294967294U) - (16U - v13)));
      }
      v9 = (v9 + 1U);
      if (((v2[(3U + (4294967295U - 4294967295U))] + v3[1U]) + (1U - v2[(4294967295U + 2U)])) < ((v2[(6U + (4294967295U - 4294967295U))] - v7[2U]) + (16U + v11))) {
        break;
      } else {
      }
      if (((v3[(13U - 8U)] - v12) + (16U - v3[(2147483649U - 2147483648U)])) > ((v7[2U] + 0U) + (v7[1U] - v2[(9U - 8U)]))) {
        return ((v2[6U] - v7[2U]) + (v3[(2147483655U - 2147483648U)] + v2[(2147483655U - 2147483648U)]));
      } else {
      }
    }
    v3[2U] = (((v7[2U] - v3[(5U + (4294967295U - 4294967295U))]) - (v10 + v7[1U])) + ((v12 - v7[2U]) - (v3[(5U + (4294967295U - 4294967295U))] - v3[(4294967295U + 2U)])));
    v13 = (((8U - v3[(2147483655U - 2147483648U)]) - (v10 - v10)) + ((v10 + v12) + (v1 - v3[(5U + (4294967295U - 4294967295U))])));
    if (((v2[(5U + (4294967295U - 4294967295U))] + v3[(4294967295U + 2U)]) + (v10 + v7[1U])) > ((v10 + v2[(2147483648U - 2147483648U)]) - (v11 + v1))) {
      v3[(6U + (4294967295U - 4294967295U))] = (((7U - v7[2U]) - (v1 + v2[(4294967295U + 8U)])) - ((16U + 4294967295U) - (v1 - v13)));
    } else {
      v2[(6U + (4294967295U - 4294967295U))] = (((16U - v7[1U]) - (v3[(2U + (4294967295U - 4294967295U))] - v13)) + ((16U - v7[2U]) - (v7[1U] + 4294967295U)));
    }
    v8 = (v8 + 1U);
  }
  v2[(5U + (4294967295U - 4294967295U))] = (((v2[(4294967295U + 5U)] - 7U) - (v2[0U] - v3[(4294967295U + 1U)])) - ((v11 + v2[(4294967295U + 5U)]) + (v2[(4294967295U + 3U)] + v3[(2147483653U - 2147483648U)])));
  return (((v3[(11U - 8U)] - v7[1U]) - (v2[(1U + (4294967295U - 4294967295U))] + v1)) - ((8U + 4294967294U) + (v2[(2147483653U - 2147483648U)] + v3[(2147483651U - 2147483648U)])));
}
