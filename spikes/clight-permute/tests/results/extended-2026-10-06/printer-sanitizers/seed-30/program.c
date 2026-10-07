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
  v9 = 4294967295U;
  v10 = 7U;
  v11 = 16U;
  v12 = 16U;
  v13 = 2147483647U;
  v7[0U] = 0U;
  v7[1U] = 0U;
  v7[2U] = 0U;
  if (((v3[(5U + (4294967295U - 4294967295U))] + v3[(8U - 8U)]) + (v2[(8U - 8U)] - v7[2U])) != ((v7[1U] + v2[(1U + (4294967295U - 4294967295U))]) - (v7[2U] + v3[(2147483651U - 2147483648U)]))) {
    v2[(1U + (4294967295U - 4294967295U))] = (((v3[1U] - 16U) - (v2[(2147483654U - 2147483648U)] - v12)) - ((8U + v3[(4294967295U + 8U)]) + (v7[1U] + v7[1U])));
  } else {
    v2[(4294967295U + 7U)] = (((v12 - v13) + (v3[(3U + (4294967295U - 4294967295U))] + v7[2U])) + ((v2[(4294967295U + 5U)] - v2[(4294967295U + 2U)]) + (v2[(2147483652U - 2147483648U)] - v2[(4294967295U + 8U)])));
    if (((v2[(4294967295U + 5U)] - v3[4U]) - (7U - 16U)) == ((v3[(2147483655U - 2147483648U)] - v3[(1U + (4294967295U - 4294967295U))]) + (v3[(7U + (4294967295U - 4294967295U))] + v1))) {
      v12 = (((v12 + v3[0U]) - (v3[(2147483653U - 2147483648U)] + v12)) + ((2147483648U - v3[(2147483649U - 2147483648U)]) - (2147483647U + 0U)));
    } else {
      v10 = (((v7[1U] - v7[2U]) - (v2[(4294967295U + 5U)] + v3[(2147483648U - 2147483648U)])) - ((v7[1U] - 8U) - (v7[2U] + v2[(4294967295U + 8U)])));
    }
  }
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
      v2[(4U + (4294967295U - 4294967295U))] = (((4294967295U + v13) - (v7[1U] - v7[2U])) - ((v3[(5U + (4294967295U - 4294967295U))] - v7[2U]) - (v12 - v7[2U])));
      v9 = (v9 + 1U);
      if (((v10 + 1U) + (v11 - v2[(4294967295U + 5U)])) == ((v2[1U] + v3[(4294967295U + 4U)]) + (v3[(4294967295U + 2U)] + 16U))) {
        break;
      } else {
      }
      if (((v2[(2147483653U - 2147483648U)] - v7[2U]) + (v11 - 0U)) > ((v2[(1U + (4294967295U - 4294967295U))] + v10) + (v7[2U] - v10))) {
        return ((v7[2U] + v3[(15U - 8U)]) + (1U + v13));
      } else {
      }
    }
    v7[1U] = (((v12 + 2147483647U) - (v3[(2147483653U - 2147483648U)] - 2147483647U)) - ((v2[(9U - 8U)] + v2[1U]) - (v2[(10U - 8U)] + v12)));
    v8 = (v8 + 1U);
  }
  v11 = (((v3[(2147483648U - 2147483648U)] + v1) + (16U + 2147483647U)) + ((v7[1U] + v2[(14U - 8U)]) - (v13 + v7[2U])));
  return (((v11 + v1) - (v2[5U] + 7U)) - ((v13 - v2[2U]) - (v7[2U] + v3[(13U - 8U)])));
}
