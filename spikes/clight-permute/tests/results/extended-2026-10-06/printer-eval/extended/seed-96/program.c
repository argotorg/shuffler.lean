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
  v8 = 8U;
  v9 = 4294967295U;
  v10 = 2147483647U;
  v11 = 1U;
  v12 = 16U;
  v13 = 4294967295U;
  v7[0U] = 0U;
  v7[1U] = 0U;
  v7[2U] = 0U;
  v12 = (((v7[1U] + 0U) - (1U + v2[(2147483652U - 2147483648U)])) + ((2147483648U - v2[(1U + (4294967295U - 4294967295U))]) + (v2[(14U - 8U)] - v3[(13U - 8U)])));
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
      if (((v13 + v11) - (v7[1U] + v2[(4294967295U + 7U)])) > ((v7[2U] - v7[2U]) + (v13 + v3[6U]))) {
        if (((v10 - v12) - (v13 + v3[(8U - 8U)])) >= ((v7[2U] + 4294967294U) + (16U + v11))) {
          v3[6U] = (((v2[(5U + (4294967295U - 4294967295U))] + v7[1U]) - (v3[(12U - 8U)] - v3[(4294967295U + 2U)])) - ((v7[2U] - v2[(4294967295U + 8U)]) + (v2[(3U + (4294967295U - 4294967295U))] - v1)));
        } else {
          v2[6U] = (((v3[5U] - 4294967294U) + (2147483648U + v7[2U])) - ((v10 + v3[(2147483649U - 2147483648U)]) - (v1 - v1)));
        }
      } else {
        v7[1U] = (((16U - 16U) + (v2[(2147483649U - 2147483648U)] + v3[(4294967295U + 5U)])) + ((v1 - v3[2U]) + (4294967295U - v3[(2147483653U - 2147483648U)])));
        v10 = (((v11 + v12) + (v2[5U] - v3[(2147483653U - 2147483648U)])) + ((v13 - v7[2U]) + (v7[2U] - 7U)));
      }
      v9 = (v9 + 1U);
      if (((v3[(2147483651U - 2147483648U)] + v10) - (16U - v11)) != ((16U - v2[0U]) - (v2[(4294967295U + 1U)] + v7[2U]))) {
        break;
      } else {
      }
      if (((v2[(2147483654U - 2147483648U)] + v3[(4294967295U + 8U)]) + (2147483648U - 8U)) == ((v10 - v12) - (v13 + v3[(8U - 8U)]))) {
        return ((v7[1U] - v7[2U]) + (v3[(2147483655U - 2147483648U)] + v7[2U]));
      } else {
      }
    }
    if (((v7[2U] - 7U) - (4294967294U + 2147483647U)) != ((v2[7U] - v7[2U]) - (v7[1U] - 4294967294U))) {
      v7[2U] = (((1U - v2[(4294967295U + 5U)]) - (v7[2U] - 1U)) - ((v7[2U] - 1U) + (v7[2U] + 1U)));
    } else {
      v2[(9U - 8U)] = (((v2[(13U - 8U)] + v13) - (v7[2U] + v7[1U])) - ((v12 + 7U) + (v3[(2U + (4294967295U - 4294967295U))] + v10)));
    }
    v7[1U] = (((0U - v11) + (4294967295U - v2[(2U + (4294967295U - 4294967295U))])) + ((v7[1U] + v2[(2147483655U - 2147483648U)]) + (1U - 2147483648U)));
    v11 = (((v2[(4294967295U + 6U)] + v2[0U]) + (v2[(2147483652U - 2147483648U)] - v7[2U])) - ((v12 - v3[(2147483648U - 2147483648U)]) - (v3[(4U + (4294967295U - 4294967295U))] + v7[2U])));
    v8 = (v8 + 1U);
  }
  v2[(15U - 8U)] = (((v2[(5U + (4294967295U - 4294967295U))] + v3[4U]) - (v7[2U] + 1U)) + ((16U + v2[(13U - 8U)]) - (v7[2U] + v3[(2147483649U - 2147483648U)])));
  return (((v3[(2147483649U - 2147483648U)] + v7[1U]) - (v7[1U] + v11)) + ((v2[(4294967295U + 7U)] - v2[(2147483651U - 2147483648U)]) + (v3[(4294967295U + 5U)] + v2[(4294967295U + 5U)])));
}
