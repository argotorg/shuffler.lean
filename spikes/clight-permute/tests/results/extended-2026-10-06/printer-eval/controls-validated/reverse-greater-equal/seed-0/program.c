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
  v8 = 0U;
  v9 = 2147483648U;
  v10 = 2147483647U;
  v11 = 16U;
  v12 = 7U;
  v13 = 8U;
  v7[0U] = 0U;
  v7[1U] = 0U;
  v7[2U] = 0U;
  v3[(4294967295U + 5U)] = (((2147483648U + v1) + (7U - 0U)) + ((v13 + v13) + (v7[2U] + v7[2U])));
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
      v13 = (((v2[7U] - v10) + (v7[1U] + v1)) - ((2147483648U + 4294967295U) - (0U - v1)));
      v9 = (v9 + 1U);
      if (((8U + 2147483648U) - (v7[2U] + 4294967295U)) > ((v7[2U] + v3[3U]) - (v1 + 0U))) {
        break;
      } else {
      }
      if (((v7[1U] - 1U) - (4294967295U + v12)) <= ((v3[(4294967295U + 4U)] - v3[(4294967295U + 6U)]) + (8U - v2[(7U + (4294967295U - 4294967295U))]))) {
        return ((8U - 16U) - (v7[2U] - v7[2U]));
      } else {
      }
    }
    v2[(14U - 8U)] = (((v2[(9U - 8U)] - v3[3U]) + (v7[2U] - v7[1U])) + ((v7[1U] + v3[(4294967295U + 1U)]) - (v7[1U] + v2[(10U - 8U)])));
    v3[(2147483655U - 2147483648U)] = (((v3[(12U - 8U)] + v2[(12U - 8U)]) + (v7[1U] - 1U)) - ((v7[1U] + v7[2U]) + (v10 + v1)));
    v2[3U] = (((v3[(2147483648U - 2147483648U)] - v3[(4294967295U + 2U)]) - (v2[(4294967295U + 2U)] + v2[(13U - 8U)])) - ((7U - v7[1U]) - (v7[1U] - v12)));
    v8 = (v8 + 1U);
  }
  v7[2U] = (((v7[1U] - v3[(6U + (4294967295U - 4294967295U))]) - (v7[2U] - v3[(15U - 8U)])) - ((v7[1U] + v3[(4294967295U + 3U)]) + (v2[(4294967295U + 3U)] + v2[2U])));
  return (((7U - 4294967295U) + (4294967295U - v1)) - ((v3[(2147483650U - 2147483648U)] + 4294967295U) + (v12 - 4294967295U)));
}
