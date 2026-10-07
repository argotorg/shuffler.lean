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

unsigned int permute(unsigned int v1208925819614629174706176, unsigned int *v2417851639229258349412352, unsigned int *v3626777458843887524118528, unsigned int *v4835703278458516698824704, unsigned int *v6044629098073145873530880, unsigned int *v7253554917687775048237056, unsigned int *v8462480737302404222943232)
{
  v8462480737302404222943232[0U] = 0U;
  v8462480737302404222943232[1U] = (0U - 1U);
  v8462480737302404222943232[2U] = v2417851639229258349412352[(4294967295U + 1U)];
  v2417851639229258349412352[1U] = (v2417851639229258349412352[0U] + v3626777458843887524118528[1U]);
  v3626777458843887524118528[2U] = (v2417851639229258349412352[2U] - v3626777458843887524118528[0U]);
  return v8462480737302404222943232[2U];
}
