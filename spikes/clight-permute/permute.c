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
  v7[0U] = 0U;
  v7[1U] = 0U;
  v7[2U] = 0U;
  if (v1 > 1024U) {
    return 2U;
  } else {
  }
  if (v1 == 0U) {
    return 0U;
  } else {
  }
  v8 = 0U;
  while (1) {
    if (v8 < v1) {
    } else {
      break;
    }
    v5[v8] = 0U;
    v8 = (v8 + 1U);
  }
  v8 = 0U;
  while (1) {
    if (v8 < v1) {
    } else {
      break;
    }
    v9 = v3[v8];
    if (v9 >= v1) {
      return 2U;
    } else {
    }
    if (v5[v9] != 0U) {
      return 2U;
    } else {
    }
    v5[v9] = 1U;
    v4[v9] = v2[v8];
    v8 = (v8 + 1U);
  }
  v8 = 0U;
  while (1) {
    if (v8 < v1) {
    } else {
      break;
    }
    if (v2[v8] == v4[v8]) {
      v3[v8] = v8;
      v5[v8] = 1U;
    } else {
      v5[v8] = 0U;
    }
    v8 = (v8 + 1U);
  }
  v8 = 0U;
  while (1) {
    if (v8 < v1) {
    } else {
      break;
    }
    if (v2[v8] != v4[v8]) {
      v9 = 0U;
      while (1) {
        if (v9 < v1) {
        } else {
          break;
        }
        if (v5[v9] == 0U) {
          if (v2[v8] == v4[v9]) {
            break;
          } else {
          }
        } else {
        }
        v9 = (v9 + 1U);
      }
      if (v9 == v1) {
        return 2U;
      } else {
      }
      v3[v8] = v9;
      v5[v9] = 1U;
    } else {
    }
    v8 = (v8 + 1U);
  }
  v10 = (v1 - 1U);
  while (1) {
    v11 = v3[v10];
    if (v11 == v10) {
      while (1) {
        if (v11 > 0U) {
        } else {
          break;
        }
        v11 = (v11 - 1U);
        if (v3[v11] != v11) {
          break;
        } else {
        }
      }
      if (v3[v11] == v11) {
        return 0U;
      } else {
      }
    } else {
    }
    if (v2[v11] != v2[v10]) {
      v13 = (v10 - v11);
      if (v13 > 16U) {
        v7[1U] = v11;
        v7[2U] = (v13 - 16U);
        return 1U;
      } else {
      }
      if (v7[0U] >= (v1 + v1)) {
        return 2U;
      } else {
      }
      v12 = v2[v11];
      v2[v11] = v2[v10];
      v2[v10] = v12;
      v6[v7[0U]] = v13;
      v7[0U] = (v7[0U] + 1U);
    } else {
    }
    v12 = v3[v11];
    v3[v11] = v3[v10];
    v3[v10] = v12;
  }
}
