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

/*@
  predicate permutation{L}(unsigned int *p, integer n) =
    (\forall integer i; 0 <= i < n ==> 0 <= p[i] < n) &&
    (\forall integer i,j; 0 <= i < n && 0 <= j < n && p[i] == p[j] ==> i == j) &&
    (\forall integer j; 0 <= j < n ==> \exists integer i; 0 <= i < n && p[i] == j);

*/

/*@
  requires size: 1 <= v1 <= 1024;
  requires data_valid: \valid(v2 + (0 .. v1-1));
  requires permutation_valid: \valid(v3 + (0 .. v1-1));
  requires target_valid: \valid(v4 + (0 .. v1-1));
  requires used_valid: \valid(v5 + (0 .. v1-1));
  requires trace_valid: \valid(v6 + (0 .. 2*v1-1));
  requires out_valid: \valid(v7 + (0 .. 2));
  requires disjoint: \separated(v2 + (0 .. v1-1), v3 + (0 .. v1-1),
    v4 + (0 .. v1-1), v5 + (0 .. v1-1), v6 + (0 .. 2*v1-1), v7 + (0 .. 2));
  requires data_initialized: \initialized(v2 + (0 .. v1-1));
  requires permutation_initialized: \initialized(v3 + (0 .. v1-1));
  requires permutation_input: ((\forall integer i; 0 <= i < v1 ==> v3[i] < v1) &&
        (\forall integer i,j; 0 <= i < v1 && 0 <= j < v1 && v3[i] == v3[j] ==> i == j) &&
        (\forall integer j; 0 <= j < v1 ==> \exists integer i; 0 <= i < v1 && v3[i] == j));
  terminates \true;
  assigns v2[0 .. v1-1], v3[0 .. v1-1], v4[0 .. v1-1], v5[0 .. v1-1],
          v6[0 .. 2*v1-1], v7[0 .. 2];

  ensures status_range: 0 <= \result <= 2;
  ensures count: 0 <= v7[0] <= 2*v1;
  ensures out_initialized: \initialized(v7 + (0 .. 2));
  ensures data_initialized: \initialized(v2 + (0 .. v1-1));
  ensures permutation_initialized: \initialized(v3 + (0 .. v1-1));
  ensures trace_initialized: \initialized(v6 + (0 .. v7[0]-1));
*/
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
  /*@ loop invariant original_permutation:
        \forall integer j; 0 <= j < v1 ==> v3[j] == \at(v3[j],Pre);
      loop invariant permutation_initialized: \initialized(v3 + (0 .. v1-1));

      loop invariant data_initialized: \initialized(v2 + (0 .. v1-1));
      loop invariant data_unchanged: \forall integer j; 0 <= j < v1 ==> v2[j] == \at(v2[j],Pre);
      loop invariant out_initialized: \initialized(v7 + (0 .. 2));
      loop invariant out_clear: v7[0] == 0 && v7[1] == 0 && v7[2] == 0;
 loop invariant bounds: 0 <= v8 <= v1;
      loop invariant clear: \forall integer j; 0 <= j < v8 ==> v5[j] == 0;
      loop invariant initialized: \initialized(v5 + (0 .. v8-1));
      loop assigns v8, v5[0 .. v1-1];
      loop variant v1-v8;
  */
while (1) {
    if (v8 < v1) {
    } else {
      break;
    }
    v5[v8] = 0U;
    v8 = (v8 + 1U);
  }
  v8 = 0U;
  /*@ loop invariant original_permutation:
        \forall integer j; 0 <= j < v1 ==> v3[j] == \at(v3[j],Pre);
      loop invariant permutation_initialized: \initialized(v3 + (0 .. v1-1));

      loop invariant data_initialized: \initialized(v2 + (0 .. v1-1));
      loop invariant data_unchanged: \forall integer j; 0 <= j < v1 ==> v2[j] == \at(v2[j],Pre);
      loop invariant out_initialized: \initialized(v7 + (0 .. 2));
      loop invariant out_clear: v7[0] == 0 && v7[1] == 0 && v7[2] == 0;
 loop invariant bounds: 0 <= v8 <= v1;
      loop invariant initialized: \initialized(v5 + (0 .. v1-1));
      loop invariant filled_initialized: \forall integer i;
        0 <= i < v8 ==> \initialized(v4 + \at(v3[i],Pre));
      loop assigns v8, v9, v4[0 .. v1-1], v5[0 .. v1-1];
      loop variant v1-v8;
  */
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
    v4[v9] = (v2[v8]);
    v8 = (v8 + 1U);
  }
  v8 = 0U;
  /*@
      loop invariant data_initialized: \initialized(v2 + (0 .. v1-1));
      loop invariant data_unchanged: \forall integer j; 0 <= j < v1 ==> v2[j] == \at(v2[j],Pre);
      loop invariant out_initialized: \initialized(v7 + (0 .. 2));
      loop invariant out_clear: v7[0] == 0 && v7[1] == 0 && v7[2] == 0;
 loop invariant bounds: 0 <= v8 <= v1;
      loop invariant target_initialized: \initialized(v4 + (0 .. v1-1));
      loop invariant permutation_initialized: \initialized(v3 + (0 .. v1-1));
      loop invariant used_initialized: \initialized(v5 + (0 .. v1-1));
      loop invariant permutation_bounds: \forall integer j; 0 <= j < v1 ==> v3[j] < v1;
      loop assigns v8, v3[0 .. v1-1], v5[0 .. v1-1];
      loop variant v1-v8;
  */
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
  /*@
      loop invariant data_initialized: \initialized(v2 + (0 .. v1-1));
      loop invariant data_unchanged: \forall integer j; 0 <= j < v1 ==> v2[j] == \at(v2[j],Pre);
      loop invariant out_initialized: \initialized(v7 + (0 .. 2));
      loop invariant out_clear: v7[0] == 0 && v7[1] == 0 && v7[2] == 0;
 loop invariant bounds: 0 <= v8 <= v1;
      loop invariant target_initialized: \initialized(v4 + (0 .. v1-1));
      loop invariant permutation_initialized: \initialized(v3 + (0 .. v1-1));
      loop invariant used_initialized: \initialized(v5 + (0 .. v1-1));
      loop invariant permutation_bounds: \forall integer j; 0 <= j < v1 ==> v3[j] < v1;
      loop assigns v8, v9, v3[0 .. v1-1], v5[0 .. v1-1];
      loop variant v1-v8;
  */
while (1) {
    if (v8 < v1) {
    } else {
      break;
    }
    if (v2[v8] != v4[v8]) {
      v9 = 0U;
      /*@ loop invariant bounds: 0 <= v9 <= v1;
          loop assigns v9;
          loop variant v1-v9;
      */
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
  /*@ loop invariant top: v10 == v1-1;
      loop invariant data_initialized: \initialized(v2 + (0 .. v1-1));
      loop invariant permutation_initialized: \initialized(v3 + (0 .. v1-1));
      loop invariant out_initialized: \initialized(v7 + (0 .. 2));
      loop invariant permutation_bounds: \forall integer j; 0 <= j < v1 ==> v3[j] < v1;
      loop invariant count: 0 <= v7[0] <= 2*v1;
      loop invariant initialized: \initialized(v6 + (0 .. v7[0]-1));
      loop assigns v11, v12, v13, v2[0 .. v1-1], v3[0 .. v1-1], v6[0 .. 2*v1-1], v7[0 .. 2];
  */
while (1) {
    v11 = v3[v10];
    if (v11 == v10) {
      /*@ loop invariant bounds: 0 <= v11 <= v10;
          loop assigns v11;
          loop variant v11;
      */
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
      /*@ assert append_room: v7[0] < 2*v1; */
      /*@ assert append_initialized: \initialized(v6 + (0 .. v7[0]-1)); */
      v6[v7[0U]] = v13;
      /*@ assert append_written: \initialized(v6 + (0 .. v7[0])); */
      v7[0U] = (v7[0U] + 1U);
    } else {
    }
    /*@ assert swap_data_initialized: \initialized(v2 + (0 .. v1-1)); */
    /*@ assert swap_permutation_initialized: \initialized(v3 + (0 .. v1-1)); */
    /*@ assert swap_out_initialized: \initialized(v7 + (0 .. 2)); */
    /*@ assert swap_trace_initialized: \initialized(v6 + (0 .. v7[0]-1)); */
    /*@ assert swap_permutation_bounds: \forall integer j; 0 <= j < v1 ==> v3[j] < v1; */
    v12 = v3[v11];
    v3[v11] = v3[v10];
    v3[v10] = v12;
  }
}

/*@
  strategy InitSMT: \prover("CVC5", "Z3", 10.0);
  strategy InstantiateTargetCover:
    \tactic("Wp.instance",
      \when(H: \forall integer j; 0 <= j ==> j < N ==> (\exists integer k; _)),
      \goal(_[shift_uint32(_, J)]), \select(H), \param("P1", J),
      \children(InitSMT));
  proof InstantiateTargetCover: target_initialized;
*/
