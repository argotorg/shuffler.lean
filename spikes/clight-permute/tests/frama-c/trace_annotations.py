# SPDX-License-Identifier: GPL-3.0-or-later
"""Trace bounds, replay, and changes of values for the emitted C.

Snapshot labels record the trace before data swaps, output stores, and
permutation stores. These ghost statements do not read or write C state.
"""

LOOPS = (
    r'''/*@ loop invariant original_permutation:
        \forall integer j; 0 <= j < v1 ==> v3[j] == \at(v3[j],Pre);
      loop invariant data_unchanged: \forall integer j; 0 <= j < v1 ==> v2[j] == \at(v2[j],Pre);
      loop invariant out_clear: v7[0] == 0 && v7[1] == 0 && v7[2] == 0;
 loop invariant bounds: 0 <= v8 <= v1;
      loop invariant clear: \forall integer j; 0 <= j < v8 ==> v5[j] == 0;
      loop assigns v8, v5[0 .. v1-1];
      loop variant v1-v8;
  */''',
    r'''/*@ loop invariant original_permutation:
        \forall integer j; 0 <= j < v1 ==> v3[j] == \at(v3[j],Pre);
      loop invariant data_unchanged: \forall integer j; 0 <= j < v1 ==> v2[j] == \at(v2[j],Pre);
      loop invariant out_clear: v7[0] == 0 && v7[1] == 0 && v7[2] == 0;
 loop invariant bounds: 0 <= v8 <= v1;
      loop assigns v8, v9, v4[0 .. v1-1], v5[0 .. v1-1];
      loop variant v1-v8;
  */''',
    r'''/*@
      loop invariant data_unchanged: \forall integer j; 0 <= j < v1 ==> v2[j] == \at(v2[j],Pre);
      loop invariant out_clear: v7[0] == 0 && v7[1] == 0 && v7[2] == 0;
 loop invariant bounds: 0 <= v8 <= v1;
      loop invariant permutation_bounds: \forall integer j; 0 <= j < v1 ==> v3[j] < v1;
      loop assigns v8, v3[0 .. v1-1], v5[0 .. v1-1];
      loop variant v1-v8;
  */''',
    r'''/*@
      loop invariant data_unchanged: \forall integer j; 0 <= j < v1 ==> v2[j] == \at(v2[j],Pre);
      loop invariant out_clear: v7[0] == 0 && v7[1] == 0 && v7[2] == 0;
 loop invariant bounds: 0 <= v8 <= v1;
      loop invariant permutation_bounds: \forall integer j; 0 <= j < v1 ==> v3[j] < v1;
      loop assigns v8, v9, v3[0 .. v1-1], v5[0 .. v1-1];
      loop variant v1-v8;
  */''',
    r'''/*@ loop invariant bounds: 0 <= v9 <= v1;
          loop assigns v9;
          loop variant v1-v9;
      */''',
    r'''/*@ loop invariant trace_bounds: \forall integer k; 0 <= k < v7[0] ==> 1 <= v6[k] <= 16 && v6[k] < v1;
      loop invariant trace_replay: \forall integer j; 0 <= j < v1 ==>
        v2[j] == replay_value{Pre,Here}(v2,v6,v1,v7[0],j);
      loop invariant trace_changes_values: trace_changes{Pre,Here}(v2,v6,v1,v7[0]);
      loop invariant top: v10 == v1-1;
      loop invariant permutation_bounds: \forall integer j; 0 <= j < v1 ==> v3[j] < v1;
      loop invariant count: 0 <= v7[0] <= 2*v1;
      loop assigns v11, v12, v13, v2[0 .. v1-1], v3[0 .. v1-1], v6[0 .. 2*v1-1], v7[0 .. 2];
  */''',
    r'''/*@ loop invariant bounds: 0 <= v11 <= v10;
          loop assigns v11;
          loop variant v11;
      */''',
)

BEFORE = (
    ('    if (v2[v11] != v2[v10]) {', r'''    /*@ assert trace_chosen_bounds: 0 <= v11 < v10; */
'''),
    ('        v7[1U] = v11;', r'''        /*@ ghost trace_blocked: ; */
'''),
    ('        return 1U;', r'''        /*@ assert trace_blocked_count: v7[0] == \at(v7[0],trace_blocked); */
        /*@ assert trace_blocked_prefix: \forall integer k; 0 <= k < v7[0] ==>
          v6[k] == \at(v6[k],trace_blocked); */
        /*@ assert trace_blocked_data: \forall integer j; 0 <= j < v1 ==>
          v2[j] == \at(v2[j],trace_blocked); */
        /*@ assert trace_blocked_replay: \forall integer k; 0 <= k <= v7[0] ==>
          replay_same{Pre,trace_blocked,Here}(v2,v6,v1,k); */
        /*@ assert trace_blocked_changes: trace_changes{Pre,Here}(v2,v6,v1,v7[0]); */
'''),
    ('      v12 = v2[v11];', r'''      /*@ assert trace_changing:
        replay_value{Pre,Here}(v2,v6,v1,v7[0],v10) !=
        replay_value{Pre,Here}(v2,v6,v1,v7[0],v11); */
      /*@ ghost trace_step: ; */
'''),
    ('      v6[v7[0U]] = v13;', r'''      /*@ assert trace_data_swap: \forall integer j; 0 <= j < v1 ==>
        v2[j] == \at(v2[j == v10 ? v11 : j == v11 ? v10 : j],trace_step); */
      /*@ assert trace_count_frame: v7[0] == \at(v7[0],trace_step); */
      /*@ assert append_room: v7[0] < 2*v1; */
'''),
    ('      v7[0U] = (v7[0U] + 1U);', r'''      /*@ assert trace_written: v6[\at(v7[0],trace_step)] == v13; */
      /*@ assert trace_prefix_written: \forall integer k; 0 <= k < \at(v7[0],trace_step) ==>
        v6[k] == \at(v6[k],trace_step); */
'''),
    ('    v12 = v3[v11];', r'''    /*@ assert trace_p_frame: \forall integer j; 0 <= j < v1 ==>
      v3[j] == \at(v3[j],LoopCurrent); */
    /*@ assert swap_permutation_bounds: \forall integer j; 0 <= j < v1 ==> v3[j] < v1; */
    /*@ assert trace_before_replay: \forall integer j; 0 <= j < v1 ==>
      v2[j] == replay_value{Pre,Here}(v2,v6,v1,v7[0],j); */
    /*@ assert trace_before_changes: trace_changes{Pre,Here}(v2,v6,v1,v7[0]); */
    /*@ assert trace_p_chosen_bounds: v3[v11] < v1 && v3[v10] < v1; */
    /*@ ghost trace_perm: ; */
'''),
)

AFTER = (
    ('      v7[0U] = (v7[0U] + 1U);', r'''      /*@ assert trace_prefix_frame: \forall integer k; 0 <= k < \at(v7[0],trace_step) ==>
        v6[k] == \at(v6[k],trace_step); */
      /*@ assert trace_old_replay: \forall integer k; 0 <= k <= \at(v7[0],trace_step) ==>
        replay_same{Pre,trace_step,Here}(v2,v6,v1,k); */

      /*@ assert trace_new_count: v7[0] == \at(v7[0],trace_step) + 1; */
      /*@ assert trace_after_replay: \forall integer j; 0 <= j < v1 ==>
        v2[j] == replay_value{Pre,Here}(v2,v6,v1,v7[0],j); */
      /*@ assert trace_after_bounds: \forall integer k; 0 <= k < v7[0] ==>
        1 <= v6[k] <= 16 && v6[k] < v1; */
      /*@ assert trace_kept_changes:
        trace_changes{Pre,Here}(v2,v6,v1,\at(v7[0],trace_step)); */
      /*@ assert trace_last_change:
        replay_value{Pre,Here}(v2,v6,v1,\at(v7[0],trace_step),v1-1) !=
        replay_value{Pre,Here}(v2,v6,v1,\at(v7[0],trace_step),v1-1-v6[\at(v7[0],trace_step)]); */
      /*@ assert trace_after_changes: trace_changes{Pre,Here}(v2,v6,v1,v7[0]); */
'''),
    ('    v3[v10] = v12;', r'''    /*@ assert trace_p_after_values: v3[v11] == \at(v3[v10],trace_perm) &&
      v3[v10] == \at(v3[v11],trace_perm); */
    /*@ assert trace_p_after_frame: \forall integer j; 0 <= j < v1 && j != v11 && j != v10 ==>
      v3[j] == \at(v3[j],trace_perm); */
    /*@ assert trace_swap_bounds: \forall integer j; 0 <= j < v1 ==> v3[j] < v1; */
    /*@ assert trace_perm_count: v7[0] == \at(v7[0],trace_perm); */
    /*@ assert trace_perm_prefix: \forall integer k; 0 <= k < v7[0] ==>
      v6[k] == \at(v6[k],trace_perm); */
    /*@ assert trace_perm_data: \forall integer j; 0 <= j < v1 ==>
      v2[j] == \at(v2[j],trace_perm); */
    /*@ assert trace_perm_replay: \forall integer k; 0 <= k <= v7[0] ==>
      replay_same{Pre,trace_perm,Here}(v2,v6,v1,k); */
    /*@ assert trace_final_changes: trace_changes{Pre,Here}(v2,v6,v1,v7[0]); */
'''),
)
