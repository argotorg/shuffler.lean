# SPDX-License-Identifier: GPL-3.0-or-later
"""Termination annotations for the seven loops in the emitted C.
The ghost counter bounds the number of main-loop iterations. It cannot
change production state. The rank counts nonfixed entries below the top.
Its helper lemmas and proof strategies are in lemmas.acsl.
"""
LOOPS = (
    r'''/*@ loop invariant original_permutation:
        \forall integer j; 0 <= j < v1 ==> v3[j] == \at(v3[j],Pre);
      loop invariant bounds: 0 <= v8 <= v1;
      loop invariant clear: \forall integer j; 0 <= j < v8 ==> v5[j] == 0;
      loop assigns v8, v5[0 .. v1-1];
      loop variant v1-v8;
  */''',
    r'''/*@ loop invariant original_permutation:
        \forall integer j; 0 <= j < v1 ==> v3[j] == \at(v3[j],Pre);
      loop invariant bounds: 0 <= v8 <= v1;
      loop assigns v8, v9, v4[0 .. v1-1], v5[0 .. v1-1];
      loop variant v1-v8;
  */''',
    r'''/*@ loop invariant bounds: 0 <= v8 <= v1;
      loop invariant permutation_bounds: \forall integer j; 0 <= j < v1 ==> 0 <= v3[j] < v1;
      loop invariant processed: \forall integer j; 0 <= j < v8 ==>
        (v5[j] == 1 && v3[j] == j && v2[j] == v4[j]) || (v5[j] == 0 && v2[j] != v4[j]);
      loop assigns v8, v3[0 .. v1-1], v5[0 .. v1-1];
      loop variant v1-v8;
  */''',
    r'''/*@ loop invariant bounds: 0 <= v8 <= v1;
      loop invariant permutation_bounds: \forall integer j; 0 <= j < v1 ==> 0 <= v3[j] < v1;
      loop invariant fixed: \forall integer j; 0 <= j < v1 && v2[j] == v4[j] ==> v3[j] == j && v5[j] == 1;
      loop invariant selected_marked: \forall integer i; 0 <= i < v1 &&
        (i < v8 || v2[i] == v4[i]) ==> v5[v3[i]] != 0;
      loop invariant injective_selected: \forall integer i,j;
        0 <= i < v1 && 0 <= j < v1 && (i < v8 || v2[i] == v4[i]) &&
        (j < v8 || v2[j] == v4[j]) && v3[i] == v3[j] ==> i == j;
      loop assigns v8, v9, v3[0 .. v1-1], v5[0 .. v1-1];
      loop variant v1-v8;
  */''',
    r'''/*@ loop invariant bounds: 0 <= v9 <= v1;
          loop assigns v9;
          loop variant v1-v9;
      */''',
    r'''/*@ loop invariant rank_budget: 2*moved(v3,v10) + (v3[v10] == v10 ? 1 : 0) <= proof_steps;
      loop invariant steps: 0 <= proof_steps <= 2*v1;
      loop invariant top: v10 == v1-1;
      loop invariant permutation_bounds: \forall integer j; 0 <= j < v1 ==> 0 <= v3[j] < v1;
      loop invariant permutation_injective: injective(v3,v1);
      loop assigns proof_steps, v11, v12, v13, v2[0 .. v1-1], v3[0 .. v1-1], v6[0 .. 2*v1-1], v7[0 .. 2];
      loop variant proof_steps;
  */''',
    r'''/*@ loop invariant bounds: 0 <= v11 <= v10;
          loop assigns v11;
          loop variant v11;
      */''',
)
BEFORE = (
    ('      v3[v8] = v9;', r'''      /*@ assert fill_unused: v5[v9] == 0; */
      /*@ assert fill_fresh: \forall integer i; 0 <= i < v1 &&
        (i < v8 || v2[i] == v4[i]) ==> v3[i] != v9; */
      /*@ assert fill_pre_injective: selected_injective(v2,v4,v3,v1,v8); */
      /*@ assert fill_pre_marked: selected_marked(v2,v4,v3,v5,v1,v8); */
      /*@ assert fill_addresses: v3+v8 != v5+v9; */
      /*@ ghost proof_fill: ; */
'''),
    ('  v10 = (v1 - 1U);', r'''  /*@ assert ghost_initial_safe: 0 <= 2*v1 <= 2048; */
  /*@ ghost int proof_steps = 2*v1; */
'''),
    ('    if (v2[v11] != v2[v10]) {', r'''    /*@ assert chosen_bounds: 0 <= v11 < v10; */
    /*@ assert chosen_not_fixed: v3[v11] != v11; */
    /*@ assert chosen_destination: v3[v10] != v10 ==> v11 == v3[v10]; */
    /*@ assert chosen_top: v3[v10] == v10 ==> v3[v11] != v10; */
'''),
    ('      v6[v7[0U]] = v13;', r'''      /*@ assert data_count_frame: v7[0] == \at(v7[0],LoopCurrent); */
      /*@ assert append_room: v7[0] < 2*v1; */
'''),
    ('    v12 = v3[v11];', r'''    /*@ assert swap_permutation_bounds: \forall integer j; 0 <= j < v1 ==> 0 <= v3[j] < v1; */
    /*@ assert permutation_frame: \forall integer i; 0 <= i < v1 ==>
      v3[i] == \at(v3[i],LoopCurrent); */
    /*@ assert swap_chosen_bounds: 0 <= v11 < v10; */
    /*@ assert swap_chosen_not_fixed: v3[v11] != v11; */
    /*@ assert swap_chosen_destination: v3[v10] != v10 ==> v11 == v3[v10]; */
    /*@ assert swap_chosen_top: v3[v10] == v10 ==> v3[v11] != v10; */
    /*@ assert swap_injective: injective(v3,v1); */
    /*@ assert swap_top_frame: v3[v10] == \at(v3[v10],LoopCurrent); */
    /*@ assert swap_position_frame: v3[v11] == \at(v3[\at(v11,Here)],LoopCurrent); */
    /*@ assert rank_frame: moved(v3,v10) == moved{LoopCurrent}(v3,v10); */
    /*@ assert swap_rank_budget: 2*moved(v3,v10) + (v3[v10] == v10 ? 1 : 0) <= proof_steps; */
    /*@ ghost proof_swap: ; */
'''),
)
AFTER = (
    ('      v5[v9] = 1U;', r'''      /*@ assert fill_data_frame: \forall integer i; 0 <= i < v1 ==> v2[i] == \at(v2[i],proof_fill); */
      /*@ assert fill_target_frame: \forall integer i; 0 <= i < v1 ==> v4[i] == \at(v4[i],proof_fill); */
      /*@ assert fill_perm_frame: \forall integer i; 0 <= i < v1 && i != v8 ==> v3[i] == \at(v3[i],proof_fill); */
      /*@ assert fill_used_frame: \forall integer i; 0 <= i < v1 && i != v9 ==> v5[i] == \at(v5[i],proof_fill); */
      /*@ assert fill_destination: v3[v8] == v9; */
      /*@ assert fill_mark: v5[v9] != 0; */
      /*@ assert fill_post_injective: selected_injective(v2,v4,v3,v1,v8+1); */
      /*@ assert fill_post_marked: selected_marked(v2,v4,v3,v5,v1,v8+1); */
'''),
    ('    v3[v10] = v12;', r'''    /*@ assert swap_prefix_frame: \forall integer i; 0 <= i < v10 && i != v11 ==>
      v3[i] == \at(v3[i],proof_swap); */
    /*@ assert swap_endpoints: v3[v11] == \at(v3[v10],proof_swap) &&
      v3[v10] == \at(v3[v11],proof_swap); */
    /*@ assert swap_full_frame: \forall integer i; 0 <= i < v1 && i != v11 && i != v10 ==>
      v3[i] == \at(v3[i],proof_swap); */
    /*@ assert swap_post_bounds: \forall integer i; 0 <= i < v1 ==> 0 <= v3[i] < v1; */
    /*@ assert swap_post_injective: injective(v3,v1); */
    /*@ assert rank_change: moved(v3,v10) == moved{proof_swap}(v3,v10) -
      (\at(v3[v10],proof_swap) == v10 ? 0 : 1); */
    /*@ assert rank_decreased: 2*moved(v3,v10) + (v3[v10] == v10 ? 1 : 0) <
      2*moved{proof_swap}(v3,v10) + (\at(v3[v10],proof_swap) == v10 ? 1 : 0); */
    /*@ assert swap_post_budget: 2*moved(v3,v10) + (v3[v10] == v10 ? 1 : 0) <= proof_steps-1; */
    /*@ assert ghost_step_safe: 1 <= proof_steps <= 2048; */
    /*@ ghost proof_steps--; */
'''),
)
