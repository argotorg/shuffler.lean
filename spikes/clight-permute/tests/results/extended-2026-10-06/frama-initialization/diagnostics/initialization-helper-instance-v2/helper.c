/* SPDX-License-Identifier: GPL-3.0-or-later */
/*@
 lemma initialized_by_surjection{A,B}:
   \forall unsigned int *p,*t, integer n;
     0 <= n &&
     (\forall integer j; 0 <= j < n ==> \exists integer i; 0 <= i < n && \at(p[i],A) == j) &&
     (\forall integer i; 0 <= i < n ==> \initialized{B}(t + \at(p[i],A))) ==>
     \initialized{B}(t + (0 .. n-1));
*/

/*@
 strategy SMT: \prover("CVC5", "Z3", 10.0);
 strategy InstantiateCover:
   \tactic("Wp.instance",
     \when(H: \forall integer j; 0 <= j ==> j < N ==> (\exists integer k; _)),
     \ingoal(shift_uint32(_, J)), \select(H), \param("P1", J),
     \children(SMT));
 proof InstantiateCover: initialized_by_surjection;
*/
