/* SPDX-License-Identifier: GPL-3.0-or-later */
/*@
 lemma initialized_by_surjection{A,B}:
   \forall unsigned int *p,*t, integer n;
     0 <= n &&
     (\forall integer j; 0 <= j < n ==> \exists integer i; 0 <= i < n && \at(p[i],A) == j) &&
     (\forall integer i; 0 <= i < n ==> \initialized{B}(t + \at(p[i],A))) ==>
     \initialized{B}(t + (0 .. n-1));
*/
