/*@
  predicate permutation{L}(unsigned int *p, integer n) =
    (\forall integer i; 0 <= i < n ==> 0 <= p[i] < n) &&
    (\forall integer i,j; 0 <= i < n && 0 <= j < n && p[i] == p[j] ==> i == j) &&
    (\forall integer j; 0 <= j < n ==> \exists integer i; 0 <= i < n && p[i] == j);

  predicate target_matches{L1,L2}(unsigned int *d, unsigned int *p,
                                  unsigned int *t, integer n) =
    \forall integer i; 0 <= i < n ==> \at(t[\at(p[i],L1)],L2) == \at(d[i],L1);

  predicate values_reachable{L}(unsigned int *d, unsigned int *p, integer n) =
    \forall integer i; 0 <= i < n && n - 1 - p[i] > 16 ==> d[p[i]] == d[i];

  logic integer replay_value{Input,Trace}(unsigned int *d, unsigned int *t,
                                         integer n, integer k, integer j) =
    k <= 0 ? \at(d[j],Input) :
      replay_value{Input,Trace}(d,t,n,k-1,
        j == n-1 ? n-1-\at(t[k-1],Trace) :
        j == n-1-\at(t[k-1],Trace) ? n-1 : j);

  logic integer moved{L}(unsigned int *p, integer k) =
    k <= 0 ? 0 : moved(p,k-1) + (p[k-1] != k-1 ? 1 : 0);

  logic integer occurrences{L}(unsigned int *d, integer k, integer value) =
    k <= 0 ? 0 : occurrences(d,k-1,value) + (d[k-1] == value ? 1 : 0);

  logic integer available{L}(unsigned int *t, unsigned int *u, integer k,
                            integer value) =
    k <= 0 ? 0 : available(t,u,k-1,value) +
      (u[k-1] == 0 && t[k-1] == value ? 1 : 0);

  logic integer pending{L}(unsigned int *d, unsigned int *t, integer k,
                          integer start, integer value) =
    k <= start ? 0 : pending(d,t,k-1,start,value) +
      (d[k-1] != t[k-1] && d[k-1] == value ? 1 : 0);
*/

/* SPDX-License-Identifier: GPL-3.0-or-later */
/* These are proof obligations. There are no user axioms in this file. */
/*@
  lemma moved_bounds{L}:
    \forall unsigned int *p, integer k;
      0 <= k ==> 0 <= moved(p,k) <= k;

  lemma moved_frame{A,B}:
    \forall unsigned int *p, integer k;
      0 <= k && (\forall integer i; 0 <= i < k ==> \at(p[i],A) == \at(p[i],B)) ==>
      moved{A}(p,k) == moved{B}(p,k);

  lemma moved_update{A,B}:
    \forall unsigned int *p, integer k,j;
      0 <= k && (\forall integer i; 0 <= i < k && i != j ==> \at(p[i],A) == \at(p[i],B)) ==>
      moved{B}(p,k) == moved{A}(p,k) +
        (0 <= j < k ? ((\at(p[j],B) != j ? 1 : 0) - (\at(p[j],A) != j ? 1 : 0)) : 0);
*/

/*@
  strategy SMT: \prover("CVC5", "Z3", 10.0);
  strategy InductMoved:
    \tactic("Wp.induction", \ingoal(L_moved(_,_,K)), \select(K),
      \param("base",0), \children(SMT));
  proof InductMoved: moved_bounds, moved_frame, moved_update;
*/
