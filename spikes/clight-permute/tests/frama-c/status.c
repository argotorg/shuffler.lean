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

/* SPDX-License-Identifier: GPL-3.0-or-later */
/* Definitions and proved lemma obligations. No user axioms. */
/*@ axiomatic Counts {
  logic integer occurrences{L}(unsigned int *d, integer k, integer value) =
    k <= 0 ? 0 : occurrences(d,k-1,value) + (d[k-1] == value ? 1 : 0);
  logic integer collected{L}(unsigned int *t, unsigned int *u, integer k, integer value) =
    k <= 0 ? 0 : collected(t,u,k-1,value) + (u[k-1] != 0 && t[k-1] == value ? 1 : 0);
  logic integer available{L}(unsigned int *t, unsigned int *u, integer k, integer value) =
    k <= 0 ? 0 : available(t,u,k-1,value) + (u[k-1] == 0 && t[k-1] == value ? 1 : 0);
  logic integer pending{L}(unsigned int *d, unsigned int *t, integer k, integer start, integer value) =
    k <= start ? 0 : pending(d,t,k-1,start,value) + (d[k-1] != t[k-1] && d[k-1] == value ? 1 : 0);

  lemma occurrences_bounds{L}:
    \forall unsigned int *d, integer k,v; 0 <= occurrences(d,k,v) <= (k <= 0 ? 0 : k);
  lemma occurrences_frame{A,B}:
    \forall unsigned int *d, integer k,v;
      (\forall integer i; 0 <= i < k ==> \at(d[i],A) == \at(d[i],B)) ==>
      occurrences{A}(d,k,v) == occurrences{B}(d,k,v);
  lemma collected_empty{L}:
    \forall unsigned int *t,*u, integer k,v;
      (\forall integer i; 0 <= i < k ==> u[i] == 0) ==> collected(t,u,k,v) == 0;
  lemma collected_full{L}:
    \forall unsigned int *t,*u, integer k,v;
      (\forall integer i; 0 <= i < k ==> u[i] != 0) ==> collected(t,u,k,v) == occurrences(t,k,v);
  lemma collected_update{A,B}:
    \forall unsigned int *t,*u, integer k,v,pos;
      (\forall integer i; 0 <= i < k && i != pos ==>
        \at(t[i],A) == \at(t[i],B) && \at(u[i],A) == \at(u[i],B)) ==>
      collected{B}(t,u,k,v) == collected{A}(t,u,k,v) + (0 <= pos < k ?
        ((\at(u[pos],B) != 0 && \at(t[pos],B) == v ? 1 : 0) -
         (\at(u[pos],A) != 0 && \at(t[pos],A) == v ? 1 : 0)) : 0);

  lemma collected_insert{A,B}:
    \forall unsigned int *t,*u, integer k,v,pos;
      \at(u[pos],A) == 0 && \at(u[pos],B) != 0 &&
      (\forall integer i; 0 <= i < k && i != pos ==>
        \at(t[i],A) == \at(t[i],B) && \at(u[i],A) == \at(u[i],B)) ==>
      collected{B}(t,u,k,v) == collected{A}(t,u,k,v) +
        (0 <= pos < k && \at(t[pos],B) == v ? 1 : 0);
  lemma available_update{A,B}:
    \forall unsigned int *t,*u, integer k,v,pos;
      (\forall integer i; 0 <= i < k && i != pos ==>
        \at(t[i],A) == \at(t[i],B) && \at(u[i],A) == \at(u[i],B)) ==>
      available{B}(t,u,k,v) == available{A}(t,u,k,v) + (0 <= pos < k ?
        ((\at(u[pos],B) == 0 && \at(t[pos],B) == v ? 1 : 0) -
         (\at(u[pos],A) == 0 && \at(t[pos],A) == v ? 1 : 0)) : 0);
  lemma available_empty{L}:
    \forall unsigned int *t,*u, integer k,v;
      (\forall integer i; 0 <= i < k ==> u[i] != 0 || t[i] != v) ==> available(t,u,k,v) == 0;
  lemma pending_bounds{L}:
    \forall unsigned int *d,*t, integer k,s,v; 0 <= s ==> 0 <= pending(d,t,k,s,v);
  lemma pending_shift{L}:
    \forall unsigned int *d,*t, integer k,s,v; 0 <= s ==>
      pending(d,t,k,s,v) == pending(d,t,k,s+1,v) +
        (0 <= s < k && d[s] != t[s] && d[s] == v ? 1 : 0);
  lemma pending_frame{A,B}:
    \forall unsigned int *d,*t, integer k,s,v; 0 <= s &&
      (\forall integer i; 0 <= i < k ==> \at(d[i],A) == \at(d[i],B) && \at(t[i],A) == \at(t[i],B)) ==>
      pending{A}(d,t,k,s,v) == pending{B}(d,t,k,s,v);
  lemma matching_initial{L}:
    \forall unsigned int *d,*t,*u, integer k,v;
      (\forall integer i; 0 <= i < k ==> (u[i] != 0 <==> d[i] == t[i])) ==>
      pending(d,t,k,0,v) - available(t,u,k,v) == occurrences(d,k,v) - occurrences(t,k,v);
} */
/*@
 strategy CountSMT: \prover("Z3", "CVC5", 3.0);
 strategy CountUnfold4:
   \tactic("Wp.unfold", \when(0 < K), \ingoal(T: L_occurrences(_,_,K,_)), \select(T), \children(CountSMT)),
   \tactic("Wp.unfold", \when(0 < K), \ingoal(T: L_collected(_,_,_,K,_)), \select(T), \children(CountSMT)),
   \tactic("Wp.unfold", \when(0 < K), \ingoal(T: L_available(_,_,_,K,_)), \select(T), \children(CountSMT)),
   \tactic("Wp.unfold", \when(0 < K), \ingoal(T: L_pending(_,_,_,K,_,_)), \select(T), \children(CountSMT)), CountSMT;
 strategy CountUnfold3:
   \tactic("Wp.unfold", \when(0 < K), \ingoal(T: L_occurrences(_,_,K,_)), \select(T), \children(CountUnfold4)),
   \tactic("Wp.unfold", \when(0 < K), \ingoal(T: L_collected(_,_,_,K,_)), \select(T), \children(CountUnfold4)),
   \tactic("Wp.unfold", \when(0 < K), \ingoal(T: L_available(_,_,_,K,_)), \select(T), \children(CountUnfold4)),
   \tactic("Wp.unfold", \when(0 < K), \ingoal(T: L_pending(_,_,_,K,_,_)), \select(T), \children(CountUnfold4)), CountSMT;
 strategy CountUnfold2:
   \tactic("Wp.unfold", \when(0 < K), \ingoal(T: L_occurrences(_,_,K,_)), \select(T), \children(CountUnfold3)),
   \tactic("Wp.unfold", \when(0 < K), \ingoal(T: L_collected(_,_,_,K,_)), \select(T), \children(CountUnfold3)),
   \tactic("Wp.unfold", \when(0 < K), \ingoal(T: L_available(_,_,_,K,_)), \select(T), \children(CountUnfold3)),
   \tactic("Wp.unfold", \when(0 < K), \ingoal(T: L_pending(_,_,_,K,_,_)), \select(T), \children(CountUnfold3)), CountSMT;
 strategy CountUnfold:
   \tactic("Wp.unfold", \when(0 < K), \ingoal(T: L_occurrences(_,_,K,_)), \select(T), \children(CountUnfold2)),
   \tactic("Wp.unfold", \when(0 < K), \ingoal(T: L_collected(_,_,_,K,_)), \select(T), \children(CountUnfold2)),
   \tactic("Wp.unfold", \when(0 < K), \ingoal(T: L_available(_,_,_,K,_)), \select(T), \children(CountUnfold2)),
   \tactic("Wp.unfold", \when(0 < K), \ingoal(T: L_pending(_,_,_,K,_,_)), \select(T), \children(CountUnfold2)), CountSMT;
 strategy CountPoint:
   \tactic("Wp.instance", \when(0 < N), \when(H: \forall integer j; _),
     \select(H), \param("P1",N-1), \children(CountUnfold)), CountUnfold;
 strategy CountPremise:
   \tactic("Wp.cut", \when(H: (P: (\forall integer j; _)) ==> _),
     \select(H), \param("case","MODUS"), \param("clause",P), \children(CountPoint),
     \child("Clause",CountSMT)), CountPoint;
 strategy CountPrevious:
   \tactic("Wp.instance", \when(H: \forall integer i; 0 <= i ==> i < N ==> ((\forall integer j; _) ==> _)),
     \select(H), \param("P1",N-1), \children(CountPremise)), CountUnfold;
 strategy OccInduct:
   \tactic("Wp.induction", \ingoal(L_occurrences(_,_,K,_)), \select(K),
     \param("base",0), \children(CountSMT), \child("Induction (sup)",CountPrevious));
 strategy CollectedInduct:
   \tactic("Wp.induction", \ingoal(L_collected(_,_,_,K,_)), \select(K),
     \param("base",0), \children(CountSMT), \child("Induction (sup)",CountPrevious));
 strategy AvailableInduct:
   \tactic("Wp.induction", \ingoal(L_available(_,_,_,K,_)), \select(K),
     \param("base",0), \children(CountSMT), \child("Induction (sup)",CountPrevious));
 strategy PendingInduct:
   \tactic("Wp.induction", \ingoal(L_pending(_,_,_,K,_,_)), \select(K),
     \param("base",0), \children(CountSMT), \child("Induction (sup)",CountPrevious));
 proof OccInduct: occurrences_bounds,occurrences_frame;
 proof CollectedInduct: collected_empty,collected_full,collected_update,collected_insert;
 proof AvailableInduct: available_update,available_empty;
 proof PendingInduct: pending_bounds,pending_shift,pending_frame,matching_initial;
*/

/*@ axiomatic PermuteRank {
logic integer moved{L}(unsigned int *p, integer k) =
    k <= 0 ? 0 : moved(p,k-1) + (p[k-1] != k-1 ? 1 : 0);

lemma moved_bounds_all{L}:
    \forall unsigned int *p, integer k;
      0 <= moved(p,k) <= (k <= 0 ? 0 : k);

  check lemma moved_frame_all{A,B}:
    \forall unsigned int *p, integer k;
      (\forall integer i; 0 <= i < k ==> \at(p[i],A) == \at(p[i],B)) ==>
      moved{A}(p,k) == moved{B}(p,k);

  check lemma moved_update_all{A,B}:
    \forall unsigned int *p, integer k,j;
      (\forall integer i; 0 <= i < k && i != j ==> \at(p[i],A) == \at(p[i],B)) ==>
      moved{B}(p,k) == moved{A}(p,k) +
        (0 <= j < k ? ((\at(p[j],B) != j ? 1 : 0) - (\at(p[j],A) != j ? 1 : 0)) : 0);

  check lemma moved_bounds{L}:
    \forall unsigned int *p, integer k;
      0 <= k ==> 0 <= moved(p,k) <= k;

  lemma moved_frame{A,B}:
    \forall unsigned int *p, integer k;
      0 <= k && (\forall integer i; 0 <= i < k ==> \at(p[i],A) == \at(p[i],B)) ==>
      moved{A}(p,k) == moved{B}(p,k);

  check lemma moved_update{A,B}:
    \forall unsigned int *p, integer k,j;
      0 <= k && (\forall integer i; 0 <= i < k && i != j ==> \at(p[i],A) == \at(p[i],B)) ==>
      moved{B}(p,k) == moved{A}(p,k) +
        (0 <= j < k ? ((\at(p[j],B) != j ? 1 : 0) - (\at(p[j],A) != j ? 1 : 0)) : 0);

lemma moved_exchange_count{A,B}:
   \forall unsigned int *p, integer top,pos;
     0 <= pos < top && \at(p[pos],A) != pos &&
     (\at(p[top],A) != top ==> pos == \at(p[top],A)) &&
     \at(p[pos],B) == \at(p[top],A) &&
     (\forall integer i; 0 <= i < top && i != pos ==> \at(p[i],A) == \at(p[i],B)) ==>
     moved{B}(p,top) == moved{A}(p,top) - (\at(p[top],A) == top ? 0 : 1);
} */

/*@ axiomatic PermuteInjective {
predicate injective{L}(unsigned int *p, integer n) =
    \forall integer i,j; 0 <= i < n && 0 <= j < n && p[i] == p[j] ==> i == j;
  lemma injective_swap{A,B}:
    \forall unsigned int *p, integer n,a,b;
      0 <= a < n && 0 <= b < n && a != b && injective{A}(p,n) &&
      \at(p[a],B) == \at(p[b],A) && \at(p[b],B) == \at(p[a],A) &&
      (\forall integer i; 0 <= i < n && i != a && i != b ==> \at(p[i],A) == \at(p[i],B)) ==>
      injective{B}(p,n);
} */

/*@ axiomatic PermuteSelectedInjective {
predicate selected_injective{L}(unsigned int *d, unsigned int *t, unsigned int *p, integer n,integer k) =
   \forall integer i,j; 0 <= i < n && 0 <= j < n && (i < k || d[i] == t[i]) &&
     (j < k || d[j] == t[j]) && p[i] == p[j] ==> i == j;

lemma selected_injective_step{A,B}:
   \forall unsigned int *d,*t,*p, integer n,k,dest;
     0 <= k < n && \at(d[k],A) != \at(t[k],A) && selected_injective{A}(d,t,p,n,k) &&
     (\forall integer i; 0 <= i < n && (i < k || \at(d[i],A) == \at(t[i],A)) ==> \at(p[i],A) != dest) &&
     (\forall integer i; 0 <= i < n ==> \at(d[i],A) == \at(d[i],B) && \at(t[i],A) == \at(t[i],B)) &&
     \at(p[k],B) == dest &&
     (\forall integer i; 0 <= i < n && i != k ==> \at(p[i],A) == \at(p[i],B)) ==>
     selected_injective{B}(d,t,p,n,k+1);
} */
/*@ axiomatic PermuteSelectedMarked {
predicate selected_marked{L}(unsigned int *d, unsigned int *t, unsigned int *p, unsigned int *u, integer n,integer k) =
   \forall integer i; 0 <= i < n && (i < k || d[i] == t[i]) ==> 0 <= p[i] < n && u[p[i]] != 0;

lemma selected_marked_step{A,B}:
   \forall unsigned int *d,*t,*p,*u, integer n,k,dest;
     0 <= k < n && 0 <= dest < n && \at(d[k],A) != \at(t[k],A) && selected_marked{A}(d,t,p,u,n,k) &&
     (\forall integer i; 0 <= i < n ==> \at(d[i],A) == \at(d[i],B) && \at(t[i],A) == \at(t[i],B)) &&
     \at(p[k],B) == dest && \at(u[dest],B) != 0 &&
     (\forall integer i; 0 <= i < n && i != k ==> \at(p[i],A) == \at(p[i],B)) &&
     (\forall integer i; 0 <= i < n && i != dest ==> \at(u[i],A) == \at(u[i],B)) ==>
     selected_marked{B}(d,t,p,u,n,k+1);
} */

/*@
  strategy RankSMT: \prover("CVC5", "Z3", 3.0);
  strategy RankUnfoldSecond:
    \tactic("Wp.unfold", \when(0 < N), \ingoal(T: L_moved(_,_,N)),
      \select(T), \children(RankSMT)), RankSMT;
  strategy RankUnfoldFirst:
    \tactic("Wp.unfold", \when(0 < N), \ingoal(T: L_moved(_,_,N)),
      \select(T), \children(RankUnfoldSecond)), RankSMT;
  strategy RankPoint:
    \tactic("Wp.instance", \when(0 < N), \when(H: \forall integer j; _),
      \select(H), \param("P1",N-1), \children(RankUnfoldFirst)), RankUnfoldFirst;
  strategy RankFramePremise:
    \tactic("Wp.cut", \when(H: (P: (\forall integer j; _)) ==> _),
      \select(H), \param("case","MODUS"), \param("clause",P), \children(RankPoint),
      \child("Clause",RankSMT)), RankPoint;
  strategy RankPrevious:
    \tactic("Wp.instance",
      \when(H: \forall integer i; 0 <= i ==> i < N ==> ((\forall integer j; _) ==> _)),
      \select(H), \param("P1",N-1), \children(RankFramePremise)), RankSMT;
  strategy RankInduct:
    \tactic("Wp.induction", \ingoal(L_moved(_,_,K)), \select(K),
      \param("base",0), \children(RankSMT), \child("Induction (sup)",RankPrevious));
  proof RankInduct: moved_bounds_all, moved_frame_all, moved_update_all;
  strategy RankUpdateCorollary:
    \tactic("Wp.lemma", \goal(L_moved(A,P,K) + _ == L_moved(B,P,K)),
      \ingoal(shift_uint32(P,J)), \select(0),
      \param("lemma","moved_update_all"), \param("P1",B), \param("P2",A),
      \param("P3",P), \param("P4",K), \param("P5",J), \children(RankSMT));

  strategy RankFrameCorollary:
    \tactic("Wp.lemma", \goal(L_moved(A,P,K) == L_moved(B,P,K)), \select(0),
      \param("lemma","moved_frame_all"), \param("P1",A), \param("P2",B),
      \param("P3",P), \param("P4",K), \children(RankSMT));
  proof RankSMT: moved_bounds;
  proof RankFrameCorollary: moved_frame;
  proof RankUpdateCorollary: moved_update;
*/

/*@
 strategy RankExchangeCount:
   \tactic("Wp.lemma", \goal(L_moved(A,P,K) + _ == L_moved(B,P,K)),
     \when(0 <= J), \when(J < K),
     \select(0), \param("lemma","moved_update_all"),
     \param("P1",B), \param("P2",A), \param("P3",P), \param("P4",K), \param("P5",J),
     \children(RankSMT));
 proof RankExchangeCount: moved_exchange_count;
*/

/*@
strategy InjectivePre:
  \tactic("Wp.unfold", \when(H: P_injective(_,_,_)), \select(H), \children(ProofSMT));
strategy InjectivePost:
  \tactic("Wp.unfold", \goal(G: P_injective(_,_,_)), \select(G), \children(InjectivePre));
proof InjectivePost: injective_swap;
*/

/*@

 strategy SelectedPair:
   \tactic("Wp.instance", \goal(I == J), \when(H: \forall integer a,b; _),
     \select(H), \param("P1",I), \param("P2",J), \children(ProofSMT)), ProofSMT;
 strategy SelectedPre:
   \tactic("Wp.unfold", \when(H: P_selected_injective(_,_,_,_,_,_)), \select(H), \children(SelectedPair));
 strategy SelectedPost:
   \tactic("Wp.unfold", \goal(G: P_selected_injective(_,_,_,_,_,_)), \select(G), \children(SelectedPre));
 proof SelectedPost: selected_injective_step;
*/

/*@

 strategy MarkedPoint:
   \tactic("Wp.instance", \ingoal(_[shift_uint32(U,_[shift_uint32(P,I)])]),
     \when(H: \forall integer j; _), \select(H), \param("P1",I), \children(MarkedDataAt));
 strategy MarkedPre:
   \tactic("Wp.unfold", \when(H: P_selected_marked(_,_,_,_,_,_,_)), \select(H), \children(MarkedPoint));
 strategy MarkedIndex:
   \tactic("Wp.cut", \when(M[shift_uint32(D,K)] != M[shift_uint32(T,K)]),
     \ingoal(_[shift_uint32(U,_[shift_uint32(P,I)])]), \select(0),
     \param("case","CASES"), \param("clause",I == K), \children(MarkedPre)), MarkedPre;
 strategy MarkedPost:
   \tactic("Wp.unfold", \goal(G: P_selected_marked(_,_,_,_,_,_,_)), \select(G), \children(MarkedIndex));
 proof MarkedPost: selected_marked_step;
*/

/*@ strategy ProofSMT: \prover("Z3", "CVC5", 10.0); */
/*@
  proof InjectivePost: swap_injective;

*/
/*@
  strategy SwapFramePremise:
    \tactic("Wp.cut", \when(H: P ==> _),
      \select(H), \param("case","MODUS"), \param("clause",P), \children(ProofSMT)), ProofSMT;
  strategy SwapCount:
    \tactic("Wp.lemma",
      \ingoal(L_moved(B: A[shift_uint32(P,J)[_]][shift_uint32(P,K)[_]],P,K)),
      \select(0), \param("lemma","moved_exchange_count"),
      \param("P1",B), \param("P2",A), \param("P3",P), \param("P4",K), \param("P5",J),
      \children(SwapFramePremise)), SwapCountAliasRight;

  strategy SwapInjectiveAlias:
    \tactic("Wp.lemma", \goal(P_injective(B,P,N)),
      \when(B == A[shift_uint32(P,J)[_]][shift_uint32(P,K)[_]]),
      \select(0), \param("lemma","injective_swap"),
      \param("P1",B), \param("P2",A), \param("P3",P), \param("P4",N),
      \param("P5",J), \param("P6",K), \children(SwapFramePremise)), InjectivePost;
  strategy SwapInjective:
    \tactic("Wp.lemma",
      \goal(P_injective(B: A[shift_uint32(P,J)[_]][shift_uint32(P,K)[_]],P,N)),
      \select(0), \param("lemma","injective_swap"),
      \param("P1",B), \param("P2",A), \param("P3",P), \param("P4",N),
      \param("P5",J), \param("P6",K), \children(SwapFramePremise)), SwapInjectiveAlias;
  strategy StoredArrayRight:
    \tactic("Wp.array", \goal(_ == (T: _[_[_]][_])), \select(T), \children(ProofSMT)), ProofSMT;
  strategy StoredArray:
    \tactic("Wp.array", \goal((T: _[_[_]][_]) == _), \select(T), \children(StoredArrayRight)), StoredArrayRight;
  proof SwapCount: rank_change;
  proof SwapInjective: swap_post_injective;

  strategy RankFrameUse:
    \tactic("Wp.lemma", \goal(L_moved(A,P,K) == L_moved(B,P,K)), \select(0),
      \param("lemma","moved_frame"), \param("P1",A), \param("P2",B),
      \param("P3",P), \param("P4",K), \children(SwapFramePremise));
  proof RankFrameUse: rank_frame;
  proof StoredArray: swap_prefix_frame;
*/

/*@

 strategy FillInjectiveAlias:
   \tactic("Wp.lemma", \goal(P_selected_injective(B,S,T,P,N,_)),
     \when(B == A[shift_uint32(P,K)[D]][shift_uint32(U,D)[_]]),
     \select(0), \param("lemma","selected_injective_step"),
     \param("P1",B), \param("P2",A), \param("P3",S), \param("P4",T), \param("P5",P),
     \param("P6",N), \param("P7",K), \param("P8",D), \children(SwapFramePremise)), SelectedPost;
 strategy FillInjective:
   \tactic("Wp.lemma", \goal(P_selected_injective(B: A[shift_uint32(P,K)[D]][shift_uint32(U,D)[_]],S,T,P,N,_)),
     \select(0), \param("lemma","selected_injective_step"),
     \param("P1",B), \param("P2",A), \param("P3",S), \param("P4",T), \param("P5",P),
     \param("P6",N), \param("P7",K), \param("P8",D), \children(SwapFramePremise)), FillInjectiveAlias;

 strategy FillMarkedAlias:
   \tactic("Wp.lemma", \goal(P_selected_marked(B,S,T,P,U,N,_)),
     \when(B == A[shift_uint32(P,K)[D]][shift_uint32(U,D)[_]]),
     \select(0), \param("lemma","selected_marked_step"),
     \param("P1",B), \param("P2",A), \param("P3",S), \param("P4",T), \param("P5",P),
     \param("P6",U), \param("P7",N), \param("P8",K), \param("P9",D), \children(SwapFramePremise)), MarkedPost;
 strategy FillMarked:
   \tactic("Wp.lemma", \goal(P_selected_marked(B: A[shift_uint32(P,K)[D]][shift_uint32(U,D)[_]],S,T,P,U,N,_)),
     \select(0), \param("lemma","selected_marked_step"),
     \param("P1",B), \param("P2",A), \param("P3",S), \param("P4",T), \param("P5",P),
     \param("P6",U), \param("P7",N), \param("P8",K), \param("P9",D), \children(SwapFramePremise)), FillMarkedAlias;
 proof FillInjective: fill_post_injective;
 proof FillMarked: fill_post_marked;
 proof MarkedPre: fill_fresh;
 proof StoredArray: fill_data_frame,fill_target_frame,fill_perm_frame,fill_used_frame,fill_mark;
*/
/*@
 strategy MarkedUsedAt:
   \tactic("Wp.instance", \ingoal(_[shift_uint32(U,V: _[shift_uint32(P,I)])]),
     \when(H: \forall integer j; _ ==> _[shift_uint32(U,j)] == _[shift_uint32(U,j)]),
     \select(H), \param("P1",V), \children(ProofSMT)), ProofSMT;
 strategy MarkedPermutationAt:
   \tactic("Wp.instance", \ingoal(_[shift_uint32(U,_[shift_uint32(P,I)])]),
     \when(H: \forall integer j; _ ==> _[shift_uint32(P,j)] == _[shift_uint32(P,j)]),
     \select(H), \param("P1",I), \children(MarkedUsedAt)), MarkedUsedAt;
 strategy MarkedDataAt:
   \tactic("Wp.instance", \ingoal(_[shift_uint32(U,_[shift_uint32(P,I)])]),
     \when(H: \forall integer j; _ ==> (_[shift_uint32(D,j)] == _[shift_uint32(D,j)] && _[shift_uint32(T,j)] == _[shift_uint32(T,j)])),
     \select(H), \param("P1",I), \children(MarkedPermutationAt)), MarkedPermutationAt;
*/

/*@ proof SelectedPost: fill_pre_injective;
  */

/*@
 strategy PreMarkedUsed:
   \tactic("Wp.instance", \ingoal(M[shift_uint32(U,M[shift_uint32(P,I)])]),
     \when(H: \forall integer j; _ ==> M[shift_uint32(U,M[shift_uint32(P,j)])] != 0),
     \select(H), \param("P1",I), \children(ProofSMT)), ProofSMT;
 strategy PreMarkedBound:
   \tactic("Wp.instance", \ingoal(M[shift_uint32(U,M[shift_uint32(P,I)])]),
     \when(H: \forall integer j; 0 <= j ==> j < N ==> M[shift_uint32(P,j)] < N),
     \select(H), \param("P1",I), \children(PreMarkedUsed)), PreMarkedUsed;
 strategy PreMarked:
   \tactic("Wp.unfold", \goal(G: P_selected_marked(_,_,_,_,_,_,_)), \select(G), \children(PreMarkedBound));
 strategy SwapCountAliasLeft:
   \tactic("Wp.lemma",
     \when(A[shift_uint32(P,J)[_]][shift_uint32(P,K)[_]] == B),
     \ingoal(L_moved(B,P,K)),
     \select(0), \param("lemma","moved_exchange_count"),
     \param("P1",B), \param("P2",A), \param("P3",P), \param("P4",K), \param("P5",J),
     \children(SwapFramePremise)), ProofSMT;
 strategy SwapCountAliasRight:
   \tactic("Wp.lemma",
     \when(B == A[shift_uint32(P,J)[_]][shift_uint32(P,K)[_]]),
     \ingoal(L_moved(B,P,K)),
     \select(0), \param("lemma","moved_exchange_count"),
     \param("P1",B), \param("P2",A), \param("P3",P), \param("P4",K), \param("P5",J),
     \children(SwapFramePremise)), SwapCountAliasLeft;
 proof PreMarked: fill_pre_marked;
*/

/*@
 strategy TraceAssign:
   \tactic("Wp.valid", \ingoal(T: included(shift_uint32(P,I),1,shift_uint32(P,0),N)),
     \select(T), \children(ProofSMT)), ProofSMT;
 proof TraceAssign: "@assigns";
*/


/*@ axiomatic MatchingFrames {
  lemma injective_frame{A,B}:
    \forall unsigned int *p, integer n;
      injective{A}(p,n) &&
      (\forall integer i; 0 <= i < n ==> \at(p[i],A) == \at(p[i],B)) ==>
      injective{B}(p,n);
} */
/*@ proof InjectivePost: injective_frame; */

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
  requires permutation_input: ((\forall integer i; 0 <= i < v1 ==> 0 <= v3[i] < v1) &&
        (\forall integer i,j; 0 <= i < v1 && 0 <= j < v1 && v3[i] == v3[j] ==> i == j) &&
        (\forall integer j; 0 <= j < v1 ==> \exists integer i; 0 <= i < v1 && v3[i] == j));
  terminates \true;
  ensures status: 0 <= \result <= 1;
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
  /*@ loop invariant data_unchanged: \forall integer j; 0 <= j < v1 ==> v2[j] == \at(v2[j],Pre);
      loop invariant out_clear: v7[0] == 0 && v7[1] == 0 && v7[2] == 0;
       loop invariant original_permutation:
        \forall integer j; 0 <= j < v1 ==> v3[j] == \at(v3[j],Pre);
      loop invariant bounds: 0 <= v8 <= v1;
      loop invariant clear: \forall integer j; 0 <= j < v8 ==> v5[j] == 0;
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
  /*@ loop invariant data_unchanged: \forall integer j; 0 <= j < v1 ==> v2[j] == \at(v2[j],Pre);
      loop invariant out_clear: v7[0] == 0 && v7[1] == 0 && v7[2] == 0;

      loop invariant marks: \forall integer j; 0 <= j < v1 ==>
        (v5[j] != 0 <==> (\exists integer i; 0 <= i < v8 && \at(v3[i],Pre) == j));
      loop invariant filled: \forall integer i; 0 <= i < v8 ==>
        v4[\at(v3[i],Pre)] == \at(v2[i],Pre);
      loop invariant collected: \forall integer value;
        collected(v4,v5,v1,value) == occurrences{Pre}(v2,v8,value);
       loop invariant original_permutation:
        \forall integer j; 0 <= j < v1 ==> v3[j] == \at(v3[j],Pre);
      loop invariant bounds: 0 <= v8 <= v1;
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
    /*@ assert collect_unused: v5[v9] == 0; */
    /*@ ghost target_step: ; */
    v5[v9] = 1U;
    v4[v9] = v2[v8];
    /*@ assert collect_target_frame: \forall integer i; 0 <= i < v1 && i != v9 ==>
      v4[i] == \at(v4[i],target_step); */
    /*@ assert collect_used_frame: \forall integer i; 0 <= i < v1 && i != v9 ==>
      v5[i] == \at(v5[i],target_step); */
    /*@ assert collect_value: v4[v9] == \at(v2[\at(v8,Here)],Pre) && v5[v9] != 0; */
    /*@ assert collected_changed: \forall integer value;
      collected(v4,v5,v1,value) == collected{target_step}(v4,v5,v1,value) +
        (\at(v2[\at(v8,Here)],Pre) == value ? 1 : 0); */
    v8 = (v8 + 1U);
  }
  v8 = 0U;
  /*@ assert target_all_used: \forall integer j; 0 <= j < v1 ==> v5[j] != 0; */
  /*@ ghost target_ready: ; */
  /*@ assert target_multiset: \forall integer value;
    occurrences{Pre}(v2,v1,value) == occurrences{target_ready}(v4,v1,value); */
  /*@ loop invariant data_unchanged: \forall integer j; 0 <= j < v1 ==> v2[j] == \at(v2[j],Pre);
      loop invariant out_clear: v7[0] == 0 && v7[1] == 0 && v7[2] == 0;

      loop invariant target_static: \forall integer j; 0 <= j < v1 ==> v4[j] == \at(v4[j],target_ready);
       loop invariant bounds: 0 <= v8 <= v1;
      loop invariant permutation_bounds: \forall integer j; 0 <= j < v1 ==> 0 <= v3[j] < v1;
      loop invariant processed: \forall integer j; 0 <= j < v8 ==>
        (v5[j] == 1 && v3[j] == j && v2[j] == v4[j]) || (v5[j] == 0 && v2[j] != v4[j]);
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
  /*@ ghost normal_start: ; */
  /*@ assert normal_mask: \forall integer j; 0 <= j < v1 ==> (v5[j] != 0 <==> v2[j] == v4[j]); */
  /*@ assert normal_data_count: \forall integer value;
    occurrences(v2,v1,value) == occurrences{Pre}(v2,v1,value); */
  /*@ assert normal_target_count: \forall integer value;
    occurrences(v4,v1,value) == occurrences{target_ready}(v4,v1,value); */
  /*@ assert normal_multiset: \forall integer value;
    occurrences(v2,v1,value) == occurrences(v4,v1,value); */
  /*@ assert normal_matching: \forall integer value;
    pending(v2,v4,v1,0,value) == available(v4,v5,v1,value); */
  /*@ loop invariant data_unchanged: \forall integer j; 0 <= j < v1 ==> v2[j] == \at(v2[j],Pre);
      loop invariant out_clear: v7[0] == 0 && v7[1] == 0 && v7[2] == 0;

      loop invariant normal_data: \forall integer j; 0 <= j < v1 ==> v2[j] == \at(v2[j],normal_start);
      loop invariant normal_target: \forall integer j; 0 <= j < v1 ==> v4[j] == \at(v4[j],normal_start);
      loop invariant matched: \forall integer j; 0 <= j < v8 ==>
        \at(v2[j],normal_start) == \at(v4[\at(v3[j],Here)],normal_start);
      loop invariant matching_count: \forall integer value;
        pending{normal_start}(v2,v4,v1,v8,value) == available(v4,v5,v1,value);
       loop invariant bounds: 0 <= v8 <= v1;
      loop invariant permutation_bounds: \forall integer j; 0 <= j < v1 ==> 0 <= v3[j] < v1;
      loop invariant fixed: \forall integer j; 0 <= j < v1 && v2[j] == v4[j] ==> v3[j] == j && v5[j] == 1;
      loop invariant selected_marked: \forall integer i; 0 <= i < v1 &&
        (i < v8 || v2[i] == v4[i]) ==> v5[v3[i]] != 0;
      loop invariant injective_selected: \forall integer i,j;
        0 <= i < v1 && 0 <= j < v1 && (i < v8 || v2[i] == v4[i]) &&
        (j < v8 || v2[j] == v4[j]) && v3[i] == v3[j] ==> i == j;
      loop assigns v8, v9, v3[0 .. v1-1], v5[0 .. v1-1];
      loop variant v1-v8;
  */
while (1) {
    if (v8 < v1) {
    } else {
      break;
    }
    /*@ assert pending_same: v2[v8] == v4[v8] ==> (\forall integer value;
      pending{normal_start}(v2,v4,v1,v8+1,value) == pending{normal_start}(v2,v4,v1,v8,value)); */
    if (v2[v8] != v4[v8]) {
      /*@ assert pending_current: 0 < pending{normal_start}(v2,v4,v1,v8,v2[v8]); */
      /*@ assert available_current: 0 < available(v4,v5,v1,v2[v8]); */
      /*@ assert pending_next: \forall integer value;
        pending{normal_start}(v2,v4,v1,v8+1,value) == pending{normal_start}(v2,v4,v1,v8,value) -
          (v2[v8] == value ? 1 : 0); */
      v9 = 0U;
      /*@
      loop invariant absent: \forall integer j; 0 <= j < v9 ==> v5[j] != 0 || v2[v8] != v4[j];
       loop invariant bounds: 0 <= v9 <= v1;
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
      /*@ assert search_exists: v9 < v1; */
      /*@ assert fill_value: v4[v9] == v2[v8]; */
      if (v9 == v1) {
        return 2U;
      } else {
      }
      /*@ assert fill_unused: v5[v9] == 0; */
      /*@ assert fill_fresh: \forall integer i; 0 <= i < v1 &&
        (i < v8 || v2[i] == v4[i]) ==> v3[i] != v9; */
      /*@ assert fill_pre_injective: selected_injective(v2,v4,v3,v1,v8); */
      /*@ assert fill_pre_marked: selected_marked(v2,v4,v3,v5,v1,v8); */
      /*@ assert fill_addresses: v3+v8 != v5+v9; */
      /*@ ghost proof_fill: ; */
      v3[v8] = v9;
      v5[v9] = 1U;
      /*@ assert fill_data_frame: \forall integer i; 0 <= i < v1 ==> v2[i] == \at(v2[i],proof_fill); */
      /*@ assert fill_target_frame: \forall integer i; 0 <= i < v1 ==> v4[i] == \at(v4[i],proof_fill); */
      /*@ assert fill_perm_frame: \forall integer i; 0 <= i < v1 && i != v8 ==> v3[i] == \at(v3[i],proof_fill); */
      /*@ assert fill_used_frame: \forall integer i; 0 <= i < v1 && i != v9 ==> v5[i] == \at(v5[i],proof_fill); */
      /*@ assert fill_destination: v3[v8] == v9; */
      /*@ assert fill_mark: v5[v9] != 0; */
      /*@ assert fill_matched_value: v2[v8] == v4[v3[v8]]; */
      /*@ assert fill_matched_snapshot:
        \at(v2[\at(v8,Here)],normal_start) == \at(v4[\at(v3[v8],Here)],normal_start); */
      /*@ assert fill_post_injective: selected_injective(v2,v4,v3,v1,v8+1); */
      /*@ assert available_changed: \forall integer value;
        available(v4,v5,v1,value) == available{proof_fill}(v4,v5,v1,value) -
          (\at(v2[v8],proof_fill) == value ? 1 : 0); */
      /*@ assert matching_after: \forall integer value;
        pending{normal_start}(v2,v4,v1,v8+1,value) == available(v4,v5,v1,value); */
      /*@ assert fill_post_marked: selected_marked(v2,v4,v3,v5,v1,v8+1); */

    } else {
    }
    v8 = (v8 + 1U);
  }
  /*@ assert ghost_initial_safe: 0 <= 2*v1 <= 2048; */
  /*@ ghost int proof_steps = 2*v1; */
  v10 = (v1 - 1U);
  /*@
      loop invariant count: 0 <= v7[0] <= 2*v1;
      loop invariant budget: v7[0] + 2*moved(v3,v10) + (v3[v10] == v10 ? 1 : 0) <= 2*v1-1;
       loop invariant rank_budget: 2*moved(v3,v10) + (v3[v10] == v10 ? 1 : 0) <= proof_steps;
      loop invariant steps: 0 <= proof_steps <= 2*v1;
      loop invariant top: v10 == v1-1;
      loop invariant permutation_bounds: \forall integer j; 0 <= j < v1 ==> 0 <= v3[j] < v1;
      loop invariant permutation_injective: injective(v3,v1);
      loop assigns proof_steps, v11, v12, v13, v2[0 .. v1-1], v3[0 .. v1-1], v6[0 .. 2*v1-1], v7[0 .. 2];
      loop variant proof_steps;
  */
while (1) {
    v11 = v3[v10];
    if (v11 == v10) {
      /*@  loop invariant bounds: 0 <= v11 <= v10;
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
    /*@ assert chosen_bounds: 0 <= v11 < v10; */
    /*@ assert chosen_not_fixed: v3[v11] != v11; */
    /*@ assert chosen_destination: v3[v10] != v10 ==> v11 == v3[v10]; */
    /*@ assert chosen_top: v3[v10] == v10 ==> v3[v11] != v10; */
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
      /*@ assert data_count_frame: v7[0] == \at(v7[0],LoopCurrent); */
      /*@ assert append_room: v7[0] < 2*v1; */
      v6[v7[0U]] = v13;
      v7[0U] = (v7[0U] + 1U);
    } else {
    }
    /*@ assert count_increment: v7[0] <= \at(v7[0],LoopCurrent) + 1; */
    /*@ assert permutation_before_bounds: \forall integer i; 0 <= i < v1 ==>
      v3[i] == \at(v3[i],LoopCurrent); */
    /*@ assert swap_permutation_bounds: \forall integer j; 0 <= j < v1 ==> 0 <= v3[j] < v1; */
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
    /*@ assert functional_budget_before: \at(v7[0],LoopCurrent) +
      2*moved(v3,v10) + (v3[v10] == v10 ? 1 : 0) <= 2*v1-1; */
    /*@ assert swap_value_bounds: 0 <= v3[v11] < v1 && 0 <= v3[v10] < v1; */
    /*@ ghost proof_swap: ; */
    v12 = v3[v11];
    v3[v11] = v3[v10];
    v3[v10] = v12;
    /*@ assert swap_prefix_frame: \forall integer i; 0 <= i < v10 && i != v11 ==>
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
    /*@ assert functional_count_frame: v7[0] == \at(v7[0],proof_swap); */
    /*@ assert functional_budget_after: v7[0] +
      2*moved(v3,v10) + (v3[v10] == v10 ? 1 : 0) <= 2*v1-1; */
    /*@ assert ghost_step_safe: 1 <= proof_steps <= 2048; */
    /*@ ghost proof_steps--; */

  }
}


/*@
 strategy TargetUsed:
   \tactic("Wp.instance", \goal(_[shift_uint32(_,J)] != 0),
     \when(H: \forall integer j; 0 <= j ==> j < N ==> (\exists integer k; _)),
     \select(H), \param("P1",J), \children(ProofSMT)), ProofSMT;
 proof TargetUsed: target_all_used;
 strategy CollectedUpdate:
   \tactic("Wp.lemma", \ingoal(L_collected(B: A[shift_uint32(U,J)[_]][shift_uint32(T,J)[_]],T,U,N,V)),
     \select(0), \param("lemma","collected_insert"),
     \param("P1",B), \param("P2",A), \param("P3",T), \param("P4",U),
     \param("P5",N), \param("P6",V), \param("P7",J), \children(SwapFramePremise)), ProofSMT;
 proof CollectedUpdate: collected_changed;
 strategy MatchingInitial:
   \tactic("Wp.lemma", \ingoal(L_pending(M,D,T,N,0,V)), \ingoal(L_available(M,T,U,N,V)),
     \select(0), \param("lemma","matching_initial"),
     \param("P1",M), \param("P2",D), \param("P3",T), \param("P4",U),
     \param("P5",N), \param("P6",V), \children(SwapFramePremise)), ProofSMT;
 proof MatchingInitial: normal_matching;
 strategy AvailableUpdateAliasLeft:
   \tactic("Wp.lemma", \ingoal(L_available(B,T,U,N,V)),
     \when(A[shift_uint32(P,K)[J]][shift_uint32(U,J)[_]] == B),
     \select(0), \param("lemma","available_update"),
     \param("P1",B), \param("P2",A), \param("P3",T), \param("P4",U),
     \param("P5",N), \param("P6",V), \param("P7",J), \children(SwapFramePremise)), ProofSMT;
 strategy AvailableUpdateAlias:
   \tactic("Wp.lemma", \ingoal(L_available(B,T,U,N,V)),
     \when(B == A[shift_uint32(P,K)[J]][shift_uint32(U,J)[_]]),
     \select(0), \param("lemma","available_update"),
     \param("P1",B), \param("P2",A), \param("P3",T), \param("P4",U),
     \param("P5",N), \param("P6",V), \param("P7",J), \children(SwapFramePremise)), AvailableUpdateAliasLeft;
 strategy AvailableUpdate:
   \tactic("Wp.lemma", \ingoal(L_available(B: A[shift_uint32(P,K)[J]][shift_uint32(U,J)[_]],T,U,N,V)),
     \select(0), \param("lemma","available_update"),
     \param("P1",B), \param("P2",A), \param("P3",T), \param("P4",U),
     \param("P5",N), \param("P6",V), \param("P7",J), \children(SwapFramePremise)), AvailableUpdateAlias;
 proof AvailableUpdate: available_changed;
*/

/*@ proof StoredArray: functional_count_frame; */

/*@
 strategy ZeroIndex:
   \tactic("Wp.cut", \when(V <= 0), \when(0 <= V), \select(0),
     \param("case","MODUS"), \param("clause",V == 0), \children(ProofSMT)), ProofSMT;
 proof ZeroIndex: functional_budget_after;
*/

/*@ proof ZeroIndex: permutation_bounds, injective_selected; */

/*@
 strategy SelectedCurrentPair:
   \tactic("Wp.instance", \goal(I == J),
     \when(M[shift_uint32(P,I)] == M[shift_uint32(P,J)]),
     \when(H: \forall integer a,b; M[shift_uint32(P,a)] == M[shift_uint32(P,b)] ==> _),
     \select(H), \param("P1",I), \param("P2",J), \children(ProofSMT)), ProofSMT;
 proof SelectedCurrentPair: injective_selected;
 strategy UseInjectiveFrame:
   \tactic("Wp.lemma", \goal(P_injective(B,P,N)),
     \when(\forall integer j; _ ==> B[shift_uint32(P,j)] == A[shift_uint32(P,j)]),
     \select(0), \param("lemma","injective_frame"),
     \param("P1",B), \param("P2",A), \param("P3",P), \param("P4",N),
     \children(SwapFramePremise)), InjectivePost;
 proof UseInjectiveFrame: swap_injective;
 strategy ZeroAssign:
   \tactic("Wp.cut", \when(V <= 0), \when(0 <= V), \select(0),
     \param("case","MODUS"), \param("clause",V == 0),
     \children(TraceAssign), \child("Clause",ProofSMT)), TraceAssign;
 proof ZeroAssign: "@assigns";
*/

/*@
 strategy BoundsPoint:
   \tactic("Wp.instance", \ingoal(M[shift_uint32(P,I)]),
     \when(H: \forall integer j; 0 <= j ==> j < N ==>
       (0 <= M[shift_uint32(P,j)] && M[shift_uint32(P,j)] < N)),
     \select(H), \param("P1",I), \children(ProofSMT)), ZeroIndex;
 proof BoundsPoint: permutation_bounds;
*/

/*@
 strategy BoundsPointUpper:
   \tactic("Wp.instance", \ingoal(M[shift_uint32(P,I)]),
     \when(H: \forall integer j; _ ==>
       (M[shift_uint32(P,j)] <= _ && 0 <= M[shift_uint32(P,j)])),
     \select(H), \param("P1",I), \children(ProofSMT)), BoundsPoint;
 proof BoundsPointUpper: permutation_bounds;
*/

/*@
 strategy StoredZero:
   \tactic("Wp.cut", \when(V <= 0), \when(0 <= V), \select(0),
     \param("case","MODUS"), \param("clause",V == 0), \children(StoredArray)), StoredArray;
 proof StoredZero: permutation_before_bounds,swap_full_frame,functional_count_frame;
 proof BoundsPointUpper: swap_permutation_bounds,swap_post_bounds;
*/

/*@
 strategy BoundsFrameReverse:
   \tactic("Wp.instance", \ingoal(B[shift_uint32(P,I)]),
     \when(H: \forall integer j; _ ==> A[shift_uint32(P,j)] == B[shift_uint32(P,j)]),
     \select(H), \param("P1",I), \children(ProofSMT)), BoundsPointUpper;
 strategy BoundsFrame:
   \tactic("Wp.instance", \ingoal(B[shift_uint32(P,I)]),
     \when(H: \forall integer j; _ ==> B[shift_uint32(P,j)] == A[shift_uint32(P,j)]),
     \select(H), \param("P1",I), \children(ProofSMT)), BoundsFrameReverse;
 proof BoundsFrame: swap_post_bounds;
*/

/*@
 strategy SelectedReversePair:
   \tactic("Wp.instance", \goal(I == J),
     \when(M[shift_uint32(P,I)] == M[shift_uint32(P,J)]),
     \when(H: \forall integer a,b; M[shift_uint32(P,b)] == M[shift_uint32(P,a)] ==> _),
     \select(H), \param("P1",I), \param("P2",J), \children(ProofSMT)), SelectedCurrentPair;
 strategy SelectedCurrentPredicate:
   \tactic("Wp.unfold", \goal(I == J),
     \when(M[shift_uint32(P,I)] == M[shift_uint32(P,J)]),
     \when(H: P_selected_injective(M,_,_,P,_,_)), \select(H),
     \children(SelectedReversePair)), SelectedReversePair;
 proof SelectedCurrentPredicate: injective_selected;
*/
