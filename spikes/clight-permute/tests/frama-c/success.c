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
/*@ axiomatic Reachability {
  predicate target_matches{L1,L2}(unsigned int *d, unsigned int *p,
                                  unsigned int *t, integer n) =
    \forall integer i; 0 <= i < n ==> \at(t[\at(p[i],L1)],L2) == \at(d[i],L1);

  predicate values_reachable{L}(unsigned int *d, unsigned int *p, integer n) =
    \forall integer i; 0 <= i < n && n - 1 - p[i] > 16 ==> d[p[i]] == d[i];


  predicate far_correct{Input,Target}(unsigned int *d, unsigned int *t, integer n) =
    \forall integer j; 0 <= j < n && n-1-j > 16 ==> \at(d[j],Input) == \at(t[j],Target);
  lemma reachability_forward{Input,Target}:
    \forall unsigned int *d,*p,*t, integer n;
      (\forall integer j; 0 <= j < n ==> \exists integer i; 0 <= i < n && \at(p[i],Input) == j) &&
      target_matches{Input,Target}(d,p,t,n) && values_reachable{Input}(d,p,n) ==>
      far_correct{Input,Target}(d,t,n);
  lemma reachability_backward{Input,Target}:
    \forall unsigned int *d,*p,*t, integer n;
      (\forall integer i; 0 <= i < n ==> 0 <= \at(p[i],Input) < n) &&
      target_matches{Input,Target}(d,p,t,n) && far_correct{Input,Target}(d,t,n) ==>
      values_reachable{Input}(d,p,n);
} */
/*@
 strategy ReachSMT: \prover("Z3", "CVC5", 5.0);
 strategy ReachCover:
   \tactic("Wp.instance", \ingoal(_[shift_uint32(_,J)]),
     \when(H: \forall integer j; 0 <= j ==> j < N ==> (\exists integer i; _)),
     \select(H), \param("P1",J), \children(ReachSMT)), ReachBackBound;
 strategy ReachTarget:
   \tactic("Wp.unfold", \when(H: P_target_matches(_,_,_,_,_,_)), \select(H), \children(ReachCover)), ReachCover;
 strategy ReachPre:
   \tactic("Wp.unfold", \when(H: P_values_reachable(_,_,_,_)), \select(H), \children(ReachTarget)),
   \tactic("Wp.unfold", \when(H: P_far_correct(_,_,_,_,_)), \select(H), \children(ReachTarget)), ReachTarget;
 strategy ReachPost:
   \tactic("Wp.unfold", \goal(G: P_far_correct(_,_,_,_,_)), \select(G), \children(ReachPre)),
   \tactic("Wp.unfold", \goal(G: P_values_reachable(_,_,_,_)), \select(G), \children(ReachPre));
 proof ReachPost: reachability_forward,reachability_backward;
*/

/*@
 strategy ReachBackTarget:
   \tactic("Wp.instance", \ingoal(M[shift_uint32(D,M[shift_uint32(P,I)])]),
     \when(H: \forall integer j; _ ==> _[shift_uint32(_,M[shift_uint32(P,j)])] == M[shift_uint32(D,j)]),
     \select(H), \param("P1",I), \children(ReachSMT)), ReachSMT;
 strategy ReachBackFar:
   \tactic("Wp.instance", \ingoal(M[shift_uint32(D,X: M[shift_uint32(P,I)])]),
     \when(H: \forall integer j; _ ==> _[shift_uint32(_,j)] == M[shift_uint32(D,j)]),
     \select(H), \param("P1",X), \children(ReachBackTarget)), ReachBackTarget;
 strategy ReachBackBound:
   \tactic("Wp.instance", \ingoal(M[shift_uint32(D,M[shift_uint32(P,I)])]),
     \when(H: \forall integer j; _ ==> (0 <= M[shift_uint32(P,j)] && M[shift_uint32(P,j)] < _)),
     \select(H), \param("P1",I), \children(ReachBackFar)), ReachBackFar;
*/



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
  proof StoredArray: swap_prefix_frame, permutation_frame;
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


/*@ axiomatic ValueExchange {
  predicate value_matched{Data,Target}(unsigned int *d,unsigned int *p,unsigned int *t,integer n) =
    \forall integer j; 0 <= j < n ==>
      \at(d[j],Data) == \at(t[\at(p[j],Data)],Target);
  predicate exchanged{A,B}(unsigned int *p,integer n,integer a,integer b) =
    \forall integer j; 0 <= j < n ==>
      \at(p[j],B) == \at(p[j == a ? b : j == b ? a : j],A);
  lemma values_exchange{A,B,T}:
    \forall unsigned int *d,*p,*t,integer n,a,b;
      0 <= a < n && 0 <= b < n &&
      value_matched{A,T}(d,p,t,n) &&
      exchanged{A,B}(d,n,a,b) && exchanged{A,B}(p,n,a,b) ==>
      value_matched{B,T}(d,p,t,n);
} */
/*@
 strategy ExchangePre:
   \tactic("Wp.unfold", \when(H: P_exchanged(_,_,_,_,_,_)), \select(H), \children(ExchangePre)),
   \tactic("Wp.unfold", \when(H: P_value_matched(_,_,_,_,_,_)), \select(H), \children(ProofSMT)), ProofSMT;
 strategy ExchangePost:
   \tactic("Wp.unfold", \goal(G: P_value_matched(_,_,_,_,_,_)), \select(G), \children(ExchangePre));
 proof ExchangePost: values_exchange;
*/

/*@ lemma guarded_success_iff{Input}:
    \forall unsigned int *d,*p, integer n,result;
      0 <= result <= 1 &&
      (result == 0 ==> values_reachable{Input}(d,p,n)) &&
      (result == 1 ==> !values_reachable{Input}(d,p,n)) ==>
      ((result == 0) <==> values_reachable{Input}(d,p,n));
*/
/*@ proof ProofSMT: guarded_success_iff; */

/*@ axiomatic DisjointCells {
  lemma separate_cells{L}:
    \forall unsigned int *p,*q, integer n,m,i,j;
      \separated(p+(0..n-1),q+(0..m-1)) && 0 <= i < n && 0 <= j < m ==>
      p+i != q+j;
} */
/*@
 strategy DisjointCells:
   \tactic("Wp.separated", \when(H: separated(_,_,_,_)), \select(H), \children(ProofSMT)), ProofSMT;
 proof ProofSMT: separate_cells;
*/

/*@ axiomatic BoundExchange {
  predicate array_bounded{L}(unsigned int *p,integer n) =
    \forall integer i; 0 <= i < n ==> 0 <= p[i] < n;
  lemma bounds_exchange{A,B}:
    \forall unsigned int *p,integer n,a,b;
      0 <= a < n && 0 <= b < n && array_bounded{A}(p,n) &&
      exchanged{A,B}(p,n,a,b) ==> array_bounded{B}(p,n);
} */
/*@
 strategy BoundExchangePre:
   \tactic("Wp.unfold", \when(H: P_exchanged(_,_,_,_,_,_)), \select(H), \children(BoundExchangePre)),
   \tactic("Wp.unfold", \when(H: P_array_bounded(_,_,_)), \select(H), \children(ProofSMT)), ProofSMT;
 strategy BoundExchangePost:
   \tactic("Wp.unfold", \goal(G: P_array_bounded(_,_,_)), \select(G), \children(BoundExchangePre));
 proof BoundExchangePost: bounds_exchange;
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
  requires permutation_input: ((\forall integer i; 0 <= i < v1 ==> 0 <= v3[i] < v1) &&
        (\forall integer i,j; 0 <= i < v1 && 0 <= j < v1 && v3[i] == v3[j] ==> i == j) &&
        (\forall integer j; 0 <= j < v1 ==> \exists integer i; 0 <= i < v1 && v3[i] == j));
  terminates \false;
  ensures success_reachable: \result == 0 ==> values_reachable{Pre}(v2,v3,v1);
  ensures blocked_unreachable: \result == 1 ==> !values_reachable{Pre}(v2,v3,v1);
  ensures success_data: \result == 0 ==> (\forall integer j; 0 <= j < v1 ==> v2[j] == v4[j]);
  ensures success_info: \result == 0 ==> v7[1] == 0 && v7[2] == 0;
  ensures blocked_info: \result == 1 ==> v7[1] < v1 && v1 - 1 - v7[1] > 16 &&
    v7[2] == v1 - 1 - v7[1] - 16 && v2[v7[1]] != v2[v1-1];
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

      loop invariant filled: \forall integer i; 0 <= i < v8 ==>
        v4[\at(v3[i],Pre)] == \at(v2[i],Pre);
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
    v5[v9] = 1U;
    v4[v9] = v2[v8];
    v8 = (v8 + 1U);
  }
  v8 = 0U;
  /*@ loop invariant data_unchanged: \forall integer j; 0 <= j < v1 ==> v2[j] == \at(v2[j],Pre);
      loop invariant out_clear: v7[0] == 0 && v7[1] == 0 && v7[2] == 0;

      loop invariant target_definition: \forall integer i; 0 <= i < v1 ==>
        v4[\at(v3[i],Pre)] == \at(v2[i],Pre);
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
  /*@ assert normal_target_relation: target_matches{Pre,normal_start}(v2,v3,v4,v1); */
  /*@ loop invariant data_unchanged: \forall integer j; 0 <= j < v1 ==> v2[j] == \at(v2[j],Pre);
      loop invariant out_clear: v7[0] == 0 && v7[1] == 0 && v7[2] == 0;

      loop invariant normal_data: \forall integer j; 0 <= j < v1 ==> v2[j] == \at(v2[j],normal_start);
      loop invariant normal_target: \forall integer j; 0 <= j < v1 ==> v4[j] == \at(v4[j],normal_start);
      loop invariant matched_prefix: \forall integer j; 0 <= j < v8 ==>
        \at(v2[j],normal_start) == \at(v4[\at(v3[j],Here)],normal_start);
       loop invariant bounds: 0 <= v8 <= v1;
      loop invariant permutation_bounds: \forall integer j; 0 <= j < v1 ==> 0 <= v3[j] < v1;
      loop invariant fixed: \forall integer j; 0 <= j < v1 && v2[j] == v4[j] ==> v3[j] == j && v5[j] == 1;
      loop invariant selected_marked: \forall integer i; 0 <= i < v1 &&
        (i < v8 || v2[i] == v4[i]) ==> v5[v3[i]] != 0;
      loop invariant injective_selected: selected_injective(v2,v4,v3,v1,v8);
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
      /*@  loop invariant bounds: 0 <= v9 <= v1;
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
      /*@ assert fill_value: v4[v9] == v2[v8]; */
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
      /*@ assert fill_post_marked: selected_marked(v2,v4,v3,v5,v1,v8+1); */

    } else {
    }
    v8 = (v8 + 1U);
  }


  v10 = (v1 - 1U);
  /*@
      loop invariant main_matched: \forall integer j; 0 <= j < v1 ==>
        v2[j] == \at(v4[\at(v3[j],Here)],normal_start);
      loop invariant initially_fixed: \forall integer j; 0 <= j < v10 &&
        \at(v2[j],Pre) == \at(v4[j],normal_start) ==> v3[j] == j;
      loop invariant far_values: \forall integer j; 0 <= j < v1 && v1-1-j > 16 ==>
        v2[j] == \at(v2[j],Pre);
      loop invariant target_unchanged: \forall integer j; 0 <= j < v1 ==> v4[j] == \at(v4[j],normal_start);
      loop invariant info: v7[1] == 0 && v7[2] == 0;


      loop invariant top: v10 == v1-1;
      loop invariant permutation_bounds: \forall integer j; 0 <= j < v1 ==> 0 <= v3[j] < v1;
      loop invariant permutation_injective: injective(v3,v1);
      loop assigns v11, v12, v13, v2[0 .. v1-1], v3[0 .. v1-1], v6[0 .. 2*v1-1], v7[0 .. 2];

  */
while (1) {
    v11 = v3[v10];
    if (v11 == v10) {
      /*@
      loop invariant cursor_fixed: v3[v11] == v11;
      loop invariant suffix: \forall integer j; v11 < j <= v10 ==> v3[j] == j;
       loop invariant bounds: 0 <= v11 <= v10;
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
        /*@ assert success_permutation: \forall integer j; 0 <= j < v1 ==> v3[j] == j; */
        /*@ assert success_values: \forall integer j; 0 <= j < v1 ==>
          v2[j] == \at(v4[j],normal_start); */
        /*@ assert success_far: far_correct{Pre,normal_start}(v2,v4,v1); */
        /*@ assert success_reachable: values_reachable{Pre}(v2,v3,v1); */
        return 0U;
      } else {
      }
    } else {
    }
    /*@ assert chosen_bounds: 0 <= v11 < v10; */
    /*@ assert chosen_not_fixed: v3[v11] != v11; */
    /*@ assert chosen_destination: v3[v10] != v10 ==> v11 == v3[v10]; */
    /*@ assert chosen_top: v3[v10] == v10 ==> v3[v11] != v10; */
    /*@ ghost action_start: ; */
    /*@ assert action_bounds: array_bounded{action_start}(v3,v1); */
    /*@ assert action_matches: value_matched{action_start,normal_start}(v2,v3,v4,v1); */
    if (v2[v11] != v2[v10]) {
      v13 = (v10 - v11);
      if (v13 > 16U) {
        /*@ assert blocked_original_wrong:
          \at(v2[\at(v11,Here)],Pre) != \at(v4[\at(v11,Here)],normal_start); */
        /*@ assert blocked_not_far: !far_correct{Pre,normal_start}(v2,v4,v1); */
        /*@ assert blocked_not_reachable: !values_reachable{Pre}(v2,v3,v1); */
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
    /*@ assert data_far: \forall integer j; 0 <= j < v1 && v1-1-j > 16 ==>
      v2[j] == \at(v2[j],Pre); */
    /*@ assert data_target: \forall integer j; 0 <= j < v1 ==>
      v4[j] == \at(v4[j],normal_start); */
    /*@ assert data_info: v7[1] == 0 && v7[2] == 0; */
    /*@ assert data_exchange: \forall integer j; 0 <= j < v1 ==>
      v2[j] == \at(v2[j == v10 ? v11 : j == v11 ? v10 : j],action_start); */
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



    /*@ assert swap_data_cells: \forall integer j; 0 <= j < v1 ==>
      v3+v11 != v2+j && v3+v10 != v2+j; */
    /*@ assert swap_target_cells: \forall integer j; 0 <= j < v1 ==>
      v3+v11 != v4+j && v3+v10 != v4+j; */
    /*@ assert swap_value_bounds: 0 <= v3[v11] < v1 && 0 <= v3[v10] < v1; */
    /*@ ghost proof_swap: ; */
    v12 = v3[v11];
    v3[v11] = v3[v10];
    /*@ assert target_mid_frame: \forall integer j; 0 <= j < v1 ==>
      v4[j] == \at(v4[j],proof_swap); */
    /*@ assert data_mid_frame: \forall integer j; 0 <= j < v1 ==>
      v2[j] == \at(v2[j],proof_swap); */
    v3[v10] = v12;
    /*@ assert target_final_frame: \forall integer j; 0 <= j < v1 ==>
      v4[j] == \at(v4[j],proof_swap); */
    /*@ assert info_final_frame: v7[1] == \at(v7[1],proof_swap) && v7[2] == \at(v7[2],proof_swap); */
    /*@ assert swap_prefix_frame: \forall integer i; 0 <= i < v10 && i != v11 ==>
      v3[i] == \at(v3[i],proof_swap); */
    /*@ assert swap_endpoints: v3[v11] == \at(v3[v10],proof_swap) &&
      v3[v10] == \at(v3[v11],proof_swap); */
    /*@ assert swap_full_frame: \forall integer i; 0 <= i < v1 && i != v11 && i != v10 ==>
      v3[i] == \at(v3[i],proof_swap); */

    /*@ assert permutation_exchange: \forall integer j; 0 <= j < v1 ==>
      v3[j] == \at(v3[j == v10 ? v11 : j == v11 ? v10 : j],action_start); */
    /*@ assert data_final_frame: \forall integer j; 0 <= j < v1 ==>
      v2[j] == \at(v2[j],proof_swap); */
    /*@ assert data_final_exchange: \forall integer j; 0 <= j < v1 ==>
      v2[j] == \at(v2[j == v10 ? v11 : j == v11 ? v10 : j],action_start); */
    /*@ assert final_data_exchange: exchanged{action_start,Here}(v2,v1,v10,v11); */
    /*@ assert final_perm_exchange: exchanged{action_start,Here}(v3,v1,v10,v11); */
    /*@ assert after_bounds: array_bounded(v3,v1); */
    /*@ assert swap_post_bounds: \forall integer i; 0 <= i < v1 ==> 0 <= v3[i] < v1; */
    /*@ assert final_matches: value_matched{Here,normal_start}(v2,v3,v4,v1); */
    /*@ assert matched_after: \forall integer j; 0 <= j < v1 ==>
      v2[j] == \at(v4[\at(v3[j],Here)],normal_start); */
    /*@ assert swap_post_injective: injective(v3,v1); */






  }
}


/*@
 strategy TargetRelation:
   \tactic("Wp.unfold", \goal(G: P_target_matches(_,_,_,_,_,_)), \select(G), \children(ProofSMT)), ProofSMT;
 strategy FarCorrect:
   \tactic("Wp.unfold", \ingoal(G: P_far_correct(_,_,_,_,_)), \select(G), \children(ProofSMT)), ProofSMT;
 proof TargetRelation: normal_target_relation;
 proof FarCorrect: success_far,blocked_not_far;
 proof StoredArray: data_exchange,permutation_exchange;
*/
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

/*@ proof ZeroIndex: swap_post_bounds,swap_post_injective,suffix;
    proof StoredArray: info,target_unchanged,far_values,initially_fixed;
*/

/*@
 proof StoredArray: data_far,data_target,data_info,data_final_frame;
 strategy MatchAt:
   \tactic("Wp.instance", \goal(T[shift_uint32(Target,P[shift_uint32(Perm,J)])] == D[shift_uint32(Data,J)]),
     \when(H: \forall integer j; _ ==> T[shift_uint32(Target,A[shift_uint32(Perm,j)])] == A[shift_uint32(Data,j)]),
     \select(H), \param("P1",J), \children(ProofSMT)), ProofSMT;
 proof MatchAt: matched_after;
*/

/*@
 strategy PointRight:
   \tactic("Wp.instance", \goal(_ == M[shift_uint32(P,I)]),
     \when(H: \forall integer j; _ ==> _ == M[shift_uint32(P,j)]),
     \select(H), \param("P1",I), \children(ProofSMT)), ProofSMT;
 strategy PointLeft:
   \tactic("Wp.instance", \goal(M[shift_uint32(P,I)] == _),
     \when(H: \forall integer j; _ ==> M[shift_uint32(P,j)] == _),
     \select(H), \param("P1",I), \children(PointRight)), PointRight;
 strategy PointStoreRight:
   \tactic("Wp.array", \goal(_ == (T: _[_[_]][_])), \select(T), \children(PointLeft)), PointLeft;
 strategy PointStore:
   \tactic("Wp.array", \goal((T: _[_[_]][_]) == _), \select(T), \children(PointStoreRight)), PointStoreRight;
 strategy PointZero:
   \tactic("Wp.cut", \when(V <= 0), \when(0 <= V), \select(0),
     \param("case","MODUS"), \param("clause",V == 0), \children(PointStore)), PointStore;
 proof PointZero: far_values,info,initially_fixed,target_unchanged,suffix,
   data_far,data_target,data_info,data_final_frame,data_final_exchange;
*/

/*@
 strategy MatchDefinition:
   \tactic("Wp.unfold", \goal(G: P_value_matched(_,_,_,_,_,_)), \select(G), \children(ProofSMT)), ProofSMT;
 strategy ExchangeDefinition:
   \tactic("Wp.unfold", \goal(G: P_exchanged(_,_,_,_,_,_)), \select(G), \children(PointZero)), PointZero;
 strategy UseValueExchange:
   \tactic("Wp.lemma", \goal(P_value_matched(T,B,D,P,Target,N)),
     \when(P_value_matched(T,A,D,P,Target,N)), \when(P_exchanged(B,A,D,N,I,J)),
     \select(0), \param("lemma","values_exchange"),
     \param("P1",T), \param("P2",B), \param("P3",A),
     \param("P4",D), \param("P5",P), \param("P6",Target),
     \param("P7",N), \param("P8",I), \param("P9",J), \children(SwapFramePremise)), ProofSMT;
 strategy MatchedFromPredicate:
   \tactic("Wp.unfold", \when(H: P_value_matched(_,_,_,_,_,_)), \select(H), \children(PointZero)), PointZero;
 proof MatchDefinition: action_matches;
 proof ExchangeDefinition: final_data_exchange,final_perm_exchange;
 proof UseValueExchange: final_matches;
 proof MatchedFromPredicate: matched_after;
*/

/*@
 strategy SuffixPoint:
   \tactic("Wp.instance", \goal(M[shift_uint32(P,I)] == I),
     \when(H: \forall integer j; j <= N ==> K < j ==> M[shift_uint32(P,j)] == j),
     \select(H), \param("P1",I), \children(ProofSMT)), ProofSMT;
 proof SuffixPoint: suffix;
 strategy ExchangePointLeft:
   \tactic("Wp.instance", \goal(M[shift_uint32(P,I)] == A[shift_uint32(P,_)]),
     \when(H: \forall integer j; _ ==> M[shift_uint32(P,j)] == A[shift_uint32(P,_)]),
     \select(H), \param("P1",I), \children(ProofSMT)), ProofSMT;
 strategy ExchangePointRight:
   \tactic("Wp.instance", \goal(A[shift_uint32(P,_)] == M[shift_uint32(P,I)]),
     \when(H: \forall integer j; _ ==> A[shift_uint32(P,_)] == M[shift_uint32(P,j)]),
     \select(H), \param("P1",I), \children(ProofSMT)), ExchangePointLeft;
 strategy ExchangeExact:
   \tactic("Wp.unfold", \goal(G: P_exchanged(_,_,_,_,_,_)), \select(G), \children(ExchangePointRight));
 proof ExchangeExact: final_data_exchange,final_perm_exchange;
 proof StoredArray: target_final_frame,info_final_frame;
 proof ProofSMT: target_unchanged,info;
*/

/*@ proof StoredArray: target_mid_frame,data_mid_frame; */

/*@
 strategy IffOne:
   \tactic("Wp.cut", \when(0 <= S), \when(S <= 1), \select(0),
     \param("case","CASES"), \param("clause",S == 1), \children(ProofSMT)), ProofSMT;
 strategy IffZero:
   \tactic("Wp.cut", \when(0 <= S), \when(S <= 1), \select(0),
     \param("case","CASES"), \param("clause",S == 0), \children(IffOne)), IffOne;
 proof IffZero: guarded_success_iff;
 proof ProofSMT: target_mid_frame,data_mid_frame,target_final_frame,data_final_frame;
*/

/*@
 strategy CellApartReverse:
   \tactic("Wp.lemma", \goal(shift_uint32(P,I) != shift_uint32(Q,J)),
     \when(separated(shift_uint32(Q,0),M,shift_uint32(P,0),N)),
     \select(0), \param("lemma","separate_cells"),
     \param("P1",Q), \param("P2",P), \param("P3",M), \param("P4",N),
     \param("P5",J), \param("P6",I), \children(SwapFramePremise)), ProofSMT;
 strategy CellApart:
   \tactic("Wp.lemma", \goal(shift_uint32(P,I) != shift_uint32(Q,J)),
     \when(separated(shift_uint32(P,0),N,shift_uint32(Q,0),M)),
     \select(0), \param("lemma","separate_cells"),
     \param("P1",P), \param("P2",Q), \param("P3",N), \param("P4",M),
     \param("P5",I), \param("P6",J), \children(SwapFramePremise)), CellApartReverse;
 strategy CellsSplit:
   \tactic("Wp.split", \goal(G: _ && _), \select(G), \children(CellApart)), CellApart;
 proof CellsSplit: swap_data_cells,swap_target_cells;
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

/*@ proof SelectedPost: injective_selected;
 proof InjectivePost: permutation_injective;
 proof ProofSMT: swap_post_bounds;
*/

/*@
 strategy SuffixCases:
   \tactic("Wp.cut", \goal(M[shift_uint32(P,I)] == I),
     \when(\forall integer j; j <= N ==> K < j ==> M[shift_uint32(P,j)] == j),
     \select(0), \param("case","CASES"), \param("clause",I == K), \children(SuffixPoint)), SuffixPoint;
 proof SuffixCases: suffix;
 strategy FillInjectiveAliasLeft:
   \tactic("Wp.lemma", \goal(P_selected_injective(B,S,T,P,N,_)),
     \when(A[shift_uint32(P,K)[D]][shift_uint32(U,D)[_]] == B),
     \select(0), \param("lemma","selected_injective_step"),
     \param("P1",B), \param("P2",A), \param("P3",S), \param("P4",T), \param("P5",P),
     \param("P6",N), \param("P7",K), \param("P8",D), \children(SwapFramePremise)), FillInjective;
 proof FillInjectiveAliasLeft: fill_post_injective;
*/

/*@
 strategy BoundUnfold:
   \tactic("Wp.unfold", \goal(G: P_array_bounded(_,_,_)), \select(G), \children(ProofSMT)), ProofSMT;
 strategy BoundUse:
   \tactic("Wp.lemma", \goal(P_array_bounded(B,P,N)),
     \when(P_exchanged(B,A,P,N,I,J)), \select(0), \param("lemma","bounds_exchange"),
     \param("P1",B), \param("P2",A), \param("P3",P), \param("P4",N),
     \param("P5",I), \param("P6",J), \children(SwapFramePremise)), ProofSMT;
 strategy BoundFromPredicate:
   \tactic("Wp.unfold", \when(H: P_array_bounded(_,_,_)), \select(H), \children(ProofSMT)), ProofSMT;
 proof BoundUse: after_bounds;
 proof BoundFromPredicate: swap_post_bounds;
*/

/*@ proof BoundUnfold: action_bounds; */
