# Source bounds from cycle deadlines

Lean now proves the cycle lower bound and implements the reverse
construction with actual production traces. `SourceLazy.realize` returns
the prescribed target, exact additions, supplied birth events, and SWAP
count `K+2q`. The lower bound applies to every no-POP trace whose extracted
token assignment is the supplied assignment.

A general theorem that the new constructor's extracted token assignment
equals its input assignment is still separate work. The tests check that
identity in named examples. The existing source realizer has not yet been
replaced.

## Statement

Fix a reach `R`, a source height `h`, and a final size `n >= h`.
Give each source occurrence and each future birth a distinct token label.
Source token labels are `0,...,h-1`. Future token `t` is introduced when
the stack grows from height `t` to height `t+1`.

Let `f` map each token label to its final position. Assume:

1. `f` is a permutation of `0,...,n-1`.
2. `i <= f(i)+R` for every token `i`.
3. Every source position with `i+R+1<h` is fixed by `f`.

The second condition is the birth deadline. The third fixes source
positions that are already outside the initial SWAP window.

For each nontrivial cycle `C` of `f`, let `m` be its least position.
Let `b` be its first future position, or infinity if it has none. Count
`C` in `q` exactly when:

```
initial top h-1 is not in C, and b > m+R.
```

For an empty source, set `q=0`. An equivalent definition, used in Lean,
has no minimum or infinity: the cycle omits the initial top and contains
a source position `i` such that every future cycle position `j` satisfies
`i+R<j`.

Let `K(f)` be moved positions minus nontrivial cycles. The paper argument
gives this exact minimum number of SWAPs for the fixed labelled assignment:

```
K(f)+2q.
```

This fixes the birth order. It does not select an assignment between equal
values and does not solve the joint generation and assignment problem.

## Why every counted cycle costs two more SWAPs

Each SWAP either splits one remaining cycle or joins two. A split reduces
`K` by one; a join increases it by one. A trace with `M` joins therefore
has exactly `K(f)+2M` SWAPs.

Consider a counted original cycle before any SWAP touches one of its
positions. It is still a separate cycle in the remaining permutation.
Its least position `m` is moved. Thus it must be touched before the
current top passes `m+R`, when `m` becomes unreachable.

Until that point no future top belongs to this cycle, since `b>m+R`.
The initial top also lies outside it. Its first touch therefore joins
it to another cycle.

One such first touch cannot account for two counted cycles. The lower
SWAP endpoint belongs to at most one untouched original cycle. If its
top endpoint belonged to a second counted cycle, that second cycle
would already have required a touch before that top was introduced.
Thus `M>=q`, which gives the lower bound.

## Reverse construction

Start at the assigned final token stack. Remove future tokens in
decreasing label order. Keep the remaining assignment as a permutation
on the original domain, with removed labels fixed.

Suppose `t` is the greatest remaining future label. Ordinarily:

1. Swap physical positions `t` and `f(t)` if they differ.
2. Token `t` is now at the top. Remove it in this reverse description.

The swap is legal because `f(t)>=t-R`. It splits the cycle and fixes
exactly the row `t`, except that a two-cycle becomes two fixed points.
In cycle notation, it removes `t` and connects its predecessor `p` to
`f(t)`. The shortcut satisfies the deadline because

```
p<t<=f(t)+R.
```

All other deadlines remain unchanged. Repeating the step removes future
vertices from each original cycle without splitting it into two
nontrivial cycles.

There is one special case. When the current `t=b` is a cycle's last
remaining future vertex, test `b<=m+R`.

If the test holds, every remaining source vertex in that cycle is
reachable from top `b`. Resolve the entire cycle now, with the usual
minimum star permutation. All its SWAPs are splits. Then remove `b`.
The other cycles are unchanged.

If the test fails, use the ordinary removal step and leave the source
cycle for the initial height. This source cycle has at least two
vertices. If it had only one source vertex `m`, the remaining two-cycle
would have edge `b -> m`, contrary to its preserved deadline
`b<=m+R`.

At height `h`, solve the remaining source permutation with the exact
star permutation routine. Every moved source position is reachable by
the frozen-source premise. Its cycles are the late cycles just described
and the cycles that never had a future vertex. Membership of the initial
top is unchanged. Thus exactly `q` remaining cycles omit that top.
The source routine uses one join per such cycle. Every other SWAP in
the construction is a split. Its total is `K(f)+2q`.

Reverse this operation list. Reverse removals become ordinary births;
SWAP is its own inverse. This gives the required forward construction.
The reverse removals are proof and planning steps, not POP instructions
in the output trace.

## Generation methods

The token construction first treats births as distinct labels. It can
then use the supplied legal direct or DUP method for each birth value.

Before birth `t`, every position below `t-R` already has its final target
value: later tops cannot reach it. The multiset of all present values is
the source plus the earlier birth values. Consequently the number of
readable copies of value `v` is

```
count(source + earlier births, v) - count(target.take(t-R), v).
```

The existing `BirthAvailable` DUP condition says this number is positive.
It does not depend on the order of the readable values. The existing
`physicallyAvailable_of_counts` lemma can therefore supply the actual
PUSH, LOAD, or DUP operations without changing the SWAP count or birth
word.

For the production theorem, `R=16` for both SWAP and DUP. For a generic
reach theorem, the two reaches must agree in this count argument.

## An edge cost for assignment selection

Let `E` be the number of moved rows. Let `N` count moved edges `i -> f(i)`
whose endpoints both lie strictly below the initial source top. Define

```
W = E+N.
```

This is a sum of fixed edge prices: zero for an identity edge, two for a
moved edge between interior source positions, and one for any other moved
edge.

Every counted forced cycle contains an interior edge. Take its source
witness `p` and predecessor `r`. The deadline gives `r<=p+R`, so `r` cannot
be a future vertex of that forced cycle. Both positions are old, and the
cycle omits the initial top. Different cycles give different edges. Thus
`q<=N`. Also `q` is at most the total number of nontrivial cycles, so

```
K+2q <= E+q <= W.
```

Conversely, a moved token with both endpoints below the initial top must
participate in at least two SWAPs: no physical SWAP directly joins those
two positions. Every other moved token needs at least one. Each SWAP moves
two tokens. Therefore `W<=2*SWAPs` for every no-POP trace. Lean proves this
inequality through a local potential on the actual trace's SWAP list.

Selecting a minimum-W assignment for a supplied birth word would therefore
give a factor-two SWAP guarantee. The cost matrix is explicit. An executable
minimum-W assignment solver is a separate task.

## Lean proofs and checks

`SourceLazy.realize` provides an actual `BuiltTrace`, the supplied birth
events, and exact SWAP count `SourceLazy.swapBound 16 h f` for every
`SourcePlan`. `SourceLazy.swapBound_le_trace` lower-bounds each no-POP trace
using its extracted labelled assignment.

The local erase lemmas prove fixed rows, deadlines, rank decrease, and
cycle deletion. `SourceLazy.State` tracks the current remaining assignment
and frozen prefix. `Phase` chooses and compiles one local permutation.
`Base` handles the initial source. `Birth` proves the readable count
condition and emits the selected birth operation. `Build` supplies the
terminating reverse recursion and returns the complete forward trace.

`Tests/OptimalitySourceLazy.lean` checks the actual constructor. The old
five-SWAP distinct-source plan uses three SWAPs. The two old nine-SWAP
plans each use five. A production-reach forced cycle with source height
17 and first future cycle position 24 uses four SWAPs although it moves
only three tokens. The tests also cover a closed source cycle and an
empty source and target. The constructor's axiom report lists only
`propext`, `Classical.choice`, and `Quot.sound`.

`SourceLazy.swapBound_le_weightScore` and
`SourceLazy.weightScore_le_twice_swapCount` prove the two inequalities for
the edge cost. The cost and cycle tests also cover source heights zero
and one, the exact deadline, and the first position after the deadline.
