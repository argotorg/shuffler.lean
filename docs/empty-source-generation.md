# Exact generation cost from interval packing

This note gives a paper proof for the empty-source problem. The interval
packing optimizer and this complete equivalence are not Lean theorems in
the current tree. Existing Lean trace extraction, birth-availability, and
plan-realization results supply the underlying plan model. No production
algorithm is changed here.

Assume a common DUP and SWAP reach `R>=1`, an empty source, and a legal
direct introduction for each target value. Let the target length be `n`,
the direct price of value `v` be `d_v`, and the DUP price be `u`. Define

```
p_v = max(d_v-u,0)
D   = sum_j d_target[j].
```

For each pair of consecutive occurrences `p<t` of one value `v`, give
the half-open interval `[p,t)` weight `p_v`. Let `M_R` be the maximum
weight of a subset of these intervals with at most `R` selected intervals
covering any cut. Then

```
minimum generation score = D-M_R.
```

Generation score excludes SWAP cost. The minimum ranges over valid
no-POP traces from the empty source to the exact target. Direct births
are used when they are cheaper than DUP; no inequality `d_v>=u` is needed.

## Necessity

Extract a birth-to-target assignment from a trace. At an inclusive birth
cut `k`, let `C_v(k)` count births of value `v` at indices at most `k`,
and let `A_v(k-R)` count its target occurrences at indices at most `k-R`.
Lag feasibility gives the nonnegative inventory

```
I_v(k) = C_v(k)-A_v(k-R).
```

The kth copy of `v` can use DUP only if it is born no later than the
previous target-v occurrence plus `R`. This is the available-copy count
criterion proved for the plan model. Thus a DUP that saves premium can
be assigned to its distinct preceding target gap `p->t`, and it forces
`I_v(p+R)>=1`.

There is no v-target deadline strictly between `p+R` and `t+R`. Births
can only increase `C_v`, so this unit remains in the count inventory over
`[p+R,t+R)`. Consecutive gaps of the same value do not overlap. At any cut,
the number of selected gap intervals is at most the total inventory,
which is at most `R`. Each DUP saves at most its gap premium, and no gap
receives two savings. Therefore every trace has generation cost at least
`D-M_R`.

## Sufficiency by birth deadlines

Fix a selected interval set `Y`. Give each target occurrence `t` a birth
job of the same value. Its ordinary deadline is `t+R`. If the gap `p->t`
is selected, advance that job's deadline to `p+R`. The first occurrence
of each value retains its ordinary deadline.

For a fixed value these deadlines are nondecreasing in target order.
Sort all jobs by deadline, breaking equal deadlines by target index, and
put them in birth slots `0,...,n-1` in that order. The number of jobs due
through any cut `k` is

```
dueTargets(k) + selectedOverlap(k-R).
```

Advancing `p->t` adds exactly one due job during `[p+R,t+R)`. Scheduling
all unit jobs by their deadlines is possible precisely when this count
is at most the available number `min(k+1,n)` of birth slots.

If all interval overlaps are at most `R`, those inequalities hold:

- Before `k=R`, no selected interval has started in shifted time, and no
  ordinary target deadline has arrived.
- For `R<=k<n`, the number of ordinary deadlines is `k-R+1`. There are
  exactly `R` further birth slots through the cut.
- For `k>=n`, map each active interval `[p,t)` at `k-R` to its next target
  endpoint `t`. Those endpoints are distinct and all satisfy `t>k-R`.
  Hence the overlap is at most the number of target endpoints still due,
  namely `n-dueTargets(k)`. This is exactly the smaller final inventory
  capacity. After the last deadline no interval remains active.

This proves the end boundaries, including targets shorter than `R`.
No extra capacity or terminal dummy token is needed. Conversely, the
deadline inequalities imply overlap at most `R`, so the condition is exact.

The resulting assignment satisfies `birth<=target+R`. A job whose gap
`p->t` was selected is born by `p+R`, and all earlier copies of its value
occur earlier in the birth order. The available-copy criterion therefore
permits DUP. Use DUP when it is cheaper and direct introduction otherwise.
Unselected jobs can always use their legal direct instruction. This gives
generation cost exactly `D-sum_{g in Y} p_value(g)`. The plan realizer
then produces a trace with that generation score. It may add SWAPs.

## Interval-flow algorithm and runtime

For `n>1`, make a directed path on target positions `0,...,n-1`. Each
idle arc `i->i+1` has capacity `R` and cost zero. Each gap contributes
an arc `p->t` of capacity one and cost `-p_v`. Send `R` units from the
first path node to the last. A flow unit is one interval lane: its gap
arcs cannot overlap. Conversely any interval set of overlap at most `R`
can be partitioned into `R` such lanes. Thus an optimal flow selects
exactly a maximum-weight feasible interval set. Handle `n<=1` directly.

The graph has `O(n)` vertices and arcs. The initial graph is acyclic,
so negative gap costs permit linear-time initial potentials. Successive
shortest paths with reduced costs and Dijkstra require at most `R`
augmentations, giving `O(R*n*log n)` arithmetic operations. At production
reach 16 this is `O(n log n)`, within the `O(n^2)` ceiling. Sorting the
birth jobs adds `O(n log n)` work. This bound is for generation selection
and its birth plan; it is not a bound for the unresolved joint optimizer.

Costs can be exact integers after clearing a common rational denominator.
If their bit length is `K`, path sums have `O(K+log n)` bits. The arithmetic
bound must be multiplied by the cost of exact operations on those numbers;
it is not a unit-bit bound for arbitrary supplied prices.

Capacity is `R`, not `R-1`. The current target endpoint exits at its
deadline, leaving `R` count-inventory positions for retained copies. For
example, target `a b a` at reach one can retain its a-gap, using birth
word `a a b`. A cache comparison would need a bypass-like service slot;
the interval statement above avoids transferring a different paging model.

## What this does not solve

Minimum generation does not give a factor-two surplus guarantee for
total trace score. The saved reduced-reach example `a b b b a`, with
`R=1` and the C++ gas model, has baseline 18. Its generation minimum
retains the a-gap and needs three SWAPs, for score 27 and surplus 9.
Another trace introduces a second a, uses no SWAP, and costs 21, with
surplus 3. Thus 9 exceeds twice 3. The weighted version has the same
failure with different scores. These checked examples are recorded in
`Bench/evidence-weighted-introduction-obstruction.json`.

This note completes the empty-source generation optimization argument
that was only a possible interval-flow route in
`docs/optimality-inventory-research.md`. It does not extend the result to
arbitrary source arrangements. It also does not select endpoint identities
jointly with retained gaps, prove a rounding theorem, or prove the missing
global factor-two constructor.
