# Value-job cost does not equal endpoint cost

The unit-job deadline model can express generation quotas. It cannot use
value agreement as the endpoint identity reward without changing the
minimum joint cost. The distinction already matters at reach 16.

This note gives a general family on paper, a Lean certificate for its
64-position instance, and an 80-position case where the cycle allowance
does not pay the difference. Neither case refutes the full assignment
relaxation or a factor-two trace bound. They exclude two proposed repairs
of the weaker value-job objective.

## Family

For reach `R>=2`, let

```
target = a^R ++ b^(2R) ++ a^R
DUP score = SWAP score = 1
direct_a = 3
direct_b = 1.
```

The generation baseline is `B=4R+2`. The a premium is 2; the b premium
is zero. Every internal a gap is short except the gap from position
`R-1` to position `3R`.

Keeping the target birth order misses that long gap, so it costs
`G=B+2` with zero movement. Its joint objective is `J=2B+4`.

To retain the long gap, at least `R+1` copies of a must be born by
position `2R-1`. Only R target-a positions lie in that prefix. Hence
some birth row `i<=2R-1` supplies a late target-a endpoint `j>=3R`.
A permutation with two moved positions would transpose i and j. Its
reverse edge would require

```
j <= i+R <= 3R-1,
```

which is impossible. A permutation cannot have exactly one moved
position. Thus every plan retaining the long gap has at least three
moved endpoints. All other plans pay the premium 2. The true joint
minimum is therefore at least `2B+3`.

Use the following three-cycle and fix every other endpoint:

```
2R-1 -> 3R
2R   -> 2R-1
3R   -> 2R.
```

It meets every lag bound. Its birth word changes only positions `2R-1`
and `3R`: b becomes a at the former, and a becomes b at the latter.
All a gaps are retained. Thus G=B and E=3, attaining

```
min J = 2B+3.
```

The unit-job relaxation charges only two value mismatches on this same
birth word. Its score is `2B+2`. It cannot do less: retaining the long
gap changes the word, and two words with equal multiplicities cannot
differ at exactly one position. Missing that gap costs `2B+4` already.
Therefore its exact minimum is

```
min value-job score = 2B+2.
```

No choice among optimal value-job schedules can preserve that objective
when endpoint identity is restored.

## Reach-16 certificate

`Tests/OptimalityJobRelaxation.lean` uses the actual Plan and cheapest-birth
APIs with target `a^16 ++ b^32 ++ a^16`. It checks

```
B = 66
G = 66
E = 3
value mismatches = 2
J = 135
value-job score = 134.
```

The finite certificate has scale one. Divide the positions into four
blocks of length 16. Its row multipliers are respectively `2,1,0,-1`;
its column multipliers are `2,0,1,2`. The long a gap at position 15 has
quota multiplier 3 and cap multiplier 1. Every other gap has quota
multiplier zero and cap multiplier equal to its reward.

The existing `Certificate.globallyMinimal` theorem proves that every
valid plan has J at least 135. Thus the checked relaxed witness is below
every true joint plan; this is not only a difference on one fixed word.

The three-cycle needs two SWAPs in the existing realizer. Its trace score
is `B+2`, so `score+B=2B+2`. The single cycle pays for this one-unit gap
in the final surplus comparison. The example rules out exact joint-cost
repair of the value-job relaxation. The next case also rules out a repair
theorem that uses the cycle allowance to attain this weaker lower bound.

## A longer gap exceeds the cycle allowance

At reach 16, take

```
target = a^16 ++ b^48 ++ a^16
DUP score = SWAP score = 1
direct_a = 4
direct_b = 1.
```

Now B=83. Use the four-cycle

```
31 -> 64 -> 48 -> 32 -> 31.
```

It has G=83, two value mismatches, and relaxed score 168. The actual
realizer uses three SWAPs and has score 86. These values are checked in
the `LongerGap` part of the same Lean test.

The long a gap runs from 15 to 64. The proved capped-gap lower bound is

```
Q = min(3, floor((64-15-1)/16)) = 3.
```

Thus every eligible trace has score at least `B+Q=86`, and

```
score(trace)+B >= 169 > 168.
```

The theorem `LongerGap.below_every_trace_surplus` proves this strict
inequality for every eligible trace. The relaxed optimum is at most its
feasible witness score 168. Therefore no trace can meet
`score(trace)+B <= min(value-job score)`. The cycle allowance cannot
establish that proposed global repair theorem.
