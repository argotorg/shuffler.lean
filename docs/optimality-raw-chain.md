# A counterexample for the raw chain policy

Use the C++ prices, bytes-only weights, and 32-byte LOAD addresses for two
spilled values `a` and `b`. Let:

```text
source = 0^15
target = a ++ b^12 ++ a ++ 0^15
additions = {a,a} + {b}^12
baseline = 80 bytes
```

The pinned v12 raw chain policy returns 457 bytes. It retains `a` through
the run of `b` values and repeatedly loads `b`. The full portfolio returns
146 bytes, equal to its retained original-BBU candidate on this input.

The following witness retains `b` through its run and loads `a` again:

```text
LOAD a; SW15; LOAD b; DUP1;
for d = 2 through 11: SW16; DUPd;
SW16; LOAD a; SW15; SW12; SW16
```

Production replay checks the exact target and additions. It costs 96 gas
and 128 bytes: three LOADs, eleven DUPs, and fifteen SWAPs. No exact optimum
claim is needed to refute factor two for the raw policy:

```text
457 + 80 > 2 * 128
```

The optimum is at most the witness cost. The full portfolio passes this
witness comparison because `146 + 80 ≤ 2 * 128`. This does not prove a global
ratio for the portfolio.

`Tests/OptimalityRawChain.lean` checks the production witness, raw policy,
full portfolio, and baseline. It also proves that a trace with the raw cost
cannot satisfy `TwiceExcess` in the presence of the checked-cost witness.

The initial scan tested 24 cases with block lengths 4, 8, 12, 16, 24, and 32,
and second LOAD widths 2, 8, 16, and 32. The first LOAD width stays 32.
The scan did not use an exact oracle. The explicit witness comparison above
concerns only the saved length-12, equal-width case. The pinned runner hash is
`e3a116256ffef648ac0404d04006e46b4335df01c2ce9dbad42e4d1eba8e3f0b`.
