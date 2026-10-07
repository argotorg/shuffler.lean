# Weight regions for the target-order bound

The proved [target-order theorem](target-order-optimality.md) requires
`p_v <= rho*s` for every target value. This note expands that condition
for the two supplied EVM cost models. These are algebraic consequences
of the cost definitions; the table is not a new Lean theorem.

Let `g>=0` and `b>=0` be the gas and byte weights, not both zero. Then
DUP and SWAP both have score `s=3*g+b`. Let `L` be the immediate width
of a nonzero PUSH encoding, so `1<=L<=32`. The premium is direct score
minus the smaller of direct score and DUP score.

| Direct operation | Premium | Exact target-order condition | Factor-two surplus condition |
| --- | --- | --- | --- |
| PUSH0 | `0` | always | always |
| PUSH L | `L*b` | `(L-1)*b <= 3*g` | `L*b <= 6*g+2*b` |
| EVM LOAD with PUSH0 address | `2*g+b` | always | always |
| C++ LOAD with PUSH0 address | `3*g+b` | always | always |
| LOAD with PUSH L address, either model | `3*g+(L+1)*b` | `L*b=0` | `(L-1)*b <= 3*g` |

For example, a nonzero PUSH costs `3*g+(L+1)*b`. Subtracting DUP gives
`L*b`. A LOAD adds MLOAD's `3*g+b` to the address PUSH, so its premium is
`3*g+(L+1)*b`. The two LOAD/PUSH0 rows differ because the C++ estimate
charges 6 gas for every LOAD, while the EVM model charges 5 gas in that
case.

The conditions must hold for all direct operations that occur in the
target. This gives several regions with no assignment oracle:

- Gas-only weights give exact optimality for arbitrary supplied encodings.
- PUSH1-address loads and PUSH1/PUSH2 literals give factor-two surplus
  for every choice of weights, including bytes-only.
- Arbitrary encodings up to PUSH32 give factor-two surplus whenever
  `31*b <= 3*g`. This condition covers the largest LOAD premium and also
  every PUSH premium.
- If all LOAD addresses use PUSH0, exact optimality only needs the stated
  width bound for each literal PUSH. It holds for PUSH1 literals at all
  weights, and for arbitrary literals when `31*b <= 3*g`.

The source is still empty, every target value must be directly available,
and comparison traces must be eligible. These are sufficient conditions
for the existing append candidate and scheduler. A failed condition does
not imply that their actual output is suboptimal.
