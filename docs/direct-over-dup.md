# Direct introduction in place of DUP

`DirectDominance.normalize` replaces a DUP when its value can be introduced
by a permitted PUSH or LOAD and that operation has no greater weighted cost.
`CheapDirect` states these two conditions. The pass uses the fixed spill set.
It does not make an unavailable LOAD available.

Each replacement has the same stack effect as the original DUP. Lean proves
that the complete sequence of concrete stack states is unchanged. It also
proves that endpoints, additions, POP status, and SWAP count are unchanged,
that the selected weighted cost does not increase, and that no DUP of a
`CheapDirect` value remains. `normalizeBuilt` preserves the full built-trace
type.

This result applies to the retention-plan specification. If direct
introduction costs no more than DUP, retaining a value solely to duplicate it
cannot be required to attain minimum weighted cost. PUSH0 is one example:
its two gas units are less than the three gas units for DUP.

The result is about the requested weighted score. It does not imply that
both gas and bytes decrease. A wide PUSH can tie DUP in gas while using more
bytes; the tests include this case. They also cover unavailable variables,
return labels, wildcards, cheap spilled LOAD, DUP16 at height 17, POP, and the
empty trace. The full 3035-job build passes with this module and its tests.

The pass is not called by the v15 production portfolio. Its current role is
a proved normal form for the plan objective. It does not prove a joint
transport bound, plan realization, or global factor two.
