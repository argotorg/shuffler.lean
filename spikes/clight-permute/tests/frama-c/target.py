# SPDX-License-Identifier: GPL-3.0-or-later
"""Prove target initialization and its value at each destination index."""


def specification(memory_contract, memory_loops, full_contract, initialization_strategy):
    definition = full_contract.split('  predicate target_matches')[1].split(
        '  predicate values_reachable')[0]
    prefix = memory_contract.split('  ensures status_range:')[0]
    contract = ('/*@\n  predicate target_matches' + definition + '*/\n' + prefix
                + r'''  ensures target_initialized: \initialized(v4 + (0 .. v1-1));
  ensures target_definition: target_matches{Pre,Post}(v2,v3,v4,v1);
*/
''')
    contract = contract.replace(r'terminates \true;', r'terminates \false;')
    target_invariant = r'''loop invariant target_definition: \forall integer i;
        0 <= i < v1 ==> v4[\at(v3[i],Pre)] == \at(v2[i],Pre);
      '''
    filled = r'''      loop invariant marks: \forall integer j; 0 <= j < v1 ==>
        (v5[j] != 0 <==> (\exists integer i; 0 <= i < v8 && \at(v3[i],Pre) == j));
      loop invariant filled: \forall integer i; 0 <= i < v8 ==>
        v4[\at(v3[i],Pre)] == \at(v2[i],Pre);
'''

    def extend(index, loop):
        if index == 1:
            return loop.replace('      loop invariant filled_initialized:',
                                filled + '      loop invariant filled_initialized:')
        if index in (2, 3):
            return loop.replace('loop invariant target_initialized:',
                                target_invariant + 'loop invariant target_initialized:')
        if index == 5:
            result = loop.replace('/*@', '/*@ ' + target_invariant + r'''
      loop invariant target_initialized: \initialized(v4 + (0 .. v1-1));
''', 1)
            # The safety component proves trace initialization. This component
            # proves the two target postconditions on the same C and inputs.
            return result.replace(r'loop invariant initialized: \initialized(v6 + (0 .. v7[0]-1));', '')
        return loop

    loops = tuple(extend(i, loop) for i, loop in enumerate(memory_loops))
    strategies = initialization_strategy + r'''
/*@
  strategy ProofSMT: \prover("Z3", "CVC5", 10.0);
  strategy TargetUnfold:
    \tactic("Wp.unfold", \goal(G: P_target_matches(_,_,_,_,_,_)),
      \select(G), \children(ProofSMT)), ProofSMT;
  proof TargetUnfold: target_definition;
  strategy TargetStoredRight:
    \tactic("Wp.array", \goal(_ == (T: _[_[_]][_])), \select(T), \children(ProofSMT)), ProofSMT;
  strategy TargetStored:
    \tactic("Wp.array", \goal((T: _[_[_]][_]) == _), \select(T), \children(TargetStoredRight)), TargetStoredRight;
  strategy TargetZero:
    \tactic("Wp.cut", \when(V <= 0), \when(0 <= V), \select(0),
      \param("case","MODUS"), \param("clause",V == 0), \children(TargetStored)), TargetStored;
  proof TargetZero: target_definition;
*/
'''
    return contract, loops, strategies
