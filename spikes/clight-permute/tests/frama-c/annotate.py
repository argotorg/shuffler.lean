#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0-or-later
"""Add ACSL comments to the exact emitted C. Never change a C token."""
from pathlib import Path
import hashlib
import re

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / 'build' / 'frama-c'
SOURCE = ROOT / 'permute.c'

CONTRACT = r'''/*@
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
  requires permutation_input: permutation(v3,v1);
  terminates \true;
  assigns v2[0 .. v1-1], v3[0 .. v1-1], v4[0 .. v1-1], v5[0 .. v1-1],
          v6[0 .. 2*v1-1], v7[0 .. 2];
  ensures status: 0 <= \result <= 1;
  ensures count: 0 <= v7[0] <= 2*v1;
  ensures out_initialized: \initialized(v7 + (0 .. 2));
  ensures target_initialized: \initialized(v4 + (0 .. v1-1));
  ensures target_definition: target_matches{Pre,Post}(v2,v3,v4,v1);
  ensures success_iff: (\result == 0) <==> values_reachable{Pre}(v2,v3,v1);
  ensures success_data: \result == 0 ==> (\forall integer j; 0 <= j < v1 ==> v2[j] == v4[j]);
  ensures success_info: \result == 0 ==> v7[1] == 0 && v7[2] == 0;
  ensures blocked_info: \result == 1 ==> v7[1] < v1 && v1 - 1 - v7[1] > 16 &&
    v7[2] == v1 - 1 - v7[1] - 16 && v2[v7[1]] != v2[v1-1];
  ensures trace_initialized: \initialized(v6 + (0 .. v7[0]-1));
  ensures trace_bounds: \forall integer k; 0 <= k < v7[0] ==> 1 <= v6[k] <= 16 && v6[k] < v1;
  ensures trace_replay: \forall integer j; 0 <= j < v1 ==>
    v2[j] == replay_value{Pre,Post}(v2,v6,v1,v7[0],j);
  ensures trace_changes_values: \forall integer k; 0 <= k < v7[0] ==>
    replay_value{Pre,Post}(v2,v6,v1,k,v1-1) !=
    replay_value{Pre,Post}(v2,v6,v1,k,v1-1-v6[k]);
*/
'''

LOOPS = [
r'''/*@ loop invariant bounds: 0 <= v8 <= v1;
      loop invariant clear: \forall integer j; 0 <= j < v8 ==> v5[j] == 0;
      loop invariant initialized: \initialized(v5 + (0 .. v8-1));
      loop assigns v8, v5[0 .. v1-1];
      loop variant v1-v8;
  */''',
r'''/*@ loop invariant bounds: 0 <= v8 <= v1;
      loop invariant initialized: \initialized(v5 + (0 .. v1-1));
      loop invariant marks: \forall integer j; 0 <= j < v1 ==>
        (v5[j] != 0 <==> (\exists integer i; 0 <= i < v8 && v3[i] == j));
      loop invariant filled: \forall integer i; 0 <= i < v8 ==> v4[v3[i]] == v2[i];
      loop invariant filled_initialized: \forall integer i; 0 <= i < v8 ==> \initialized(v4 + v3[i]);
      loop assigns v8, v9, v4[0 .. v1-1], v5[0 .. v1-1];
      loop variant v1-v8;
  */''',
r'''/*@ loop invariant bounds: 0 <= v8 <= v1;
      loop invariant target_initialized: \initialized(v4 + (0 .. v1-1));
      loop invariant permutation_initialized: \initialized(v3 + (0 .. v1-1));
      loop invariant used_initialized: \initialized(v5 + (0 .. v1-1));
      loop invariant target_definition: target_matches{Pre,Here}(v2,v3,v4,v1);
      loop invariant multiset: \forall integer value;
        occurrences(v2,v1,value) == occurrences(v4,v1,value);
      loop invariant processed: \forall integer j; 0 <= j < v8 ==>
        (v5[j] == 1 && v3[j] == j && v2[j] == v4[j]) || (v5[j] == 0 && v2[j] != v4[j]);
      loop invariant permutation_bounds: \forall integer j; 0 <= j < v1 ==> v3[j] < v1;
      loop assigns v8, v3[0 .. v1-1], v5[0 .. v1-1];
      loop variant v1-v8;
  */''',
r'''/*@ loop invariant bounds: 0 <= v8 <= v1;
      loop invariant permutation_initialized: \initialized(v3 + (0 .. v1-1));
      loop invariant used_initialized: \initialized(v5 + (0 .. v1-1));
      loop invariant permutation_bounds: \forall integer j; 0 <= j < v1 ==> v3[j] < v1;
      loop invariant target_definition: target_matches{Pre,Here}(v2,v3,v4,v1);
      loop invariant matched: \forall integer j; 0 <= j < v8 ==> v2[j] == v4[v3[j]];
      loop invariant fixed: \forall integer j; 0 <= j < v1 && v2[j] == v4[j] ==> v3[j] == j && v5[j] == 1;
      loop invariant selected: \forall integer j; 0 <= j < v1 ==>
        (v5[j] != 0 <==> (\exists integer i; 0 <= i < v1 &&
          (i < v8 || v2[i] == v4[i]) && v3[i] == j));
      loop invariant injective_selected: \forall integer i,j;
        0 <= i < v1 && 0 <= j < v1 && (i < v8 || v2[i] == v4[i]) &&
        (j < v8 || v2[j] == v4[j]) && v3[i] == v3[j] ==> i == j;
      loop invariant matching_count: \forall integer value;
        pending(v2,v4,v1,v8,value) == available(v4,v5,v1,value);
      loop assigns v8, v9, v3[0 .. v1-1], v5[0 .. v1-1];
      loop variant v1-v8;
  */''',
r'''/*@ loop invariant bounds: 0 <= v9 <= v1;
          loop invariant absent: \forall integer j; 0 <= j < v9 ==> v5[j] != 0 || v2[v8] != v4[j];
          loop assigns v9;
          loop variant v1-v9;
      */''',
r'''/*@ loop invariant top: v10 == v1-1;
      loop invariant data_initialized: \initialized(v2 + (0 .. v1-1));
      loop invariant permutation_initialized: \initialized(v3 + (0 .. v1-1));
      loop invariant out_initialized: \initialized(v7 + (0 .. 2));
      loop invariant permutation_bounds: \forall integer j; 0 <= j < v1 ==> v3[j] < v1;
      loop invariant permutation: permutation(v3,v1);
      loop invariant rank_nonnegative: 0 <= moved(v3,v10);
      loop invariant budget: v7[0] + 2*moved(v3,v10) + (v3[v10] == v10 ? 1 : 0) <= 2*v1-1;
      loop invariant count: 0 <= v7[0] <= 2*v1;
      loop invariant info: v7[1] == 0 && v7[2] == 0;
      loop invariant initialized: \initialized(v6 + (0 .. v7[0]-1));
      loop invariant trace_bounds: \forall integer k; 0 <= k < v7[0] ==> 1 <= v6[k] <= 16 && v6[k] < v1;
      loop invariant target_definition: target_matches{Pre,Here}(v2,v3,v4,v1);
      loop invariant matched: \forall integer j; 0 <= j < v1 ==> v2[j] == v4[v3[j]];
      loop invariant initially_correct_stay_fixed: \forall integer j;
        0 <= j < v10 && \at(v2[j],Pre) == v4[j] ==> v3[j] == j;
      loop invariant far_values: \forall integer j; 0 <= j < v1 && v1-1-j > 16 ==> v2[j] == \at(v2[j],Pre);
      loop invariant trace_replay: \forall integer j; 0 <= j < v1 ==>
        v2[j] == replay_value{Pre,Here}(v2,v6,v1,v7[0],j);
      loop invariant trace_changes_values: \forall integer k; 0 <= k < v7[0] ==>
        replay_value{Pre,Here}(v2,v6,v1,k,v1-1) !=
        replay_value{Pre,Here}(v2,v6,v1,k,v1-1-v6[k]);
      loop assigns v11, v12, v13, v2[0 .. v1-1], v3[0 .. v1-1], v6[0 .. 2*v1-1], v7[0 .. 2];
      loop variant 2*moved(v3,v10) + (v3[v10] == v10 ? 1 : 0);
  */''',
r'''/*@ loop invariant bounds: 0 <= v11 <= v10;
          loop invariant suffix: \forall integer j; v11 < j <= v10 ==> v3[j] == j;
          loop assigns v11;
          loop variant v11;
      */'''
]

# A separate safety pass has no recursive functional definitions. It keeps the
# same input domain. The full functional obligations remain in the full pass.
MEMORY_CONTRACT = CONTRACT[:CONTRACT.index('  predicate target_matches')] + '*/\n\n' + CONTRACT[
    CONTRACT.index('/*@\n  requires size:'):CONTRACT.index('  ensures status:')
] + r'''
  ensures status_range: 0 <= \result <= 2;
  ensures count: 0 <= v7[0] <= 2*v1;
  ensures out_initialized: \initialized(v7 + (0 .. 2));
  ensures data_initialized: \initialized(v2 + (0 .. v1-1));
  ensures permutation_initialized: \initialized(v3 + (0 .. v1-1));
  ensures trace_initialized: \initialized(v6 + (0 .. v7[0]-1));
*/
'''

MEMORY_LOOPS = [
    LOOPS[0],
    r'''/*@ loop invariant bounds: 0 <= v8 <= v1;
      loop invariant initialized: \initialized(v5 + (0 .. v1-1));
      loop invariant filled_initialized: \forall integer i;
        0 <= i < v8 ==> \initialized(v4 + \at(v3[i],Pre));
      loop assigns v8, v9, v4[0 .. v1-1], v5[0 .. v1-1];
      loop variant v1-v8;
  */''',
    r'''/*@ loop invariant bounds: 0 <= v8 <= v1;
      loop invariant target_initialized: \initialized(v4 + (0 .. v1-1));
      loop invariant permutation_initialized: \initialized(v3 + (0 .. v1-1));
      loop invariant used_initialized: \initialized(v5 + (0 .. v1-1));
      loop invariant permutation_bounds: \forall integer j; 0 <= j < v1 ==> v3[j] < v1;
      loop assigns v8, v3[0 .. v1-1], v5[0 .. v1-1];
      loop variant v1-v8;
  */''',
    r'''/*@ loop invariant bounds: 0 <= v8 <= v1;
      loop invariant target_initialized: \initialized(v4 + (0 .. v1-1));
      loop invariant permutation_initialized: \initialized(v3 + (0 .. v1-1));
      loop invariant used_initialized: \initialized(v5 + (0 .. v1-1));
      loop invariant permutation_bounds: \forall integer j; 0 <= j < v1 ==> v3[j] < v1;
      loop assigns v8, v9, v3[0 .. v1-1], v5[0 .. v1-1];
      loop variant v1-v8;
  */''',
    r'''/*@ loop invariant bounds: 0 <= v9 <= v1;
          loop assigns v9;
          loop variant v1-v9;
      */''',
    r'''/*@ loop invariant top: v10 == v1-1;
      loop invariant data_initialized: \initialized(v2 + (0 .. v1-1));
      loop invariant permutation_initialized: \initialized(v3 + (0 .. v1-1));
      loop invariant out_initialized: \initialized(v7 + (0 .. 2));
      loop invariant permutation_bounds: \forall integer j; 0 <= j < v1 ==> v3[j] < v1;
      loop invariant count: 0 <= v7[0] <= 2*v1;
      loop invariant initialized: \initialized(v6 + (0 .. v7[0]-1));
      loop assigns v11, v12, v13, v2[0 .. v1-1], v3[0 .. v1-1], v6[0 .. 2*v1-1], v7[0 .. 2];
  */''',
    r'''/*@ loop invariant bounds: 0 <= v11 <= v10;
          loop assigns v11;
          loop variant v11;
      */'''
]

MEMORY_UNCHANGED = r'''
      loop invariant data_initialized: \initialized(v2 + (0 .. v1-1));
      loop invariant data_unchanged: \forall integer j; 0 <= j < v1 ==> v2[j] == \at(v2[j],Pre);
      loop invariant out_initialized: \initialized(v7 + (0 .. 2));
      loop invariant out_clear: v7[0] == 0 && v7[1] == 0 && v7[2] == 0;
'''
PERMUTATION_EXPLICIT = r'''((\forall integer i; 0 <= i < v1 ==> 0 <= v3[i] < v1) &&
        (\forall integer i,j; 0 <= i < v1 && 0 <= j < v1 && v3[i] == v3[j] ==> i == j) &&
        (\forall integer j; 0 <= j < v1 ==> \exists integer i; 0 <= i < v1 && v3[i] == j))'''
MEMORY_CONTRACT = MEMORY_CONTRACT.replace('permutation(v3,v1)', PERMUTATION_EXPLICIT)
for loop_index in (0, 1, 2, 3):
    MEMORY_LOOPS[loop_index] = MEMORY_LOOPS[loop_index].replace(
        '/*@', '/*@' + MEMORY_UNCHANGED, 1)
for loop_index in (0, 1):
    MEMORY_LOOPS[loop_index] = MEMORY_LOOPS[loop_index].replace(
        '/*@', r'''/*@ loop invariant original_permutation:
        \forall integer j; 0 <= j < v1 ==> v3[j] == \at(v3[j],Pre);
      loop invariant permutation_initialized: \initialized(v3 + (0 .. v1-1));
''', 1)
MEMORY_LOOPS[1] = MEMORY_LOOPS[1].replace('v3[i] == j', r'\at(v3[i],Pre) == j')
MEMORY_LOOPS = [loop.replace('permutation(v3,v1)', PERMUTATION_EXPLICIT)
                for loop in MEMORY_LOOPS]

CUTS = (
    ('      v6[v7[0U]] = v13;', r'''      /*@ assert append_room: v7[0] < 2*v1; */
      /*@ assert append_initialized: \initialized(v6 + (0 .. v7[0]-1)); */
'''),
    ('      v7[0U] = (v7[0U] + 1U);', r'''      /*@ assert append_written: \initialized(v6 + (0 .. v7[0])); */
'''),
    ('    v12 = v3[v11];', r'''    /*@ assert swap_data_initialized: \initialized(v2 + (0 .. v1-1)); */
    /*@ assert swap_permutation_initialized: \initialized(v3 + (0 .. v1-1)); */
    /*@ assert swap_out_initialized: \initialized(v7 + (0 .. 2)); */
    /*@ assert swap_trace_initialized: \initialized(v6 + (0 .. v7[0]-1)); */
    /*@ assert swap_permutation_bounds: \forall integer j; 0 <= j < v1 ==> v3[j] < v1; */
'''),
)

# Select the index at the outer goal access. Searching inside its memory
# term can instead select a constant index from an earlier store.
INITIALIZATION_STRATEGY = r'''/*@
  strategy InitSMT: \prover("CVC5", "Z3", 10.0);
  strategy InstantiateTargetCover:
    \tactic("Wp.instance",
      \when(H: \forall integer j; 0 <= j ==> j < N ==> (\exists integer k; _)),
      \goal(_[shift_uint32(_, J)]), \select(H), \param("P1", J),
      \children(InitSMT));
  proof InstantiateTargetCover: target_initialized;
*/
'''

def strip_comments(source):
    return re.sub(r'/\*.*?\*/', '', source, flags=re.S)


def requirements(source):
    """Return the named function preconditions, including their formulas."""
    contract = re.search(r'/\*@\s*requires size:.*?\*/', source, re.S)
    if contract is None:
        raise ValueError('missing input contract')
    clauses = re.findall(r'\brequires\s+(.*?)(?=\brequires\b|\bterminates\b)', contract[0], re.S)
    return tuple(' '.join(clause.split()) for clause in clauses)


def check_ghosts(source, mode='termination'):
    """Allow only a local counter and two empty snapshot labels.

    The counter reads n once and writes only itself. The two integer-bound
    assertions are proof obligations. No ghost code can change real state.
    """
    actual = [' '.join(code.split()) for code in
              re.findall(r'/\*@\s*ghost\s+(.*?)\*/', source, re.S)]
    expected = {'safety': [], 'target': [],
                'status': ['target_step: ;', 'target_ready: ;', 'normal_start: ;',
                           'proof_fill: ;', 'int proof_steps = 2*v1;',
                           'proof_swap: ;', 'proof_steps--;'],
                'success': ['normal_start: ;', 'proof_fill: ;', 'action_start: ;', 'proof_swap: ;'],
                'termination': ['proof_fill: ;', 'int proof_steps = 2*v1;',
                                'proof_swap: ;', 'proof_steps--;'],
                'trace': ['trace_blocked: ;', 'trace_step: ;', 'trace_perm: ;']}[mode]
    if actual != expected:
        raise ValueError('unexpected ghost code')
    names = ('proof_steps', 'proof_fill', 'proof_swap', 'trace_blocked', 'trace_step',
             'trace_perm', 'target_step', 'target_ready', 'normal_start', 'action_start')
    if re.search(r'\b(?:' + '|'.join(names) + r')\b', strip_comments(source)):
        raise ValueError('ghost name occurs in production C')


def check_components(source, safety, termination):
    tokens = strip_comments(source).split()
    for component in (safety, termination):
        if strip_comments(component).split() != tokens:
            raise ValueError('component C token change')
        if re.search(r'\b(?:axiom|admit|assumes)\s', component):
            raise ValueError('unchecked proof assumption')
    if requirements(safety) != requirements(termination):
        raise ValueError('component input contracts differ')
    check_ghosts(termination)


def annotate(source, mode='full'):
    # The anchors must occur exactly once. This makes an emitter change fail closed.
    anchor = 'unsigned int permute('
    if source.count(anchor) != 1:
        raise SystemExit('function anchor changed')
    if mode in ('status', 'success'):
        # These reviewed annotation snapshots are rejected if any real C token
        # changes. They are proof inputs, never replacement production sources.
        result = Path(__file__).with_name(mode + '.c').read_text()
        if strip_comments(result).split() != strip_comments(source).split():
            raise SystemExit('C token change')
        check_ghosts(result, mode)
        return result
    cuts, after, suffix = CUTS, (), INITIALIZATION_STRATEGY
    if mode == 'full':
        contract, loops = CONTRACT, LOOPS
    elif mode in ('memory', 'safety'):
        contract, loops = MEMORY_CONTRACT, MEMORY_LOOPS
        if mode == 'safety':
            # Partial correctness only. The separate termination component
            # proves termination on the identical input domain and C tokens.
            contract = contract.replace(r'terminates \true;', r'terminates \false;')
    elif mode == 'termination':
        import termination
        library = Path(__file__).with_name('lemmas.acsl').read_text()
        preconditions = MEMORY_CONTRACT.split('/*@\n  requires size:')[1].split('  terminates ')[0]
        contract = library + '\n/*@\n  requires size:' + preconditions + r'  terminates \true;' + '\n*/\n'
        loops, cuts, after = termination.LOOPS, termination.BEFORE, termination.AFTER
        suffix = ''
    elif mode == 'target':
        import target
        contract, loops, suffix = target.specification(
            MEMORY_CONTRACT, MEMORY_LOOPS, CONTRACT, INITIALIZATION_STRATEGY)
        cuts = ()
    elif mode == 'trace':
        import trace_annotations
        library = Path(__file__).with_name('trace.acsl').read_text()
        prefix = MEMORY_CONTRACT.split('  ensures status_range:')[0]
        post = CONTRACT[CONTRACT.index('  ensures trace_bounds:'):]
        contract = library + '\n' + prefix + post
        contract = contract.replace(r'terminates \true;', r'terminates \false;')
        loops, cuts, after = trace_annotations.LOOPS, trace_annotations.BEFORE, trace_annotations.AFTER
        suffix = ''
    else:
        raise ValueError('unknown annotation mode')
    result = source.replace(anchor, contract + anchor)
    pieces = result.split('while (1)')
    if len(pieces) != len(loops) + 1:
        raise SystemExit('loop count changed')
    result = pieces[0] + ''.join(annotation + '\n' + 'while (1)' + tail for annotation,tail in zip(loops,pieces[1:]))
    for anchor, annotations in cuts:
        if result.count(anchor) != 1:
            raise SystemExit('statement anchor changed')
        result = result.replace(anchor, annotations + anchor)
    for anchor, annotations in after:
        if result.count(anchor) != 1:
            raise SystemExit('statement anchor changed')
        result = result.replace(anchor, anchor + '\n' + annotations)
    result += '\n' + suffix
    if strip_comments(result).split() != strip_comments(source).split():
        raise SystemExit('C token change')
    if mode in ('termination', 'trace'):
        check_ghosts(result, mode)
    return result

def main(mode='full'):
    source = SOURCE.read_text()
    result = annotate(source, mode)
    OUT.mkdir(parents=True,exist_ok=True)
    (OUT / 'annotated.c').write_text(result)
    (OUT / 'source.sha256').write_text(hashlib.sha256(source.encode()).hexdigest() + '  permute.c\n')

if __name__ == '__main__':
    main()
