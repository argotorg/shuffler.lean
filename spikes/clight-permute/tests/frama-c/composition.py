# SPDX-License-Identifier: GPL-3.0-or-later
"""Check the premises for conjoining the six source-C proofs.

Each component proves its own annotations. No component assumes a claim
from another component. The input contract and real C must be identical.
"""
import re
import annotate

MODES = ('safety', 'termination', 'target', 'trace', 'status', 'success')
GUARDED = {
    'success_reachable': r'\result == 0 ==> values_reachable{Pre}(v2,v3,v1);',
    'blocked_unreachable': r'\result == 1 ==> !values_reachable{Pre}(v2,v3,v1);',
}
IFF_LEMMA = r'''lemma guarded_success_iff{Input}:
    \forall unsigned int *d,*p, integer n,result;
      0 <= result <= 1 &&
      (result == 0 ==> values_reachable{Input}(d,p,n)) &&
      (result == 1 ==> !values_reachable{Input}(d,p,n)) ==>
      ((result == 0) <==> values_reachable{Input}(d,p,n));'''


def normalized(text):
    return tuple(re.findall(r'\\[a-zA-Z_]+|[a-zA-Z_][a-zA-Z_0-9]*|[0-9]+|[^\s]', text))


def function_contract(source):
    contracts = re.findall(r'/\*@\s*requires\b.*?\*/', source, re.S)
    if len(contracts) != 1:
        raise ValueError('missing or extra input contract')
    return contracts[0]


def postconditions(source):
    clauses = re.findall(r'\bensures\s+(\w+):\s*(.*?)(?=\bensures\b|\*/)',
                         function_contract(source), re.S)
    if len({name for name, _ in clauses}) != len(clauses):
        raise ValueError('duplicate postcondition')
    return {name: normalized(body) for name, body in clauses}


def definition(source, name):
    pattern = (r'\b(?:predicate|logic integer)\s+' + re.escape(name)
               + r'\b.*?(?=\s*(?:predicate\b|logic integer\b|(?:check\s+)?lemma\b|}\s*\*/|\*/))')
    definitions = re.findall(pattern, source, re.S)
    if len(definitions) != 1:
        raise ValueError('missing or duplicate definition: ' + name)
    return normalized(definitions[0])


def check_sources(original, parts):
    expected_inputs = annotate.requirements(annotate.MEMORY_CONTRACT)
    tokens = annotate.strip_comments(original).split()
    for mode, source in parts.items():
        if annotate.strip_comments(source).split() != tokens:
            raise ValueError(mode + ': C token change')
        if re.search(r'\b(?:axiom|admit|assumes)\s', source):
            raise ValueError(mode + ': unchecked proof assumption')
        function_contract(source)
        if annotate.requirements(source) != expected_inputs:
            raise ValueError(mode + ': input contracts differ')
        annotate.check_ghosts(source, mode)
        expected_termination = r'\true' if mode in ('termination', 'status') else r'\false'
        if re.findall(r'\bterminates\s+(.*?);', function_contract(source)) != [expected_termination]:
            raise ValueError(mode + ': termination clause differs')


def check(original, parts):
    if set(parts) != set(MODES):
        raise ValueError('missing or extra component')
    check_sources(original, parts)
    # The component precondition expands the full contract's permutation
    # predicate. Check that expansion against its actual definition.
    permutation = definition(annotate.CONTRACT, 'permutation')
    body = permutation[permutation.index('=') + 1:-1]
    expanded = '(' + ' '.join({'p': 'v3', 'n': 'v1'}.get(token, token)
                              for token in body) + ')'
    full_inputs = annotate.CONTRACT.replace('permutation(v3,v1)', expanded)
    if tuple(map(normalized, annotate.requirements(full_inputs))) != tuple(
            map(normalized, annotate.requirements(annotate.MEMORY_CONTRACT))):
        raise ValueError('full input contract differs from component input contracts')
    for mode, names in {'target': ('target_matches',),
                        'trace': ('replay_value',),
                        'success': ('target_matches', 'values_reachable')}.items():
        for name in names:
            if definition(parts[mode], name) != definition(annotate.CONTRACT, name):
                raise ValueError(mode + ': changed definition: ' + name)
    full = postconditions(annotate.CONTRACT)
    if full.get('success_iff') != normalized(
            r'(\result == 0) <==> values_reachable{Pre}(v2,v3,v1);'):
        raise ValueError('changed full equivalence clause')
    component_posts = {mode: postconditions(source) for mode, source in parts.items()}
    coverage = {}
    for name, clause in full.items():
        if name == 'success_iff':
            continue
        modes = [mode for mode, clauses in component_posts.items() if clauses.get(name) == clause]
        if not modes:
            raise ValueError('missing or changed postcondition: ' + name)
        coverage[name] = modes
    for name, body in GUARDED.items():
        if component_posts['success'].get(name) != normalized(body):
            raise ValueError('missing or changed guarded postcondition: ' + name)
    if normalized(IFF_LEMMA) not in tuple(
            normalized(clause) for clause in re.findall(
                r'\blemma guarded_success_iff\{.*?;\s*(?=}\s*\*/|\*/)', parts['success'], re.S)):
        raise ValueError('missing or changed success composition lemma')
    coverage['success_iff'] = ['status', 'success', 'guarded_success_iff']
    assigns = re.search(r'\bassigns\s+(.*?);', function_contract(annotate.CONTRACT), re.S)
    safety_assigns = re.search(r'\bassigns\s+(.*?);', function_contract(parts['safety']), re.S)
    if safety_assigns is None or normalized(assigns[1]) != normalized(safety_assigns[1]):
        raise ValueError('changed function assigns clause')
    return coverage
