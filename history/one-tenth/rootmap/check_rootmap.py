#!/usr/bin/env python3
"""Exact, standard-library-only candidate inclusion replay; no old code imports.

Default checks committed candidate bytes without writes. --provenance additionally
reads the explicitly pinned original files. No producers, ranking or solvers run.
The universal implication is proved in README.md, not inferred from point tests.
"""
from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations, product
from pathlib import Path
import argparse
import hashlib
import json

HERE = Path(__file__).resolve().parent
FIXTURE_SHA256 = 'cf7fd217829d9d00004f442533260add70ac55564ea0589411ca598487cb1b42'
OLD = ('R000', 'R001', 'R002', 'R003', 'R005', 'R008', 'R009')
PAIRS = tuple(combinations(range(5), 2))
PATHS = (('C01', (0,)),) + tuple((f'D{i}{j}', tuple(range(i+1, j+1))) for i, j in PAIRS)
ADJACENT = ('C01', 'D01', 'D12', 'D23', 'D34')
D, U, HMAX = F(3, 7), F(7, 3), F(1, 5)


def need(condition, message):
    if not condition:
        raise ValueError(message)


def feasible(n, states):
    """Independent Floyd-Warshall closure of source constraints, scaled by six.

    n<=5; every simple strict cycle has <=5 edges and integral unperturbed
    weight. epsilon=1/6 therefore preserves strict feasibility (README).
    """
    bounds = [[None] * n for _ in range(n)]
    for i in range(n):
        bounds[i][i] = 0
    def edge(i, j, w):
        if bounds[i][j] is None or w < bounds[i][j]:
            bounds[i][j] = w
    for i in range(n-1):
        edge(i+1, i, -1)
    for (i, j), state in zip(combinations(range(n), 2), states):
        if state == 0:
            edge(i, j, 5)
        elif state == 1:
            edge(j, i, -7)
            edge(i, j, 11)
        elif state == 2:
            edge(j, i, -13)
        else:
            raise ValueError('invalid state')
    for k in range(n):
        for i in range(n):
            if bounds[i][k] is None:
                continue
            for j in range(n):
                if bounds[k][j] is not None:
                    edge(i, j, bounds[i][k] + bounds[k][j])
        if any(bounds[i][i] < 0 for i in range(n)):
            return False
    return True


def reflect(signature):
    table = dict(zip(PAIRS, signature))
    return tuple(table[(4-j, 4-i)] for i, j in PAIRS)


@lru_cache(maxsize=1)
def universe():
    c2 = [s for s in product(range(3), repeat=1) if feasible(2, s)]
    c5 = [s for s in product(range(3), repeat=10) if feasible(5, s)]
    quotient = {min(s, reflect(s)) for s in c5}
    need((len(c2), len(c5), len(quotient)) == (3, 273, 147), 'census drift')
    return frozenset((a, b) for a in c2 for b in quotient)


def parse_fixture(text):
    lines = text.splitlines()
    need(lines and lines[0] == 'root_id\tC2\tC5', 'fixture header')
    rows = {}
    for line in lines[1:]:
        rid, a, b = line.split('\t')
        need(rid not in rows, 'duplicate root')
        need(len(a) == 1 and len(b) == 10 and set(a+b) <= set('012'), 'signature format')
        rows[rid] = (tuple(map(int, a)), tuple(map(int, b)))
    need(list(rows) == [f'R{i:03d}' for i in range(441)], 'omitted/reordered root')
    need(len(set(rows.values())) == 441 and set(rows.values()) == universe(), 'signature universe mismatch')
    return rows


def load_fixture():
    data = (HERE / 'production_ids.tsv').read_bytes()
    need(hashlib.sha256(data).hexdigest() == FIXTURE_SHA256, 'frozen ID binding changed')
    return parse_fixture(data.decode('ascii'))


def prod_ri(qs):
    r, i = F(1), F(0)
    for q in qs:
        r, i = r-i*q, i+r*q
    return r, i


def support_values(qs, h):
    r, i = prod_ri(qs)
    return r, i, 2*i*r-2*h*(r*r-i*i), i-2*h*r


def weak_state(state, a, b):
    if state == 0:
        return a <= 0
    if state == 1:
        return a >= 0 and b <= 0
    if state == 2:
        return b >= 0
    raise ValueError('invalid state')


def cube(z):
    need(len(z) == 7 and all(0 <= x <= 1 for x in z), 'outside cube')
    return tuple(D*x for x in z[:5]) + (D+F(40, 21)*z[5],), z[6]/5


def closing_gap(free):
    need(len(free) == 6 and all(0 <= q <= D for q in free[:5]) and D <= free[5] <= U,
         'outside production gap box')
    r, i = prod_ri(free)
    need(i >= 0 and 7*r-3*i >= 0 and 7*i-3*r >= 0, 'closure cone')
    need(i > 0 and r > 0, 'norm/cone denominator consequence')
    qR = r/i
    need(D <= qR <= U, 'closing separator bounds')
    rr, ii = prod_ri(tuple(free)+(qR,))
    need(rr == 0 and ii == (r*r+i*i)/i > 0, 'closure algebra')
    return qR


def carrier_point(signature, free, h):
    """All-support weak supercarrier, omitting only restrictions (see proof).

    This exact point predicate is used for regression, not a universal proof.
    Direction-word guards and pair-denominator guards of native refinements
    only shrink this set and are deliberately unnecessary for the inclusion.
    """
    if not 0 <= h <= HMAX:
        return False
    try:
        closing_gap(free)
    except ValueError:
        return False
    return all(weak_state(state, *support_values([free[k] for k in path], h)[2:])
               for (_, path), state in zip(PATHS, signature[0]+signature[1]))


def theorem_point(signature, free, h):
    qR = closing_gap(free)
    states = dict(zip((p for p, _ in PATHS), signature[0]+signature[1]))
    short = [free[k] for k, name in enumerate(ADJACENT) if states[name] != 2]
    long = [free[k] for k, name in enumerate(ADJACENT) if states[name] == 2] + [free[5], qR]
    return (0 <= h <= HMAX and len(short) == 2 and len(long) == 5 and
            all(0 <= q <= 2*h for q in short) and all(2*h <= q <= U for q in long)
            and free[5] >= D and qR >= D)


def guard_contract():
    return {
        'coordinates': 'qC,q1,q2,q3,q4=(3/7)z; qL=3/7+(40/21)zL; h=zh/5; z in [0,1]^7',
        'cycle': 'C0-qC-C1-qL-D0-q1-D1-q2-D2-q3-D3-q4-D4-qR-C0',
        'product': '(R,I)=(1,0); (R,I)<-(R-I*q,I+R*q)',
        'closure_nonnegative': ['I_free', '7*R_free-3*I_free', '7*I_free-3*R_free'],
        'closing_gap': 'qR=R_free/I_free',
        'A': '2*I*R-2*h*(R*R-I*I)',
        'B': 'I-2*h*R',
        'weak_states': {'0': 'A<=0', '1': 'A>=0 and B<=0', '2': 'B>=0'},
        'all_support_paths_free_indices': {name: list(path) for name, path in PATHS},
        'adjacent_state0_identity': 'A/2-B=h*(1+q*q)',
        'native_extra_guards_not_needed': [
            'Each direction word restricts P=7*I_J-3*R_J by a weak sign.',
            'Native pair domain R_J>0,R_J^2-I_J^2>0, or its weak closure, only restricts the supercarrier.'
        ],
        'inclusion': 'Each actual physical root closure and each native guarded refinement is contained in the all-support weak supercarrier; no equality or native carrier enumeration is claimed.'
    }


def build_candidate():
    rows = load_fixture()
    selected = []
    old_by_rule = []
    for rid, signature in rows.items():
        states = dict(zip((p for p, _ in PATHS), signature[0]+signature[1]))
        shorts = [p for p in ADJACENT if states[p] != 2]
        if len(shorts) <= 1:
            old_by_rule.append(rid)
        if len(shorts) != 2:
            continue
        reflected = signature[0]+reflect(signature[1])
        reflected_states = dict(zip((p for p, _ in PATHS), reflected))
        need(sum(reflected_states[p] != 2 for p in ADJACENT) == 2, 'reflection lost two-short property')
        selected.append({'root_id': rid, 'C2': ''.join(map(str, signature[0])),
                         'C5': ''.join(map(str, signature[1])), 'short_paths': shorts,
                         'reflected_short_paths': [p for p in ADJACENT if reflected_states[p] != 2]})
    ids = [r['root_id'] for r in selected]
    need(tuple(old_by_rule) == OLD, 'old seven signature cohort changed')
    need(len(ids) == 27 and not set(ids).intersection(OLD), 'two-short cohort drift')
    combined = sorted(set(OLD).union(ids))
    complement = [rid for rid in rows if rid not in combined]
    need(len(combined) == 34 and len(complement) == 407, 'conditional partition drift')
    return {
        'schema': 'two-short-whole-carrier-candidate-v1',
        'status': 'CANDIDATE_WHOLE_CARRIER_INCLUSION_AWAITING_PARENT_AUDIT',
        'promotion_authorized': False,
        'new_fully_certified_production_roots': [],
        'preserved_old_certified_roots_not_reaudited': list(OLD),
        'enumeration': {'C2': 3, 'oriented_C5': 273, 'reflection_C5': 147, 'production': 441},
        'id_binding': {'fixture': 'production_ids.tsv', 'sha256': FIXTURE_SHA256,
                       'meaning': 'Frozen production names; exact signature universe independently regenerated; historical floating ranking not rerun.'},
        'guard_contract': guard_contract(),
        'candidate_root_ids': ids,
        'candidate_roots': selected,
        'conditional_old_plus_candidate_ids': combined,
        'ordered_conditional_complement': complement,
        'ordered_current_unpromoted_complement': [rid for rid in rows if rid not in OLD],
        'counts': {'candidate_only': len(ids), 'old_preserved': len(OLD),
                   'conditional_total_if_accepted': len(combined), 'conditional_complement': len(complement),
                   'current_unpromoted': len(rows)-len(OLD), 'new_promotions': 0},
        'four_lower_faces': {'historically_reported': 23, 'recounted_here': False,
                             'status': 'EMPTY_IN_TRUE_C2_PLUS_C5', 'new_root_coverage': 0},
        'conditional_on': ['Accepted restricted separator theorem in the two pinned audit Markdown files.',
                           'Frozen production ID lookup; not a fresh floating ranking.',
                           'Parent independent review of the root-to-domain proof before any count promotion.']
    }


def validate_candidate(candidate, expected=None):
    need(candidate == (build_candidate() if expected is None else expected), 'candidate/guard/root/status drift')


def check_provenance():
    p = json.loads((HERE/'provenance.json').read_text())
    need(p['runtime_old_source_dependencies'] == [] and p['fixture_sha256'] == FIXTURE_SHA256,
         'provenance contract drift')
    for row in p['sources']:
        need(hashlib.sha256(Path(row['path']).read_bytes()).hexdigest() == row['sha256'],
             'original source hash drift: '+row['path'])
    # Check the frozen data slice rather than executing either old producer.
    census = json.loads(Path('/home/argustest/c2c5_441_long_gap_census_lane1.json').read_text())
    source_map = {r['root_id']: (tuple(r['generic_signature']['C2']), tuple(r['generic_signature']['C5']))
                  for r in census['rows']}
    need(source_map == load_fixture(), 'fixture does not equal frozen source lookup')
    classification = json.loads(Path('/home/argustest/c2c5_two_short_structural_classification.json').read_text())
    need(classification['root_ids'] == build_candidate()['candidate_root_ids'], 'historical classification mismatch')
    return len(p['sources'])


def encoded(candidate):
    return json.dumps(candidate, indent=2, sort_keys=True)+'\n'


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--emit', action='store_true', help='print candidate JSON to stdout, never write')
    ap.add_argument('--provenance', action='store_true', help='also hash explicitly pinned read-only originals')
    args = ap.parse_args()
    candidate = build_candidate()
    if args.emit:
        print(encoded(candidate), end='')
        return
    data = (HERE/'candidate.json').read_text()
    validate_candidate(json.loads(data), candidate)
    need(data == encoded(candidate), 'candidate bytes drift')
    sources = check_provenance() if args.provenance else 0
    print('PASS_EXACT_ROOTMAP_CANDIDATE roots=441 candidates=27 old=7 conditional=34 complement=407 new_promotions=0')
    print('candidate_sha256='+hashlib.sha256(data.encode()).hexdigest()+' original_hashes_checked='+str(sources))


if __name__ == '__main__':
    main()
