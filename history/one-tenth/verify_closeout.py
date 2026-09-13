#!/usr/bin/env python3
"""Check reviewed closeout accounting, not the handwritten geometric proofs."""
import hashlib
import json
from pathlib import Path
from rootmap.check_rootmap import build_candidate, validate_candidate

ROOT = Path(__file__).resolve().parent
COMMITS = {
    'baseline': '69ceb8881cf3bf621afb5e1d58ec3d1214369abd',
    'separator': '9b185ea96750d53fdbad42b79225bf073ee01346',
    'rootmap': 'cd8779e0bdb82f19bf8ed7c4fd2e162094c070c5',
}


def validate(data):
    c = build_candidate()
    validate_candidate(json.loads((ROOT / 'rootmap/candidate.json').read_text()), c)
    old, new = c['preserved_old_certified_roots_not_reaudited'], c['candidate_root_ids']
    combined = sorted(set(old) | set(new))
    remainder = c['ordered_conditional_complement']
    if set(old) & set(new) or set(combined) & set(remainder):
        raise ValueError('overlapping root accounting')
    if sorted(combined + remainder) != [f'R{i:03d}' for i in range(441)]:
        raise ValueError('incomplete root accounting')
    files = {}
    for folder in (*COMMITS, 'reviews'):
        for path in sorted((ROOT / folder).rglob('*')):
            if path.is_symlink():
                raise ValueError('unexpected symlink in reviewed subtree')
            if path.is_file():
                files[str(path.relative_to(ROOT))] = hashlib.sha256(path.read_bytes()).hexdigest()
    expected = {
        'schema': 'one-tenth-short-closeout-v1',
        'status': 'ACCEPTED_SCOPED_CLOSEOUT',
        'scope': 'centered common-height C2+C5 historical production root closures only',
        'universal_lower_bound': '0.082812499999972190',
        'universal_0p1_proved': False,
        'arbitrary_N7_proved': False,
        'old_roots_inherited': old,
        'new_roots': new,
        'certified_roots': combined,
        'residual_roots': remainder,
        'reviewed_commits': COMMITS,
        'audited_files': files,
    }
    if data != expected or data['universal_0p1_proved'] is not False or data['arbitrary_N7_proved'] is not False:
        raise ValueError('closeout scope, IDs, reviewed identity or byte binding mismatch')


if __name__ == '__main__':
    validate(json.loads((ROOT / 'closeout.json').read_text()))
    print('PASS_SCOPED_CLOSEOUT certified=34 residual=407; continuum 0.1 unproved')
