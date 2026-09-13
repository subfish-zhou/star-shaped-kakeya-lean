"""Run focused tests and the frozen arithmetic; write only deterministic stdout."""
import io
import sys
import unittest
from pathlib import Path
import verifier as v


def main():
    suite = unittest.defaultTestLoader.discover(str(Path(__file__).parent), 'test_verifier.py')
    log = io.StringIO()
    result = unittest.TextTestRunner(stream=log).run(suite)
    if result.testsRun != 7 or not result.wasSuccessful():
        sys.stderr.write(log.getvalue())
        raise SystemExit('focused tests failed or discovery changed')
    data = v.load()
    table = v.rows(data)
    values = v.receipts(data)
    v.certify(values)
    print('PASS: 7 focused tests')
    print('PASS: 7 fixed rows; exact maximum source load = ' + str(v.source_load(table)))
    print('Arb precision: ' + str(v.ctx.prec) + ' bits')
    for branch in v.BRANCHES:
        print('PASS: ' + branch + ' > ' + data['target'])
    print('Paper + outward arithmetic only; no Lean claim.')


if __name__ == '__main__':
    main()
