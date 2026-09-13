#!/usr/bin/env python3
"""Stable, read-only entry point: seven discovered tests and exact algebra."""
import json
from pathlib import Path
import sys
import unittest

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT))
import verify


def main():
    suite = unittest.defaultTestLoader.discover(str(ROOT), pattern="test_verify.py")
    count = suite.countTestCases()
    verify.require(count > 0, "no tests discovered")
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    if not result.wasSuccessful():
        return 1
    receipt = verify.verify_all()
    receipt["tests_run"] = result.testsRun
    print(json.dumps(receipt, sort_keys=True, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
