from __future__ import annotations
import importlib.util, json, tempfile, unittest
from pathlib import Path
HERE=Path('/home/argustest')
sp=importlib.util.spec_from_file_location('cert',HERE/'class_independent_terminal_strict_arb.py')
C=importlib.util.module_from_spec(sp);sp.loader.exec_module(C)
W=HERE/'class_independent_terminal_strict_witness.json'

def mutate(fn):
 w=json.loads(W.read_text());fn(w)
 td=tempfile.TemporaryDirectory();p=Path(td.name)/'w.json';p.write_text(json.dumps(w));return td,p

class StrictTerminalTests(unittest.TestCase):
 def test_fixed_witness_passes_above_082(self):
  r=C.run(W);self.assertEqual(r['status'],'PASS');self.assertTrue(r['strict_gt_0p082'])
  self.assertTrue(all(r['checks'].values()))
 def test_source_overload_fails(self):
  td,p=mutate(lambda w:w['prices']['low'].__setitem__(0,'2'))
  try:r=C.run(p)
  finally:td.cleanup()
  self.assertEqual(r['status'],'FAIL');self.assertFalse(r['source_load']['pass'])
 def test_extra_price_family_rejected(self):
  td,p=mutate(lambda w:w['prices'].__setitem__('omitted_column_attack',[]))
  try:
   with self.assertRaises(C.SchemaError):C.load(p)
  finally:td.cleanup()
 def test_boolean_numeric_rejected(self):
  td,p=mutate(lambda w:w.__setitem__('H',True))
  try:
   with self.assertRaises(C.SchemaError):C.load(p)
  finally:td.cleanup()
 def test_closed_seam_and_all_tail_are_reported(self):
  r=C.run(W);self.assertIn('closed finite seam M in [M0,R]',r['coverage'])
  self.assertTrue(r['checks']['remaining_dyadic_tail_floor'])
 def test_positive_primitive_nonnegative(self):
  q=C.positive_integral(C.A('1/100'),C.A('99/100'),C.A('99/100'))
  self.assertTrue(C.positive(q))

if __name__=='__main__':unittest.main()
