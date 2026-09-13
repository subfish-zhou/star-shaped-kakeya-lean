"""Stdlib unit/mutation tests. Fake compilers only: no Lean compilation or Git writes."""
import importlib.util
from contextlib import redirect_stdout, redirect_stderr
import io
import json
import subprocess
import os
from pathlib import Path
import tempfile
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parent


def load_builder():
    spec = importlib.util.spec_from_file_location('artifact_build', ROOT / 'build.py')
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


class ImportContract(unittest.TestCase):
    def test_import_needs_no_environment_or_io(self):
        # Pre-read/compile so importlib's own source IO is outside the sentinel.
        code = compile((ROOT / 'build.py').read_bytes(), str(ROOT / 'build.py'), 'exec')
        with mock.patch.dict(os.environ, {}, clear=True), \
                mock.patch.object(Path, 'resolve', side_effect=AssertionError('import IO')), \
                mock.patch.object(Path, 'mkdir', side_effect=AssertionError('import IO')), \
                mock.patch.object(Path, 'read_text', side_effect=AssertionError('import IO')), \
                mock.patch('subprocess.run', side_effect=AssertionError('import subprocess')):
            exec(code, {'__name__': 'import_contract', '__file__': str(ROOT / 'build.py')})


class GraphContract(unittest.TestCase):
    def setUp(self):
        self.build = load_builder()
        self.temp = tempfile.TemporaryDirectory(prefix='kakeya-graph-test-')
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)

    def source(self, name, text=''):
        path = self.root / (name.replace('.', '/') + '.lean')
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
        return path

    def graph(self):
        return self.build.resolve_graph(self.root, ('StarKakeyaLower.A',))

    def test_missing_local_import(self):
        self.source('StarKakeyaLower.A', 'import StarKakeyaLower.Missing\n')
        with self.assertRaisesRegex(RuntimeError, 'missing local'):
            self.graph()

    def test_cycle(self):
        self.source('StarKakeyaLower.A', 'import StarKakeyaLower.B\n')
        self.source('StarKakeyaLower.B', 'import StarKakeyaLower.A\n')
        with self.assertRaisesRegex(RuntimeError, 'cycle'):
            self.graph()

    def test_unsupported_imports(self):
        for text in ('import StarKakeyaLower.B Mathlib\n', 'public import Mathlib\n',
                     'meta import Mathlib\n', 'import\n  Mathlib\n', 'prelude\n',
                     'module\n', 'def x := 1\nimport Mathlib\n', 'import «Mathlib»\n',
                     'import Mathlib "ignored suffix"\n'):
            with self.subTest(text=text):
                self.source('StarKakeyaLower.A', text)
                with self.assertRaisesRegex(RuntimeError, 'unsupported'):
                    self.graph()

    def test_uncovered_public_module(self):
        self.source('StarKakeyaLower.A')
        self.source('Stray')
        with self.assertRaisesRegex(RuntimeError, 'uncovered'):
            self.graph()

    def test_topological_order_and_comments(self):
        self.source('StarKakeyaLower.A', '/- import Fake\n /- nested -/ -/\n'
                    'import StarKakeyaLower.B -- comment\n'
                    'def text := "import NotAModule"\n')
        self.source('StarKakeyaLower.B', 'import Mathlib\n')
        sources, imports, order = self.graph()
        self.assertEqual(order, ['StarKakeyaLower.B', 'StarKakeyaLower.A'])
        self.assertEqual(imports['StarKakeyaLower.B'], ['Mathlib'])
        self.assertEqual(set(sources), set(order))

    def test_symlink_source_directory_is_not_silently_omitted(self):
        self.source('StarKakeyaLower.A')
        external = self.root.parent / (self.root.name + '-linked')
        external.mkdir()
        self.addCleanup(external.rmdir)
        (self.root / 'Linked').symlink_to(external, target_is_directory=True)
        with self.assertRaisesRegex(RuntimeError, 'symlink'):
            self.graph()

    def test_duplicate_module_paths_rejected(self):
        self.source('StarKakeyaLower.A')
        (self.root / 'StarKakeyaLower.A.lean').write_text('')
        with self.assertRaisesRegex(RuntimeError, 'duplicate'):
            self.graph()

    def test_actual_default_public_graph_covers_44_sources(self):
        sources, imports, order = self.build.resolve_graph(ROOT)
        self.assertEqual(len(order), 44)
        self.assertEqual(set(sources), set(order))
        for name in order:
            for dep in imports[name]:
                if dep in sources:
                    self.assertLess(order.index(dep), order.index(name))


class FixtureCase(unittest.TestCase):
    def setUp(self):
        self.build = load_builder()
        self.temp = tempfile.TemporaryDirectory(prefix='kakeya-config-test-')
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name) / 'project'
        self.root.mkdir()
        self.lock = json.loads((ROOT / 'dependencies.lock.json').read_text())
        for filename in ('dependencies.lock.json', 'lake-manifest.json'):
            self.write_json(self.root / filename, self.lock)
        self.pin = 'leanprover/lean4:v4.30.0-rc2'
        (self.root / 'lean-toolchain').write_text(self.pin)
        self.sysroot = Path(self.temp.name) / 'toolchain'
        (self.sysroot / 'bin').mkdir(parents=True)
        (self.sysroot / 'bin/lean').write_text('fake compiler, NEVER executed')
        (self.sysroot / 'bin/lean').chmod(0o755)
        (self.sysroot / 'lib/lean').mkdir(parents=True)
        (self.sysroot / 'lib/lean/Init.olean').write_bytes(b'fake Init')
        for package in self.lock['packages']:
            source = self.root / '.lake/packages' / package['name']
            (source / '.lake/build/lib/lean').mkdir(parents=True)
            (source / 'lean-toolchain').write_text(self.pin)
            manifest = dict(self.lock, packages=(self.lock['packages'][1:]
                                                if package['name'] == 'mathlib' else []))
            self.write_json(source / 'lake-manifest.json', manifest)
        self.mathlib = self.root / '.lake/packages/mathlib'
        (self.mathlib / '.lake/build/lib/lean/Mathlib.olean').write_bytes(b'fake Mathlib')
        self.env = {'KAKEYA_LEAN_SYSROOT': str(self.sysroot), 'PATH': '/usr/bin:/bin'}
        self.version = ('Lean (version 4.30.0-rc2, x86_64-unknown-linux-gnu, commit '
                        '3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc, Release)')
        self.calls = []
        patcher = mock.patch.object(self.build.subprocess, 'run', side_effect=self.probe)
        patcher.start()
        self.addCleanup(patcher.stop)

    def write_json(self, path, value):
        path.write_text(json.dumps(value))

    def probe(self, command, **kwargs):
        self.calls.append((command, kwargs))
        if command[0] == 'git':
            source = Path(command[2])
            args = command[3:]
            if args == ['rev-parse', 'HEAD']:
                output = next(p['rev'] for p in self.lock['packages'] if p['name'] == source.name)
            elif args == ['status', '--porcelain', '--untracked-files=all']:
                output = ''
            elif args == ['show', 'HEAD:lake-manifest.json']:
                output = (source / 'lake-manifest.json').read_text()
            else:
                self.fail('unexpected Git query: ' + repr(args))
        elif command == [str(self.sysroot / 'bin/lean'), '--version']:
            output = self.version
        elif command == [str(self.sysroot / 'bin/lean'), '--print-prefix']:
            output = str(self.sysroot)
        else:
            self.fail('unexpected subprocess (proof compilation forbidden): ' + repr(command))
        return subprocess.CompletedProcess(command, 0, output + '\n', '')

    def config(self):
        return self.build.configure(self.root, self.env)

class ConfigurationContract(FixtureCase):
    def test_optional_donor_is_read_only_and_not_project_object_path(self):
        donor = Path(self.temp.name) / 'donor'
        donor.mkdir()
        for filename in ('lean-toolchain', 'lake-manifest.json'):
            (donor / filename).write_bytes((self.root / filename).read_bytes())
        (self.root / '.lake').rename(donor / '.lake')
        self.env['KAKEYA_DEPENDENCIES'] = str(donor)
        before = {p: p.read_bytes() for p in donor.rglob('*') if p.is_file()}
        config = self.config()
        self.assertEqual(config['donor'], donor)
        self.assertEqual(before, {p: p.read_bytes() for p in donor.rglob('*') if p.is_file()})
        self.assertNotIn(donor / '.lake/build/lib/lean', config['paths'])

    def test_unused_cli_package_does_not_require_unfetched_objects(self):
        # The real upstream Mathlib cache does not ship unused Cli objects.
        (self.root / '.lake/packages/Cli/.lake/build/lib/lean').rmdir()
        self.assertEqual(len(self.config()['report']['packages']), 9)

    def test_missing_required_mathlib_object_still_fails(self):
        (self.mathlib / '.lake/build/lib/lean/Mathlib.olean').unlink()
        with self.assertRaisesRegex(RuntimeError, 'Mathlib.olean'):
            self.config()

    def test_default_local_donor_and_read_only_config(self):
        before = set(self.root.rglob('*'))
        config = self.config()
        self.assertEqual(config['donor'], self.root)
        self.assertEqual(len(config['report']['packages']), 9)
        self.assertEqual(set(self.root.rglob('*')), before)
        self.assertFalse((self.root / '.closeout-build').exists())
        self.assertTrue(any(cmd[-1] == '--version' for cmd, _ in self.calls))
        for cmd, kwargs in self.calls:
            if cmd[0] == 'git':
                self.assertEqual(kwargs['env']['GIT_OPTIONAL_LOCKS'], '0')
                self.assertEqual(kwargs['env']['GIT_NO_LAZY_FETCH'], '1')

    def test_wrong_dependency_pin(self):
        for filename in ('dependencies.lock.json', 'lake-manifest.json'):
            for index, package in enumerate(self.lock['packages']):
                with self.subTest(filename=filename, package=package['name']):
                    altered = json.loads(json.dumps(self.lock))
                    altered['packages'][index]['rev'] = '0' * 40
                    self.write_json(self.root / filename, altered)
                    with self.assertRaisesRegex(RuntimeError, 'dependency'):
                        self.config()
                    self.write_json(self.root / filename, self.lock)

    def test_lock_and_manifest_cannot_jointly_change_accepted_pins(self):
        altered = json.loads(json.dumps(self.lock))
        altered['packages'][0]['rev'] = '0' * 40
        for filename in ('dependencies.lock.json', 'lake-manifest.json'):
            self.write_json(self.root / filename, altered)
        with self.assertRaisesRegex(RuntimeError, 'dependency'):
            self.config()

    def test_duplicate_dependency_pin(self):
        altered = dict(self.lock, packages=self.lock['packages'] + [self.lock['packages'][0]])
        self.write_json(self.root / 'lake-manifest.json', altered)
        with self.assertRaisesRegex(RuntimeError, 'dependency'):
            self.config()

    def test_wrong_toolchain(self):
        for path in (self.root / 'lean-toolchain', self.mathlib / 'lean-toolchain'):
            with self.subTest(path=path):
                path.write_text('leanprover/lean4:v4.30.0')
                with self.assertRaisesRegex(RuntimeError, 'toolchain'):
                    self.config()
                path.write_text(self.pin)

    def test_pinned_transitive_package_may_declare_older_upstream_toolchain(self):
        # This is the real pinned LeanSearchClient metadata, not our selected compiler.
        package = self.root / '.lake/packages/LeanSearchClient'
        (package / 'lean-toolchain').write_text('leanprover/lean4:v4.27.0-rc1')
        self.assertEqual(len(self.config()['report']['packages']), 9)

    def test_wrong_actual_compiler_version_and_commit(self):
        good = self.version
        for wrong in (good.replace('rc2', 'rc1'), good.replace('3dc1a088', '00000000')):
            with self.subTest(version=wrong):
                self.version = wrong
                with self.assertRaisesRegex(RuntimeError, 'compiler'):
                    self.config()

    def test_wrong_head_and_dirty_package(self):
        real_probe = self.probe
        for package in self.lock['packages']:
            for query, output in (('rev-parse', '0' * 40), ('status', ' M lake-manifest.json')):
                def altered(command, **kwargs):
                    if command[0] == 'git' and command[3] == query and Path(command[2]).name == package['name']:
                        return subprocess.CompletedProcess(command, 0, output, '')
                    return real_probe(command, **kwargs)
                with self.subTest(query=query, package=package['name']), \
                        mock.patch.object(self.build.subprocess, 'run', side_effect=altered):
                    with self.assertRaisesRegex(RuntimeError, 'dependency'):
                        self.config()

    def test_manifest_must_match_head_even_when_status_claims_clean(self):
        real_probe = self.probe
        def altered(command, **kwargs):
            if command[0] == 'git' and command[3] == 'show':
                return subprocess.CompletedProcess(command, 0, '{}', '')
            return real_probe(command, **kwargs)
        with mock.patch.object(self.build.subprocess, 'run', side_effect=altered):
            with self.assertRaisesRegex(RuntimeError, 'manifest differs from HEAD'):
                self.config()

    def test_nested_dependency_manifest_mismatch(self):
        manifest = json.loads((self.mathlib / 'lake-manifest.json').read_text())
        manifest['packages'][0]['rev'] = '0' * 40
        self.write_json(self.mathlib / 'lake-manifest.json', manifest)
        with self.assertRaisesRegex(RuntimeError, 'dependency'):
            self.config()

    def test_exact_installed_elan_toolchain_without_installer(self):
        self.env.pop('KAKEYA_LEAN_SYSROOT')
        self.env['ELAN_HOME'] = str(Path(self.temp.name) / 'elan')
        installed = Path(self.env['ELAN_HOME']) / 'toolchains/leanprover--lean4---v4.30.0-rc2'
        installed.parent.mkdir(parents=True)
        self.sysroot.rename(installed)
        self.sysroot = installed
        self.assertEqual(self.config()['sysroot'], installed)
        self.assertFalse(any('elan' == Path(cmd[0]).name for cmd, _ in self.calls))

    def test_missing_toolchain_no_fallback(self):
        self.env['KAKEYA_LEAN_SYSROOT'] = str(self.sysroot / 'absent')
        with self.assertRaisesRegex(RuntimeError, 'compiler|sysroot'):
            self.config()
        self.assertFalse(any(cmd[0] != 'git' for cmd, _ in self.calls))


class BuildContract(FixtureCase):
    def setUp(self):
        super().setUp()
        directory = self.root / 'StarKakeyaLower'
        directory.mkdir()
        (directory / 'Base.lean').write_text('import Mathlib\n')
        for name in ('OneTenthAudit', 'OneTenthParentAudit'):
            (directory / (name + '.lean')).write_text('import StarKakeyaLower.Base\n')
        self.compiled = []
        self.child_exit = 0
        self.after_compile = lambda: None

    def probe(self, command, **kwargs):
        if '-o' not in command:
            return super().probe(command, **kwargs)
        self.assertEqual(command[0], str(self.sysroot / 'bin/lean'))
        self.assertIn('-j2', command)
        # A second lease must fail while each mocked compiler is running.
        import fcntl
        with (self.root / '.closeout-build/compile.lock').open('a') as lease:
            with self.assertRaises(BlockingIOError):
                fcntl.flock(lease.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
        output = Path(command[command.index('-o') + 1])
        self.assertFalse(output.exists(), 'no stale object reuse')
        output.write_bytes(b'fake object: ' + Path(command[-1]).read_bytes())
        kwargs['stdout'].write('fake compiler log\n')
        self.assertEqual(kwargs['env']['LEAN_PATH'].split(os.pathsep)[0],
                         str(output.parents[1]))
        self.compiled.append(Path(command[-1]).stem)
        self.after_compile()
        return subprocess.CompletedProcess(command, self.child_exit)

    def run_main(self, args=()):
        self.stdout, self.stderr = io.StringIO(), io.StringIO()
        with redirect_stdout(self.stdout), redirect_stderr(self.stderr):
            return self.build.main(list(args), root=self.root, environ=self.env)

    def receipts(self):
        return [json.loads(p.read_text()) for p in
                sorted((self.root / '.closeout-build').glob('run-*/logs/*.json'))]

    def test_check_is_read_only_and_does_not_compile(self):
        before = set(self.root.rglob('*'))
        self.assertEqual(self.run_main(['--check']), 0)
        self.assertEqual(self.compiled, [])
        self.assertEqual(set(self.root.rglob('*')), before)

    def test_full_cold_rebuild_twice_under_lock_with_hashes(self):
        for _ in range(2):
            self.assertEqual(self.run_main(), 0)
        self.assertEqual(self.compiled, ['Base', 'OneTenthAudit', 'OneTenthParentAudit'] * 2)
        receipts = self.receipts()
        self.assertEqual(len(receipts), 6)
        for receipt in receipts:
            self.assertEqual(receipt['exit_code'], 0)
            self.assertEqual(receipt['source_sha256'], receipt['source_sha256_after'])
            self.assertEqual(receipt['object_sha256'], self.build.sha256(Path(receipt['object'])))
            self.assertEqual(receipt['log_sha256'], self.build.sha256(Path(receipt['log'])))
        summaries = [json.loads(p.read_text()) for p in
                     (self.root / '.closeout-build').glob('run-*/build.json')]
        self.assertEqual([s['status'] for s in summaries], ['passed', 'passed'])
        self.assertTrue(all(len(s['modules']) == 3 for s in summaries))

    def test_lake_import_path_tracks_only_successful_builds(self):
        public = self.root / '.closeout-build/lib/lean'
        self.assertEqual(self.run_main(), 0)
        self.assertTrue(public.is_symlink())
        first = public.resolve()
        self.assertTrue((public / 'StarKakeyaLower/OneTenthAudit.olean').is_file())
        self.assertEqual(self.run_main(), 0)
        self.assertNotEqual(first, public.resolve())
        last_good = public.resolve()
        self.child_exit = 23
        self.assertEqual(self.run_main(), 23)
        self.assertEqual(public.resolve(), last_good)

    def test_publication_cannot_follow_foreign_library_directory(self):
        out = self.root / '.closeout-build'
        out.mkdir()
        (out / 'lib').symlink_to(self.mathlib, target_is_directory=True)
        self.assertEqual(self.run_main(), 1)
        self.assertFalse((self.mathlib / 'lean').exists())

    def test_compiler_failure_preserves_exact_exit_and_stops(self):
        self.child_exit = 23
        self.assertEqual(self.run_main(), 23)
        self.assertEqual(self.compiled, ['Base'])
        self.assertEqual(self.receipts()[0]['exit_code'], 23)

    def test_signal_exit_is_not_disguised_as_success(self):
        self.child_exit = -15
        self.assertEqual(self.run_main(), -15)
        self.assertEqual(self.receipts()[0]['exit_code'], -15)

    def test_source_change_during_compile_fails_closed(self):
        source = self.root / 'StarKakeyaLower/Base.lean'
        self.after_compile = lambda: source.write_text('import Mathlib\n-- mutation\n')
        self.assertEqual(self.run_main(), 1)
        self.assertEqual(self.compiled, ['Base'])
        self.assertNotEqual(self.receipts()[0]['source_sha256'],
                            self.receipts()[0]['source_sha256_after'])

    def test_restored_source_bytes_still_detect_write_during_compile(self):
        source = self.root / 'StarKakeyaLower/Base.lean'
        original = source.read_bytes()
        def change_and_restore():
            source.write_bytes(original + b'-- transient mutation\n')
            source.write_bytes(original)
        self.after_compile = change_and_restore
        self.assertEqual(self.run_main(), 1)
        self.assertIn('source changed', self.stderr.getvalue())
        self.assertEqual(self.compiled, ['Base'])

    def test_zero_exit_without_object_is_not_success(self):
        def remove_object():
            for obj in (self.root / '.closeout-build').rglob('*.olean'):
                obj.unlink()
        self.after_compile = remove_object
        self.assertEqual(self.run_main(), 1)
        self.assertIn('without a regular nonempty object', self.stderr.getvalue())
        self.assertEqual(self.receipts()[0]['exit_code'], 0)

    def test_changed_dependency_object_invalidates_whole_build(self):
        object_path = self.mathlib / '.lake/build/lib/lean/Mathlib.olean'
        self.after_compile = lambda: object_path.write_bytes(b'changed fake dependency object')
        self.assertEqual(self.run_main(), 1)
        self.assertIn('dependency objects changed', self.stderr.getvalue())

    def test_output_symlink_cannot_write_donor(self):
        (self.root / '.closeout-build').symlink_to(self.mathlib, target_is_directory=True)
        self.assertEqual(self.run_main(), 1)
        self.assertIn('symlink', self.stderr.getvalue())
        self.assertEqual(self.compiled, [])

    def test_interrupted_compiler_has_no_success_receipt_and_releases_lease(self):
        def interrupt():
            raise self.build.Interrupted(15)
        self.after_compile = interrupt
        self.assertEqual(self.run_main(), 143)
        self.assertIsNone(self.receipts()[0]['exit_code'])
        self.after_compile = lambda: None
        self.assertEqual(self.run_main(), 0)

    def test_lock_contention_fails_without_compiler(self):
        import fcntl
        directory = self.root / '.closeout-build'
        directory.mkdir()
        with (directory / 'compile.lock').open('a') as lease:
            fcntl.flock(lease.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
            self.assertEqual(self.run_main(), 1)
        self.assertEqual(self.compiled, [])

    def test_unresolved_external_import_fails_even_in_check(self):
        (self.root / 'StarKakeyaLower/Base.lean').write_text('import Unknown.Package\n')
        self.assertEqual(self.run_main(['--check']), 1)
        self.assertEqual(self.compiled, [])


if __name__ == '__main__':
    unittest.main(verbosity=2)
