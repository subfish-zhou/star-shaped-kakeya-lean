#!/usr/bin/env python3
"""Serial direct compiler; exact pinned read-only dependency donor, local output only."""
import argparse
from contextlib import contextmanager
import hashlib
import fcntl
import json
import os
from pathlib import Path
import re
import signal
import stat
import subprocess
import sys
import tempfile
import time

DEFAULT_ROOTS = ('StarKakeyaLower.OneTenthAudit', 'StarKakeyaLower.OneTenthParentAudit')
MODULE = r'[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*'


def lean_code(text):
    """Mask nested comments and strings, retaining line boundaries (not a Lean parser)."""
    result, depth, string, i = [], 0, False, 0
    while i < len(text):
        pair, char = text[i:i + 2], text[i]
        if depth:
            if pair in ('/-', '-/'):
                depth += 1 if pair == '/-' else -1
                result.append('  ')
                i += 2
                continue
        elif string:
            if char == '\\' and i + 1 < len(text):
                result.append(' ' + ('\n' if text[i + 1] == '\n' else ' '))
                i += 2
                continue
            if char == '"':
                string = False
            result.append(char if char in '\n"' else ' ')
            i += 1
            continue
        elif pair == '--':
            end = text.find('\n', i)
            end = len(text) if end == -1 else end
            result.append(' ' * (end - i))
            i = end
            continue
        elif pair == '/-':
            depth = 1
            result.append('  ')
            i += 2
            continue
        elif char == '"':
            string = True
            result.append('"')
            i += 1
            continue
        result.append('\n' if char == '\n' else ' ' if depth else char)
        i += 1
    if depth or string:
        raise RuntimeError('unsupported unterminated comment/string')
    return ''.join(result)


def read_imports(source):
    imports, header = [], True
    for number, line in enumerate(lean_code(source.read_text(encoding='utf-8')).splitlines(), 1):
        line = line.strip()
        if not line:
            continue
        if re.search(r'\bimport\b', line) or (header and re.match(r'^(prelude|module)\b', line)):
            match = re.fullmatch(r'import[ \t]+(' + MODULE + r')', line)
            if not match or not header:
                raise RuntimeError(f'unsupported import/header at {source}:{number}: {line}')
            imports.append(match.group(1))
        else:
            header = False
    return imports


def source_inventory(root):
    sources = {}
    def fail(error):
        raise RuntimeError(f'source inventory failed: {error}')
    for base, dirs, files in os.walk(root, onerror=fail):
        dirs[:] = sorted(d for d in dirs if d not in ('.git', '.lake', '.closeout-build'))
        require(not any((Path(base) / d).is_symlink() for d in dirs),
                f'unsupported symlink source directory under {base}')
        for filename in sorted(files):
            if filename.endswith('.lean'):
                path = Path(base) / filename
                name = '.'.join(path.relative_to(root).with_suffix('').parts)
                if not re.fullmatch(MODULE, name) or path.is_symlink():
                    raise RuntimeError(f'unsupported source path: {path}')
                require(name not in sources, f'duplicate module source path: {path}')
                sources[name] = path
    return sources


def resolve_graph(root, roots=DEFAULT_ROOTS):
    """Resolve every shipped module; roots must cover the complete source inventory."""
    sources = source_inventory(root)
    imports = {name: read_imports(path) for name, path in sources.items()}
    order, active, done = [], [], set()

    def visit(name):
        if name not in sources:
            raise RuntimeError(f'missing local module: {name}')
        if name in active:
            raise RuntimeError('import cycle: ' + ' -> '.join(active + [name]))
        if name in done:
            return
        active.append(name)
        for dep in imports[name]:
            if dep in sources or dep == 'StarKakeyaLower' or dep.startswith('StarKakeyaLower.'):
                visit(dep)
        active.pop()
        done.add(name)
        order.append(name)

    for name in roots:
        visit(name)
    uncovered = sorted(set(sources) - done)
    if uncovered:
        raise RuntimeError('uncovered public sources: ' + ', '.join(uncovered))
    return sources, imports, order


PIN = 'leanprover/lean4:v4.30.0-rc2'
COMPILER_COMMIT = '3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc'
PACKAGE_PINS = {
    'mathlib': '5450b53e5ddc75d46418fabb605edbf36bd0beb6',
    'plausible': '86210d4ad1b08b086d0bd638637a75246523dbb8',
    'LeanSearchClient': 'c5d5b8fe6e5158def25cd28eb94e4141ad97c843',
    'importGraph': 'cdab3938ccabbdb044be6896e251b5814bec932e',
    'proofwidgets': '2db6054a44326f8c0230ee0570e2ddb894816511',
    'aesop': 'f0c6e183ea26531e82773feb4b73ab6595ca17a5',
    'Qq': '1cc7e819b9b9bc1e87c9edcccb62e0269e00a809',
    'batteries': '5c57f3857ba81924a88b2cdf4f062e34ec04ff11',
    'Cli': '13567aed1ac4f12aea9484178e07e51f8c9f7658',
}


def sha256(path):
    digest = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            digest.update(block)
    return digest.hexdigest()


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def query(command, env):
    result = subprocess.run(command, env=env, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE, timeout=30)
    require(result.returncode == 0,
            f'configuration query failed ({result.returncode}): {command}: {result.stderr.strip()}')
    return result.stdout.strip()


def package_manifest(path, complete=True):
    try:
        manifest = json.loads(path.read_text(encoding='utf-8'))
        require(manifest['packagesDir'] == '.lake/packages', f'dependency packagesDir: {path}')
        packages = manifest['packages']
        records = {p['name']: p for p in packages}
        require(len(records) == len(packages), f'duplicate dependency: {path}')
        for name, record in records.items():
            require(name in PACKAGE_PINS and record['rev'] == PACKAGE_PINS[name]
                    and record['type'] == 'git' and record.get('subDir') is None
                    and record['manifestFile'] == 'lake-manifest.json',
                    f'dependency pin/shape mismatch: {path}: {name}')
        if complete:
            require(set(records) == set(PACKAGE_PINS), f'dependency set mismatch: {path}')
        return records
    except (ValueError, KeyError, TypeError) as error:
        raise RuntimeError(f'invalid dependency manifest: {path}: {error}') from error


def configure(root, environ=None) -> dict:
    """Read-only preflight; never invokes elan, Lake, an installer, or proof compilation."""
    env = dict(os.environ if environ is None else environ)
    donor_value = env.get('KAKEYA_DEPENDENCIES', str(root))
    require(bool(donor_value), 'empty KAKEYA_DEPENDENCIES')
    donor = Path(donor_value).expanduser().resolve()
    elan_home = Path(env.get('ELAN_HOME', str(Path.home() / '.elan'))).expanduser()
    sysroot_value = env.get('KAKEYA_LEAN_SYSROOT', str(
        elan_home / 'toolchains/leanprover--lean4---v4.30.0-rc2'))
    require(bool(sysroot_value), 'empty KAKEYA_LEAN_SYSROOT')
    sysroot = Path(sysroot_value).expanduser().resolve()
    compiler = sysroot / 'bin/lean'
    require(compiler.is_file() and os.access(compiler, os.X_OK),
            f'missing executable compiler at {compiler}; prepare the exact pinned sysroot separately')
    require(compiler.resolve().parent == sysroot / 'bin', f'compiler escapes sysroot: {compiler}')
    require((sysroot / 'lib/lean/Init.olean').is_file(), f'missing sysroot Init.olean: {sysroot}')
    env.update(LEAN_SYSROOT=str(sysroot), LEAN_PATH=str(sysroot / 'lib/lean'),
               PATH=str(sysroot / 'bin') + os.pathsep + env.get('PATH', os.defpath))
    for project in {root, donor}:
        require((project / 'lean-toolchain').read_text().strip() == PIN,
                f'toolchain mismatch: {project}')
    expected = package_manifest(root / 'dependencies.lock.json')
    for project in {root, donor}:
        actual = package_manifest(project / 'lake-manifest.json')
        fields = ('rev', 'url', 'type', 'subDir', 'manifestFile', 'configFile')
        require(all(tuple(actual[n].get(k) for k in fields) ==
                    tuple(expected[n].get(k) for k in fields) for n in expected),
                f'dependency manifest mismatch: {project}')
    version = query([str(compiler), '--version'], env)
    require(re.fullmatch(r'Lean \(version 4\.30\.0-rc2, [^,\s]+, commit ' +
                         COMPILER_COMMIT + r', Release\)', version),
            f'compiler identity mismatch: {version}')
    require(Path(query([str(compiler), '--print-prefix'], env)).resolve() == sysroot,
            f'compiler sysroot mismatch: {compiler}')
    git_env = {key: value for key, value in env.items() if not key.startswith('GIT_')}
    git_env.update(GIT_NO_LAZY_FETCH='1', GIT_OPTIONAL_LOCKS='0', GIT_TERMINAL_PROMPT='0')
    records, paths = [], []
    for name in PACKAGE_PINS:
        source = donor / '.lake/packages' / name
        require(source.is_dir(), f'missing dependency {source}; prepare prebuilt dependencies separately')
        git = lambda *args: query(['git', '-C', str(source), *args], git_env)
        require(git('rev-parse', 'HEAD') == PACKAGE_PINS[name], f'dependency HEAD mismatch: {name}')
        require(not git('status', '--porcelain', '--untracked-files=all'), f'dirty dependency: {name}')
        manifest_path = source / 'lake-manifest.json'
        require(git('show', 'HEAD:lake-manifest.json') == manifest_path.read_text().strip(),
                f'dependency manifest differs from HEAD: {name}')
        nested = package_manifest(manifest_path, complete=False)
        if name == 'mathlib':
            require(set(nested) == set(PACKAGE_PINS) - {'mathlib'}, 'mathlib dependency manifest set mismatch')
        # Transitive packages can pin older upstream development toolchains;
        # the actual compiler and mathlib/project toolchains govern this build.
        if name == 'mathlib':
            require((source / 'lean-toolchain').read_text().strip() == PIN,
                    f'dependency toolchain mismatch: {name}')
        library = source / '.lake/build/lib/lean'
        # Upstream cache omits unused packages (notably Cli). Required imported
        # objects are checked by external_objects and by the real Lean compiler.
        paths.append(library)
        records.append({'name': name, 'rev': PACKAGE_PINS[name], 'clean': True,
                        'source': str(source), 'manifest_sha256': sha256(manifest_path)})
    require((paths[0] / 'Mathlib.olean').is_file(), 'missing prebuilt Mathlib.olean')
    paths.append(sysroot / 'lib/lean')
    report = {'toolchain': PIN, 'compiler': str(compiler), 'compiler_version': version,
              'compiler_sha256': sha256(compiler), 'sysroot_init_sha256': sha256(paths[-1] / 'Init.olean'),
              'packages': records, 'donor': str(donor), 'donor_project_objects_used': False,
              'lock_sha256': sha256(root / 'dependencies.lock.json'),
              'manifest_sha256': sha256(root / 'lake-manifest.json'),
              'donor_manifest_sha256': sha256(donor / 'lake-manifest.json')}
    return dict(root=root, donor=donor, sysroot=sysroot, compiler=compiler,
                env=env, paths=paths, report=report)


def source_state(root):
    result = {}
    for name, path in source_inventory(root).items():
        before = path.stat()
        digest = sha256(path)
        after = path.stat()
        stamp = lambda s: (s.st_dev, s.st_ino, s.st_size, s.st_mtime_ns, s.st_ctime_ns)
        require(stamp(before) == stamp(after), f'source changed while hashing: {path}')
        result[name] = {'sha256': digest, 'stat': stamp(after)}
    return result


def external_objects(sources, imports, paths):
    result = {}
    for name in sorted({dep for deps in imports.values() for dep in deps} - set(sources)):
        candidates = [path / (name.replace('.', '/') + '.olean') for path in paths]
        candidates = [path for path in candidates if path.is_file()]
        require(len(candidates) == 1, f'unresolved/ambiguous external import: {name}')
        result[name] = {'path': str(candidates[0]), 'sha256': sha256(candidates[0])}
    return result


def prepare(root, environ) -> dict:
    config = configure(root, environ)
    initial = source_state(root)
    sources, imports, order = resolve_graph(root)
    require(initial == source_state(root), 'source changed during graph resolution')
    external = external_objects(sources, imports, config['paths'])
    config.update(sources=sources, imports=imports, order=order, initial=initial, external=external)
    return config


@contextmanager
def serial_lease(root):
    out = root / '.closeout-build'
    require(not out.is_symlink(), f'output directory is a symlink: {out}')
    out.mkdir(exist_ok=True)
    descriptor = os.open(out / 'compile.lock', os.O_CREAT | os.O_RDWR | os.O_NOFOLLOW, 0o600)
    with os.fdopen(descriptor, 'a') as lease:
        info = os.fstat(lease.fileno())
        require(stat.S_ISREG(info.st_mode) and info.st_nlink == 1, 'unsafe compiler lock file')
        try:
            fcntl.flock(lease.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError as error:
            raise RuntimeError('another serial build holds the compiler lock; retry after it finishes') from error
        yield out


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n', encoding='utf-8')


def compile_all(config, out):
    """Fresh overlay per invocation; caller holds the lease through final validation."""
    root, sources = config['root'], config['sources']
    run = Path(tempfile.mkdtemp(prefix='run-', dir=out))
    library, logs = run / 'lib/lean', run / 'logs'
    library.mkdir(parents=True)
    logs.mkdir()
    env = dict(config['env'], LEAN_PATH=os.pathsep.join(map(str, [library] + config['paths'])))
    write_json(run / 'environment.json', dict(config['report'], LEAN_PATH=env['LEAN_PATH']))
    summary = {'status': 'running', 'exit_code': None, 'roots': DEFAULT_ROOTS,
               'order': config['order'], 'sources': config['initial'],
               'external_objects': config['external'], 'modules': []}
    write_json(run / 'build.json', summary)
    print(f'BUILD {run} (fresh, serial, -j2)', flush=True)
    try:
        for name in config['order']:
            require(source_state(root) == config['initial'], 'source changed during build')
            source = sources[name]
            obj = library / (name.replace('.', '/') + '.olean')
            obj.parent.mkdir(parents=True, exist_ok=True)
            log = logs / (name + '.log')
            command = [str(config['compiler']), '-j2', '-o', str(obj), str(source)]
            receipt = {'module': name, 'source': str(source),
                       'source_sha256': config['initial'][name]['sha256'],
                       'object': str(obj), 'command': command, 'exit_code': None, 'log': str(log)}
            started = time.monotonic()
            print(f'COMPILE {name} -> {log}', flush=True)
            try:
                with log.open('w', encoding='utf-8') as stream:
                    result = subprocess.run(command, cwd=root, env=env, stdout=stream, stderr=subprocess.STDOUT)
                receipt['exit_code'] = result.returncode
            except BaseException as error:
                receipt['error'] = repr(error)
                raise
            finally:
                receipt['wall_seconds'] = time.monotonic() - started
                receipt['source_sha256_after'] = sha256(source) if source.is_file() else None
                receipt['object_sha256'] = sha256(obj) if obj.is_file() else None
                receipt['log_sha256'] = sha256(log) if log.is_file() else None
                write_json(logs / (name + '.json'), receipt)
                summary['modules'].append(receipt)
            if receipt['exit_code']:
                summary.update(status='failed', exit_code=receipt['exit_code'])
                return receipt['exit_code']
            require(source_state(root) == config['initial'], 'source changed during build')
            require(obj.is_file() and not obj.is_symlink() and obj.stat().st_size > 0,
                    f'compiler returned zero without a regular nonempty object: {name}')
        require(config['report'] == configure(root, config['env'])['report'], 'build environment changed')
        require(config['external'] == external_objects(sources, config['imports'], config['paths']),
                'dependency objects changed during build')
        require(source_state(root) == config['initial'], 'source changed during build')
        require(all(sha256(Path(r['object'])) == r['object_sha256'] for r in summary['modules']),
                'local object changed during build')
        # Expose only a fully checked run at Lake's configured import path.
        public_dir = out / 'lib'
        require(not public_dir.is_symlink(), 'publication library directory is a symlink')
        public_dir.mkdir(exist_ok=True)
        public = public_dir / 'lean'
        require(not public.exists() or public.is_symlink(),
                'publication path is an existing non-symlink directory')
        temporary = run / 'publication-link'
        temporary.symlink_to(library, target_is_directory=True)
        os.replace(temporary, public)
        summary.update(status='passed', exit_code=0)
        print(f'PASS {len(config["order"])} modules; receipt: {run / "build.json"}', flush=True)
        return 0
    except BaseException as error:
        exit_code = 128 + getattr(error, 'signum', signal.SIGINT) if isinstance(error, KeyboardInterrupt) else 1
        summary.update(status='failed', exit_code=exit_code, error=str(error))
        raise
    finally:
        write_json(run / 'build.json', summary)


class Interrupted(KeyboardInterrupt):
    def __init__(self, signum):
        self.signum = signum
        super().__init__(f'interrupted by signal {signum}')


def stop(signum, _frame):
    # subprocess.run kills/reaps its active child before unwinding the held lease.
    raise Interrupted(signum)


def main(argv=None, root=None, environ=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true',
                        help='read-only configuration/import-graph check, no proof compilation')
    args = parser.parse_args(argv)
    root = Path(__file__).resolve().parent if root is None else Path(root).resolve()
    previous = signal.signal(signal.SIGTERM, stop)
    try:
        if args.check:
            config = prepare(root, environ)
            print(f'CHECK PASS: {len(config["order"])} modules; 9 pinned dependencies; '
                  f'{config["report"]["compiler_version"]}; no proof compilation', flush=True)
            return 0
        with serial_lease(root) as out:
            return compile_all(prepare(root, environ), out)
    except KeyboardInterrupt as error:
        print(f'BUILD INTERRUPTED: {error}', file=sys.stderr)
        return 128 + getattr(error, 'signum', signal.SIGINT)
    except (OSError, RuntimeError, ValueError, subprocess.SubprocessError) as error:
        print(f'BUILD ERROR: {error}', file=sys.stderr)
        return 1
    finally:
        signal.signal(signal.SIGTERM, previous)


if __name__ == '__main__':
    code = main()
    if code < 0:
        # Preserve a compiler signal as a signal (not Python's modulo-256 exit code).
        if -code not in (signal.SIGKILL, signal.SIGSTOP):
            signal.signal(-code, signal.SIG_DFL)
        os.kill(os.getpid(), -code)
    sys.exit(code)
