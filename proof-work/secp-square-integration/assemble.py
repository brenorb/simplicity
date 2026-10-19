"""Reconstruct committed checked square proofs as ordinary modules, externally.

Only module-name tokens and missing project membership are changed. No local
objects are copied; the normal dependency graph must build the full closure.
"""
import importlib.util
import io
import json
from pathlib import Path
import subprocess
import sys
import tarfile
import tempfile

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
SOURCE_REV = 'a591a2e13e99a6f5f7de54807ef4de14da6e4daa'
sp = importlib.util.spec_from_file_location('square_checked_public_basis', HERE.parent / 'secp-square-public/verify.py')
p = importlib.util.module_from_spec(sp)
sp.loader.exec_module(p)
s = p.s
base = s.load('square_ordinary_basis_reconstruction', HERE.parent / 'secp-beta-integration/assemble.py')
rename = base.old.rename
MAPPING = {
    'SquareRun.Run': 'C.jet_secp_square_execution',
    'SquareValue.Algebra': 'C.jet_secp_square_accum_algebra',
    'SquareValue.Columns': 'C.jet_secp_square_columns',
    'SquareValue.Schedule': 'C.jet_secp_square_schedule',
    'SquareValue.Denote': 'C.jet_secp_square_denote',
    'SquareValue.Equality': 'C.jet_secp_square_sx_equality',
    'SquareValue.Link': 'C.jet_secp_square_source_links',
    'SquareValue.Lists': 'C.jet_secp_square_source_list',
    'SquareValue.Numeric': 'C.jet_secp_square_numeric',
    'SquareValue.Execution': 'C.jet_secp_square_numeric_call',
    'SquareValue.Spec': 'C.jet_secp_square_spec_bridge',
    'SquareCaller.Bridge': 'C.jet_secp_square_writer_bridge',
    'SquarePublic.Chain': 'C.jet_secp_square_chain',
    'SquarePublic.Rest': 'C.jet_secp_square_rest',
    'SquarePublic.Public': 'C.jet_secp_square_public',
    'SquarePublic.Local': 'C.jet_secp_square_local',
}
ROOT = MAPPING['SquarePublic.Local']


def blob(name):
    return subprocess.check_output(['git', 'show', SOURCE_REV + ':' + name], cwd=REPO)


def originals():
    r = json.loads(blob('proof-work/secp-square-public/RUN.json'))
    checked = json.loads(blob('proof-work/secp-square-public/CHECKED.json'))
    if (not checked['recursive_kernel_check'] or checked['kernel']['exit_code'] or
            checked['run_sha256'] != s.sha(blob('proof-work/secp-square-public/RUN.json')) or
            not checked['whole_square_jet_proved'] or checked['accepted'] or checked['coverage_added']):
        raise ValueError('expected the checked unregistered full public square proof')
    runs = {
        'SquareRun': ('proof-work/secp-square-execution/RUN.json', 'proof-work/secp-square-execution'),
        'SquareValue': ('proof-work/secp-square-values/RUN.json', 'proof-work/secp-square-values'),
        'SquareCaller': ('proof-work/secp-square-caller/CHECKED.json', 'proof-work/secp-square-caller'),
        'SquarePublic': ('proof-work/secp-square-public/RUN.json', 'proof-work/secp-square-public'),
    }
    extensions = {}
    for group, (path, folder) in runs.items():
        record = json.loads(blob(path))
        for old in MAPPING:
            if not old.startswith(group + '.'):
                continue
            short = old.rsplit('.', 1)[-1]
            row = record['source_objects'] if group in {'SquareRun', 'SquareCaller'} else record['source_objects'][short]
            extensions[old] = dict(origin=folder + '/' + short + '.v.source', sha256=row['source_sha256'])
    if len(r['loaded_local_source_objects']) != 223 or set(extensions) != set(MAPPING):
        raise ValueError('unexpected complete square source closure')
    return r, extensions


def payloads():
    parent, extensions = originals()
    basis = base.source_payloads()
    sources = {}
    for name, row in parent['loaded_local_source_objects'].items():
        target = 'Coq/' + name
        b = basis[target]
        if s.sha(b['raw']) != row['source_sha256']:
            raise ValueError('ordinary source is not the exact checked square dependency: ' + target)
        sources[target] = dict(origin=b['origin'], origin_revision=b['origin_revision'],
            basis_source_metadata={k: v for k, v in b.items() if k != 'raw'}, raw=b['raw'], renamed=False)
    for old, row in extensions.items():
        original = blob(row['origin'])
        if s.sha(original) != row['sha256']:
            raise ValueError('committed checked square source differs: ' + old)
        normal = rename(original.decode(), MAPPING)
        if rename(normal, {v: k for k, v in MAPPING.items()}) != original.decode():
            raise ValueError('square module-only rename is not exactly reversible: ' + old)
        s.safe_source(normal, MAPPING[old])
        sources['Coq/' + MAPPING[old].replace('.', '/') + '.v'] = dict(origin=row['origin'],
            origin_revision=SOURCE_REV, original_module=old, original_sha256=row['sha256'],
            raw=normal.encode(), renamed=True)
    if len(sources) != 239:
        raise ValueError('unexpected ordinary square source count')
    return sources


def prepare():
    if (HERE / 'PREPARATION.json').exists():
        raise ValueError('ordinary square preparation already recorded')
    p.check()
    before, index = s.input_map(), s.index_hash()
    source_payloads = payloads()
    work = Path(tempfile.mkdtemp(prefix='jet-square-integration-', dir='/private/tmp'))
    raw = subprocess.check_output(['git', 'archive', SOURCE_REV, 'Coq', 'C', 'Haskell'], cwd=REPO)
    with tarfile.open(fileobj=io.BytesIO(raw)) as archive:
        archive.extractall(work, filter='data')
    if any((work / 'Coq').rglob('*.vo')):
        raise ValueError('fresh square candidate unexpectedly contains local objects')
    changes, sources = {}, {}
    for name, row in source_payloads.items():
        target = work / name
        if row['renamed'] and target.exists():
            raise ValueError('ordinary square module collision: ' + name)
        changes[target] = row['raw'].decode()
        sources[name] = {k: v for k, v in row.items() if k != 'raw'} | {'sha256': s.sha(row['raw'])}
    projects = {}
    files = sorted(name.removeprefix('Coq/') for name in sources)
    for name in ['_CoqProject', '_CoqProject.jets']:
        target = work / 'Coq' / name
        original = target.read_text()
        missing = [f for f in files if f not in original.splitlines()]
        updated = original.rstrip() + '\n' + '\n'.join(missing) + '\n'
        changes[target] = updated
        projects[name] = dict(original_sha256=s.sha(original.encode()), sha256=s.sha(updated.encode()), appended=missing)
    s.changed(changes)
    if before != s.input_map() or index != s.index_hash():
        raise ValueError('main source or staging changed during square assembly')
    r = dict(candidate=str(work), source_revision=SOURCE_REV, root=ROOT, sources=sources, projects=projects,
        module_renaming=MAPPING, parent_checked_sha256=s.sha(blob('proof-work/secp-square-public/CHECKED.json')),
        assembler_sha256=s.sha(Path(__file__).read_bytes()), rename_helper_sha256=s.sha(Path(base.old.__file__).read_bytes()),
        basis_assembler_sha256=s.sha(Path(base.__file__).read_bytes()), main_inputs=before, staged_patch_sha256=index,
        normal_registration=False, coverage_added=0)
    s.changed({HERE / 'PREPARATION.json': json.dumps(r, indent=2) + '\n'})
    print('Prepared ' + str(work) + ': 223 exact inherited sources and 16 reversible ordinary-module extensions', flush=True)


def identity():
    r = json.loads((HERE / 'PREPARATION.json').read_text())
    work = Path(r['candidate'])
    if (work == REPO or REPO in work.parents or work.is_symlink() or r['source_revision'] != SOURCE_REV or
            r['assembler_sha256'] != s.sha(Path(__file__).read_bytes()) or
            r['basis_assembler_sha256'] != s.sha(Path(base.__file__).read_bytes()) or
            r['rename_helper_sha256'] != s.sha(Path(base.old.__file__).read_bytes()) or
            r['parent_checked_sha256'] != s.sha(blob('proof-work/secp-square-public/CHECKED.json')) or
            r['main_inputs'] != s.input_map() or r['staged_patch_sha256'] != s.index_hash()):
        raise ValueError('ordinary square preparation identity differs')
    source_payloads = payloads()
    if set(r['sources']) != set(source_payloads):
        raise ValueError('ordinary square source inventory differs')
    for name, row in source_payloads.items():
        target = work / name
        if target.is_symlink() or target.read_bytes() != row['raw'] or s.sha(target.read_bytes()) != r['sources'][name]['sha256']:
            raise ValueError('ordinary square source differs from committed checked proof: ' + name)
    for name, row in r['projects'].items():
        if s.sha((work / 'Coq' / name).read_bytes()) != row['sha256']:
            raise ValueError('ordinary square project changed: ' + name)
    return work, r


def build():
    work, r = identity()
    if (HERE / 'BUILD-LAUNCH.json').exists():
        raise ValueError('ordinary square build already launched; poll original process')
    if any((work / 'Coq').rglob('*.vo')):
        raise ValueError('ordinary square fresh build must start without local objects')
    flags = []
    cc = Path(s.ENV['COMPCERT'])
    vst = Path(s.ENV.get('VST', str(cc.parent / 'vst-2.14')))
    for d in ['lib', 'common', 'x86_64', 'x86', 'cfrontend', 'export']:
        flags += ['-R', str(cc / d), 'compcert.' + d]
    flags += ['-R', str(cc / 'flocq'), 'Flocq']
    for d in ['msl', 'sepcomp', 'veric', 'zlist', 'floyd', 'progs64', 'concurrency', 'atomics', 'sha']:
        flags += ['-Q', str(vst / d), 'sha' if d == 'sha' else 'VST.' + d]
    commands = [['coq_makefile', '-f', '_CoqProject.jets', *flags, '-o', 'JetMakefile'],
        ['make', '-f', 'JetMakefile', '-j2', ROOT.replace('.', '/') + '.vo']]
    s.changed({HERE / 'BUILD-LAUNCH.json': json.dumps(dict(candidate=str(work), commands=commands,
        preparation_sha256=s.sha((HERE / 'PREPARATION.json').read_bytes()), complete=False), indent=2) + '\n'})
    rows = {}
    for stem, command in zip(['square-normal-makefile', 'square-normal-build'], commands):
        rows[stem] = s.run(work, command, stem, 2400)
        print('Passed ' + stem, flush=True)
    identity()
    source_objects = {name: s.sha((work / name).with_suffix('.vo').read_bytes()) for name in r['sources']}
    compiled = {str(f.relative_to(work)) for f in (work / 'Coq').rglob('*.vo')}
    if compiled != {str(Path(n).with_suffix('.vo')) for n in r['sources']}:
        raise ValueError('ordinary square fresh object inventory differs from the exact source closure')
    s.changed({HERE / 'BUILT.json': json.dumps(dict(candidate=str(work), complete=True, commands=rows,
        preparation_sha256=s.sha((HERE / 'PREPARATION.json').read_bytes()), source_objects=source_objects,
        no_local_objects_copied=True, normal_registration=False, coverage_added=0), indent=2) + '\n'})
    print('Normal dependency graph freshly source-built the exact 239-module square closure', flush=True)


if __name__ == '__main__':
    if len(sys.argv) != 2 or sys.argv[1] not in {'prepare', 'build', 'check'}:
        raise SystemExit('usage: assemble.py prepare|build|check')
    if sys.argv[1] == 'check':
        print(identity()[0])
    else:
        {'prepare': prepare, 'build': build}[sys.argv[1]]()
