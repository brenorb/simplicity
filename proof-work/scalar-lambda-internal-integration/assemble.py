"""Reversibly integrate the checked scalar-lambda proof under ordinary names.

All writes target a new external source-only tree. No main registry or target
changes, and no local compiled objects are copied into the candidate.
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
sp = importlib.util.spec_from_file_location('lambda_ordinary_checked_parent', HERE.parent / 'scalar-lambda-internal/verify.py')
p = importlib.util.module_from_spec(sp)
sp.loader.exec_module(p)
s = p.s
renamer = s.load('lambda_ordinary_module_rename', HERE.parent / 'secp-field-integration/assemble.py')
MAPPING = {'LambdaInternal.' + n: 'C.jet_secp_scalar_lambda_closed_' + n.lower() for n in p.NAMES}
ROOTS = [MAPPING[m] for m in p.ROOTS]


def payloads():
    work, record = p.bound()
    result = {}
    for name, row in record['loaded_local_source_objects'].items():
        raw = (work / name).read_bytes()
        if s.sha(raw) != row['source_sha256']:
            raise ValueError('checked inherited source changed: ' + name)
        result[name] = dict(raw=raw, renamed=False)
    for module, normal in MAPPING.items():
        name = module.rsplit('.', 1)[1]
        original = (p.HERE / (name + '.v.source')).read_text()
        code = renamer.rename(original, MAPPING)
        if renamer.rename(code, {v: k for k, v in MAPPING.items()}) != original:
            raise ValueError('ordinary lambda rename is not exactly reversible: ' + module)
        s.safe_source(code, normal)
        result['Coq/' + normal.replace('.', '/') + '.v'] = dict(raw=code.encode(), renamed=True,
            original_module=module, original_sha256=s.sha(original.encode()))
    return result


def prepare():
    if (HERE / 'PREPARATION.json').exists():
        raise ValueError('ordinary lambda preparation already exists')
    p.check()
    before, index = s.input_map(), s.index_hash()
    sources = payloads()
    work = Path(tempfile.mkdtemp(prefix='jet-lambda-ordinary-', dir='/private/tmp'))
    raw = subprocess.check_output(['git', 'archive', p.a.SOURCE_REV, 'Coq', 'C', 'Haskell'], cwd=REPO)
    with tarfile.open(fileobj=io.BytesIO(raw)) as archive:
        archive.extractall(work, filter='data')
    if any((work / 'Coq').rglob('*.vo')):
        raise ValueError('source archive unexpectedly contains local objects')
    changes = {}
    for name, row in sources.items():
        if row['renamed'] and (work / name).exists():
            raise ValueError('ordinary lambda source collision: ' + name)
        changes[work / name] = row['raw'].decode()
    projects = {}
    for name in ['_CoqProject', '_CoqProject.jets']:
        original = (work / 'Coq' / name).read_text()
        missing = sorted(n.removeprefix('Coq/') for n in sources if n.removeprefix('Coq/') not in original.splitlines())
        new = original.rstrip() + '\n' + '\n'.join(missing) + '\n'
        changes[work / 'Coq' / name] = new
        projects[name] = dict(original_sha256=s.sha(original.encode()), sha256=s.sha(new.encode()), appended=missing)
    s.changed(changes)
    if before != s.input_map() or index != s.index_hash():
        raise ValueError('main/index changed during ordinary lambda preparation')
    record = dict(candidate=str(work), source_revision=p.a.SOURCE_REV, roots=ROOTS, module_renaming=MAPPING,
        sources={n: {k: v for k, v in row.items() if k != 'raw'} | {'sha256': s.sha(row['raw'])} for n, row in sources.items()},
        projects=projects, parent_checked_sha256=s.sha((p.HERE / 'CHECKED.json').read_bytes()),
        assembler_sha256=s.sha(Path(__file__).read_bytes()), rename_helper_sha256=s.sha(Path(renamer.__file__).read_bytes()),
        main_inputs=before, staged_patch_sha256=index, normal_registration=False, coverage_added=0)
    s.changed({HERE / 'PREPARATION.json': json.dumps(record, indent=2) + '\n'})
    print('Prepared ' + str(work) + ': ' + str(len(sources)) + ' source-only ordinary modules', flush=True)


def identity():
    r = json.loads((HERE / 'PREPARATION.json').read_text())
    work = Path(r['candidate'])
    if (work == REPO or REPO in work.parents or work.is_symlink() or r['roots'] != ROOTS or
            r['module_renaming'] != MAPPING or r['assembler_sha256'] != s.sha(Path(__file__).read_bytes()) or
            r['rename_helper_sha256'] != s.sha(Path(renamer.__file__).read_bytes()) or
            r['parent_checked_sha256'] != s.sha((p.HERE / 'CHECKED.json').read_bytes()) or
            r['main_inputs'] != s.input_map() or r['staged_patch_sha256'] != s.index_hash()):
        raise ValueError('ordinary lambda preparation identity differs')
    proposed = payloads()
    if set(proposed) != set(r['sources']):
        raise ValueError('ordinary lambda source inventory differs')
    for n, row in proposed.items():
        if (work / n).is_symlink() or (work / n).read_bytes() != row['raw'] or s.sha(row['raw']) != r['sources'][n]['sha256']:
            raise ValueError('ordinary lambda source differs: ' + n)
    for n, row in r['projects'].items():
        if s.sha((work / 'Coq' / n).read_bytes()) != row['sha256']:
            raise ValueError('ordinary lambda project differs: ' + n)
    return work, r


def build():
    work, r = identity()
    if (HERE / 'BUILD-LAUNCH.json').exists():
        raise ValueError('ordinary lambda build already launched; poll the original process')
    cc = Path(s.ENV['COMPCERT'])
    vst = Path(s.ENV.get('VST', str(cc.parent / 'vst-2.14')))
    flags = []
    for d in ['lib', 'common', 'x86_64', 'x86', 'cfrontend', 'export']:
        flags += ['-R', str(cc / d), 'compcert.' + d]
    flags += ['-R', str(cc / 'flocq'), 'Flocq']
    for d in ['msl', 'sepcomp', 'veric', 'zlist', 'floyd', 'progs64', 'concurrency', 'atomics', 'sha']:
        flags += ['-Q', str(vst / d), 'sha' if d == 'sha' else 'VST.' + d]
    commands = [['coq_makefile', '-f', '_CoqProject.jets', *flags, '-o', 'JetMakefile'],
        ['make', '-f', 'JetMakefile', '-j2', *(m.replace('.', '/') + '.vo' for m in ROOTS)]]
    s.changed({HERE / 'BUILD-LAUNCH.json': json.dumps(dict(candidate=str(work), commands=commands,
        preparation_sha256=s.sha((HERE / 'PREPARATION.json').read_bytes()), complete=False), indent=2) + '\n'})
    rows = {}
    for stem, command in zip(['lambda-ordinary-makefile', 'lambda-ordinary-build'], commands):
        rows[stem] = s.run(work, command, stem, 3600)
        print('Passed ' + stem, flush=True)
    identity()
    result = dict(candidate=str(work), complete=True, no_local_objects_copied=True, commands=rows,
        preparation_sha256=s.sha((HERE / 'PREPARATION.json').read_bytes()),
        source_objects={n: s.sha((work / n).with_suffix('.vo').read_bytes()) for n in r['sources']},
        normal_registration=False, coverage_added=0)
    s.changed({HERE / 'BUILT.json': json.dumps(result, indent=2) + '\n'})
    print('Fresh ordinary lambda dependency closure built from source without copied local objects', flush=True)


if __name__ == '__main__':
    if len(sys.argv) != 2 or sys.argv[1] not in {'prepare', 'build', 'check'}:
        raise SystemExit('usage: assemble.py prepare|build|check')
    if sys.argv[1] == 'check':
        print(identity()[0])
    else:
        {'prepare': prepare, 'build': build}[sys.argv[1]]()
