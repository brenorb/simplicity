"""Isolate unchanged scalar-lambda dependencies with checked internal-frame support.

Never overwrite a checked tree, main proof source, registry or staged patch.
Only exact-source/object matches from the checked beta basis seed the cache.
"""
import importlib.util
import io
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tarfile
import tempfile

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
SOURCE_REV = '8d856072668d7364bd014e189fb48168afacebf3'
sp = importlib.util.spec_from_file_location('lambda_internal_checked_beta_basis', HERE.parent / 'secp-beta-integration/verify.py')
v = importlib.util.module_from_spec(sp)
sp.loader.exec_module(v)
s = v.s
ROOTS = ['C.jet_secp_scalar_lambda_local', 'C.jet_secp_scalar_lambda_fresh']


def blob(name):
    return subprocess.check_output(['git', 'show', SOURCE_REV + ':' + name], cwd=REPO)


def committed_dependency(module):
    name = 'Coq/' + module.replace('.', '/') + '.v'
    candidates = [name, 'proof-work/fe-negate/' + Path(name).name + '.source',
        'proof-work/secp-field-literal/inherited/' + name + '.source']
    for origin in candidates:
        result = subprocess.run(['git', 'show', SOURCE_REV + ':' + origin], cwd=REPO,
            stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
        if result.returncode == 0:
            return origin, result.stdout.decode()
    ledger = json.loads((HERE / 'DEPENDENCY-SOURCES.json').read_text())
    if module in ledger['sources']:
        row = ledger['sources'][module]
        record = (REPO / ledger['recorded_receipt']).read_bytes()
        raw = (REPO / row['archive']).read_bytes()
        if (s.sha(record) != ledger['recorded_receipt_sha256'] or s.sha(raw) != row['sha256'] or
                json.loads(record)['main_inputs'][row['source_path']] != row['sha256'] or
                s.sha((REPO / row['source_path']).read_bytes()) != row['sha256']):
            raise ValueError('previously recorded proof dependency differs: ' + module)
        return 'recorded-archive:' + row['archive'], raw.decode()
    raise ValueError('no committed source/archive for lambda dependency: ' + module)


def prepare():
    if (HERE / 'PREPARATION.json').exists():
        raise ValueError('lambda internal preparation already exists')
    v.check()
    basis, prep, built = v.built()
    before, index = s.input_map(), s.index_hash()
    work = Path(tempfile.mkdtemp(prefix='jet-lambda-internal-basis-', dir='/private/tmp'))
    raw = subprocess.check_output(['git', 'archive', SOURCE_REV, 'Coq', 'C', 'Haskell'], cwd=REPO)
    with tarfile.open(fileobj=io.BytesIO(raw)) as archive:
        archive.extractall(work, filter='data')
    if any((work / 'Coq').rglob('*.vo')):
        raise ValueError('unexpected objects in committed source archive')
    payloads = v.a.source_payloads()
    changes = {work / name: row['raw'].decode() for name, row in payloads.items()}
    s.changed(changes)
    sources, objects = {}, {}
    for name, row in prep['sources'].items():
        source = work / name
        obj = (basis / name).with_suffix('.vo')
        if (s.sha(source.read_bytes()) != row['sha256'] or
                s.sha(obj.read_bytes()) != built['source_objects'][name]):
            raise ValueError('source/object mismatch in checked lambda cache basis: ' + name)
        shutil.copyfile(obj, source.with_suffix('.vo'))
        sources[name] = row['sha256']
        objects[name] = built['source_objects'][name]
    known = {n.removeprefix('Coq/').removesuffix('.v').replace('/', '.') for n in sources}
    seen, active, order, added, origins = set(), set(), [], {}, {}

    def visit(module):
        if module in seen or module in known:
            return
        if module in active:
            raise ValueError('cyclic lambda source dependency: ' + module)
        active.add(module)
        name = 'Coq/' + module.replace('.', '/') + '.v'
        origin, code = committed_dependency(module)
        s.safe_source(code, module)
        if not (work / name).exists():
            s.changed({work / name: code})
        elif (work / name).read_text() != code:
            raise ValueError('archive source differs from committed lambda dependency: ' + name)
        for block in re.findall(r'\bRequire(?:\s+(?:Import|Export))?\s+(.*?)\.(?=\s|$)', s.scanner.code_only(code), re.S):
            for dep in block.split():
                if dep.startswith('C.'):
                    visit(dep)
        active.remove(module)
        seen.add(module)
        order.append(module)
        added[name] = s.sha(code.encode())
        origins[name] = origin

    for root in ROOTS:
        visit(root)
    r = dict(candidate=str(work), source_revision=SOURCE_REV, roots=ROOTS, fresh_modules=order,
        inherited_source_hashes=sources, inherited_object_hashes=objects, fresh_source_hashes=added,
        fresh_source_origins=origins,
        dependency_source_ledger_sha256=s.sha((HERE / 'DEPENDENCY-SOURCES.json').read_bytes()),
        main_inputs=before, staged_patch_sha256=index, parent_checked_sha256=s.sha((v.HERE / 'CHECKED.json').read_bytes()),
        preparer_sha256=s.sha(Path(__file__).read_bytes()), normal_registration=False, coverage_added=0)
    if before != s.input_map() or index != s.index_hash():
        raise ValueError('main inputs/staging changed during isolated lambda preparation')
    s.changed({HERE / 'PREPARATION.json': json.dumps(r, indent=2) + '\n'})
    print('Prepared ' + str(work) + ': ' + str(len(sources)) + ' checked cached sources, ' + str(len(order)) + ' fresh unchanged dependencies', flush=True)


def identity():
    r = json.loads((HERE / 'PREPARATION.json').read_text())
    work = Path(r['candidate'])
    if (work == REPO or REPO in work.parents or work.is_symlink() or
            r['preparer_sha256'] != s.sha(Path(__file__).read_bytes()) or
            r['dependency_source_ledger_sha256'] != s.sha((HERE / 'DEPENDENCY-SOURCES.json').read_bytes()) or
            r['parent_checked_sha256'] != s.sha((v.HERE / 'CHECKED.json').read_bytes()) or
            r['main_inputs'] != s.input_map() or r['staged_patch_sha256'] != s.index_hash()):
        raise ValueError('lambda basis preparation identity differs')
    for name, digest in (r['inherited_source_hashes'] | r['fresh_source_hashes']).items():
        if s.sha((work / name).read_bytes()) != digest:
            raise ValueError('lambda basis source differs: ' + name)
    for name, origin in r['fresh_source_origins'].items():
        raw = ((REPO / origin.removeprefix('recorded-archive:')).read_bytes()
            if origin.startswith('recorded-archive:') else blob(origin))
        if s.sha(raw) != r['fresh_source_hashes'][name]:
            raise ValueError('committed lambda dependency archive differs: ' + name)
    for name, digest in r['inherited_object_hashes'].items():
        if s.sha((work / name).with_suffix('.vo').read_bytes()) != digest:
            raise ValueError('lambda checked cache object differs: ' + name)
    return work, r


def build():
    work, r = identity()
    if (HERE / 'BUILD-LAUNCH.json').exists():
        raise ValueError('lambda dependency build already launched; poll original process')
    s.changed({HERE / 'BUILD-LAUNCH.json': json.dumps(dict(candidate=str(work), complete=False,
        preparation_sha256=s.sha((HERE / 'PREPARATION.json').read_bytes())), indent=2) + '\n'})
    commands = {}
    for module in r['fresh_modules']:
        stem = 'lambda-internal-base-' + module
        commands[stem] = s.run(work, ['bash', 'build-jets.sh', '--coqc', '-q', module.replace('.', '/') + '.v'], stem, 180)
        print('Fresh compiled ' + module, flush=True)
    identity()
    sources = r['fresh_source_hashes']
    s.changed({HERE / 'BUILT.json': json.dumps(dict(candidate=str(work), complete=True, commands=commands,
        preparation_sha256=s.sha((HERE / 'PREPARATION.json').read_bytes()),
        source_objects={name: s.sha((work / name).with_suffix('.vo').read_bytes()) for name in sources},
        normal_registration=False, coverage_added=0), indent=2) + '\n'})
    print('Unchanged scalar-lambda dependencies freshly built; old eight-assumption results are not promoted', flush=True)


if __name__ == '__main__':
    if len(sys.argv) != 2 or sys.argv[1] not in {'prepare', 'build', 'check'}:
        raise SystemExit('usage: prepare.py prepare|build|check')
    if sys.argv[1] == 'check':
        print(identity()[0])
    else:
        {'prepare': prepare, 'build': build}[sys.argv[1]]()
