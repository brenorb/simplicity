"""Materialize the checked field-multiply closure using ordinary C.* modules.

Only an external, newly created candidate is written. Historical checked trees,
receipts, the checkout's Coq sources and its Git index are never edited.
All proof bytes come from committed blobs, not uncommitted originals or .vo files.
"""
import importlib.util
import io
import json
from pathlib import Path
import re
import subprocess
import sys
import tarfile
import tempfile

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
SOURCE_REV = '727caf164eb492ff50790c4e8284f5c4a6364dc3'
RECEIPT = 'proof-work/secp-field-literal/CHECKED.json'
sp = importlib.util.spec_from_file_location('field_integration_support',
    REPO / 'proof-work/elements-count/support.py')
s = importlib.util.module_from_spec(sp)
sp.loader.exec_module(s)


def blob(name):
    return subprocess.check_output(['git', 'show', SOURCE_REV + ':' + name], cwd=REPO)


def namespaces(receipt):
    extensions = receipt['inherited_extension_sources_objects'] | receipt['extension_sources_objects']
    result = {}
    for old in extensions:
        group, name = old.split('.')
        group = group.removeprefix('Field').removeprefix('Secp').lower()
        result[old] = 'C.jet_secp_multiply_' + group + '_' + name.lower()
    if len(set(result.values())) != len(result):
        raise ValueError('colliding regular module names')
    return result


def rename(code, mapping):
    # Do not rewrite arbitrary substrings, unqualified identifiers, definitions,
    # statements or tactics. Only qualified module-name tokens are changed.
    for group in {m.split('.')[0] for m in mapping}:
        if re.search(r'\bFrom\s+' + re.escape(group) + r'\b', code):
            raise ValueError('unsupported relative From import: ' + group)
    pattern = r'(?<![\w.])(?:' + '|'.join(re.escape(m) for m in sorted(mapping, key=len, reverse=True)) + r')(?!\w)'
    return re.sub(pattern, lambda m: mapping[m[0]], code)


def archive_index():
    names = subprocess.check_output(['git', 'ls-tree', '-r', '--name-only', SOURCE_REV,
        'proof-work'], cwd=REPO, text=True).splitlines()
    result = {}
    # Prefer the dedicated committed dependency archive over pending originals.
    names.sort(key=lambda n: (not n.startswith('proof-work/secp-field-literal/inherited/'), n))
    for name in names:
        if name.endswith('.v.source'):
            p = REPO / name
            if p.is_file():
                result.setdefault(s.sha(p.read_bytes()), []).append(name)
    return result


def archived_source(digest, index):
    for name in index.get(digest, []):
        raw = blob(name)
        if s.sha(raw) == digest:
            return name, raw
    raise ValueError('no committed proof source with SHA-256 ' + digest)


def prepare():
    before, staged = s.input_map(), s.index_hash()
    receipt_raw = blob(RECEIPT)
    r = json.loads(receipt_raw)
    if (not r['recursive_kernel_check'] or r['kernel']['exit_code'] or
            not r['public_jet_equivalence'] or r['normal_registration'] or r['coverage_added']):
        raise ValueError('expected completed, unregistered literal proof')
    mapping, archives = namespaces(r), archive_index()
    if len(mapping) != 59 or len(r['loaded_local_source_objects']) != 176:
        raise ValueError('unexpected checked source closure')
    work = Path(tempfile.mkdtemp(prefix='jet-field-integration-', dir='/private/tmp'))
    raw = subprocess.check_output(['git', 'archive', SOURCE_REV, 'Coq', 'C', 'Haskell'], cwd=REPO)
    with tarfile.open(fileobj=io.BytesIO(raw)) as archive:
        archive.extractall(work, filter='data')
    changes, sources = {}, {}
    for name, row in r['loaded_local_source_objects'].items():
        target = 'Coq/' + name
        path = work / target
        if path.exists() and s.sha(path.read_bytes()) == row['source_sha256']:
            origin, code = target, path.read_bytes()
        else:
            origin, code = archived_source(row['source_sha256'], archives)
            changes[path] = code.decode()
        sources[target] = dict(origin=origin, sha256=s.sha(code), renamed=False)
    extensions = r['inherited_extension_sources_objects'] | r['extension_sources_objects']
    for old, new in mapping.items():
        origin, code = archived_source(extensions[old]['source_sha256'], archives)
        old_code = code.decode()
        new_code = rename(old_code, mapping)
        if rename(new_code, {v: k for k, v in mapping.items()}) != old_code:
            raise ValueError('module renaming is not exactly reversible: ' + old)
        s.safe_source(new_code, new)
        target = 'Coq/' + new.replace('.', '/') + '.v'
        if (work / target).exists():
            raise ValueError('would overwrite an existing proof module: ' + target)
        changes[work / target] = new_code
        sources[target] = dict(origin=origin, original_sha256=s.sha(code), sha256=s.sha(new_code.encode()),
            original_module=old, renamed=True)
    # Existing normal project contents are retained; only missing closure files
    # are appended. Thus the focused make target uses the regular build graph.
    files = sorted(n.removeprefix('Coq/') for n in sources)
    projects = {}
    for project in ['_CoqProject', '_CoqProject.jets']:
        p = work / 'Coq' / project
        original = p.read_text()
        missing = [n for n in files if n not in original.splitlines()]
        updated = original.rstrip() + '\n' + '\n'.join(missing) + '\n'
        changes[p] = updated
        projects[project] = dict(original_sha256=s.sha(original.encode()), sha256=s.sha(updated.encode()),
            appended=missing)
    s.changed(changes)
    result = dict(candidate=str(work), source_revision=SOURCE_REV,
        checked_parent_sha256=s.sha(receipt_raw), module_renaming=mapping,
        sources=sources, projects=projects, main_inputs=before, staged_patch_sha256=staged,
        assembler_sha256=s.sha(Path(__file__).read_bytes()),
        root=mapping['FieldLiteral.Jet'], normal_registration=False, coverage_added=0)
    if before != s.input_map() or staged != s.index_hash():
        raise ValueError('checkout inputs changed during candidate assembly')
    if (HERE / 'PREPARATION.json').exists():
        raise ValueError('candidate preparation already recorded')
    s.changed({HERE / 'PREPARATION.json': json.dumps(result, indent=2) + '\n'})
    print('Prepared ' + str(work) + ': 176 original modules, 59 mechanically renamed modules', flush=True)


def identity():
    r = json.loads((HERE / 'PREPARATION.json').read_text())
    work = Path(r['candidate'])
    if (work == REPO or REPO in work.parents or work.is_symlink() or
            r['source_revision'] != SOURCE_REV or r['assembler_sha256'] != s.sha(Path(__file__).read_bytes()) or
            r['checked_parent_sha256'] != s.sha(blob(RECEIPT)) or r['main_inputs'] != s.input_map() or
            r['staged_patch_sha256'] != s.index_hash()):
        raise ValueError('candidate/preparation/checkout identity changed')
    for name, row in r['sources'].items():
        p = work / name
        original = blob(row['origin']).decode()
        expected = rename(original, r['module_renaming']) if row['renamed'] else original
        if p.is_symlink() or p.read_text() != expected or s.sha(p.read_bytes()) != row['sha256']:
            raise ValueError('candidate source differs from committed proof: ' + name)
    for name, row in r['projects'].items():
        if s.sha((work / 'Coq' / name).read_bytes()) != row['sha256']:
            raise ValueError('candidate normal build project changed: ' + name)
    return work, r


def build():
    work, r = identity()
    if (HERE / 'BUILD-LAUNCH.json').exists():
        raise ValueError('build already launched; poll its existing handle')
    flags = []
    cc = Path(s.ENV['COMPCERT'])
    vst = Path(s.ENV.get('VST', str(cc.parent / 'vst-2.14')))
    for d in ['lib', 'common', 'x86_64', 'x86', 'cfrontend', 'export']:
        flags += ['-R', str(cc / d), 'compcert.' + d]
    flags += ['-R', str(cc / 'flocq'), 'Flocq']
    for d in ['msl', 'sepcomp', 'veric', 'zlist', 'floyd', 'progs64', 'concurrency', 'atomics', 'sha']:
        flags += ['-Q', str(vst / d), 'sha' if d == 'sha' else 'VST.' + d]
    target = r['root'].replace('.', '/') + '.vo'
    commands = [['coq_makefile', '-f', '_CoqProject.jets', *flags, '-o', 'JetMakefile'],
        ['make', '-f', 'JetMakefile', '-j2', target]]
    s.changed({HERE / 'BUILD-LAUNCH.json': json.dumps(dict(candidate=str(work), commands=commands,
        preparation_sha256=s.sha((HERE / 'PREPARATION.json').read_bytes()), complete=False), indent=2) + '\n'})
    rows = {}
    for stem, command in zip(['normal-makefile', 'normal-build'], commands):
        rows[stem] = s.run(work, command, stem, 1800)
        print('Passed ' + stem, flush=True)
    identity()
    objects = {n: s.sha((work / n).with_suffix('.vo').read_bytes()) for n in r['sources']}
    s.changed({HERE / 'BUILT.json': json.dumps(dict(candidate=str(work), commands=rows,
        preparation_sha256=s.sha((HERE / 'PREPARATION.json').read_bytes()),
        source_objects=objects, complete=True, recursive_kernel_check=False,
        normal_registration=False, coverage_added=0), indent=2) + '\n'})
    print('Ordinary C.* build graph compiled the full field-multiply closure', flush=True)


if __name__ == '__main__':
    if len(sys.argv) != 2 or sys.argv[1] not in {'prepare', 'build', 'check'}:
        raise SystemExit('usage: assemble.py prepare|build|check')
    if sys.argv[1] == 'check':
        work, receipt = identity()
        print('Candidate proofs and normal project match the committed checked inputs: ' + str(work))
    elif sys.argv[1] == 'prepare':
        prepare()
    else:
        build()
