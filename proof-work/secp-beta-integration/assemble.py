"""Materialize the exact checked beta closure as ordinary project modules.

Only a new external candidate is written. Current staging, historical receipts,
checked build trees and the frozen C/specification targets are not modified.
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
SOURCE_REV = 'f03579afc8b151fc87178ff55f9e421e9c011b76'
sp = importlib.util.spec_from_file_location('beta_public_integration_basis', HERE.parent / 'secp-beta-public/verify.py')
p = importlib.util.module_from_spec(sp)
sp.loader.exec_module(p)
s = p.s
old = s.load('beta_ordinary_rename', HERE.parent / 'secp-field-integration/assemble.py')
MAPPING = {
    'FieldBorrow.Borrow': 'C.jet_borrowed_region',
    'FieldBorrowed.Transport': 'C.jet_secp_multiply_borrowed_transport',
    'FieldBorrowed.Runs': 'C.jet_secp_multiply_borrowed_runs',
    'FieldBorrowed.Body': 'C.jet_secp_multiply_borrowed_body',
    'FieldBorrowed.Call': 'C.jet_secp_multiply_borrowed_call',
    'BetaGlobal.Global': 'C.jet_secp_beta_global',
    'BetaGlobal.Inputs': 'C.jet_secp_beta_inputs',
    'BetaGlobal.Spec': 'C.jet_secp_beta_spec',
    'BetaGlobal.Call': 'C.jet_secp_beta_from_reader',
    'InternalFrame.Internal': 'C.jet_clight_internal_frame',
    'InternalFrame.Multiply': 'C.jet_secp_beta_multiply_frame',
    'InternalFrame.Observed': 'C.jet_secp_beta_multiply_ready',
    'BetaPublic.Preserve': 'C.jet_clight_internal_preserve',
    'BetaPublic.Graph': 'C.jet_secp_beta_graph',
    'BetaPublic.State': 'C.jet_secp_beta_state',
    'BetaPublic.Chain': 'C.jet_secp_beta_chain',
    'BetaPublic.Rest': 'C.jet_secp_beta_rest',
    'BetaPublic.Public': 'C.jet_secp_beta_public',
    'BetaPublic.Local': 'C.jet_secp_beta_local',
}
ROOT = MAPPING['BetaPublic.Local']


def blob(path, rev=SOURCE_REV):
    return subprocess.check_output(['git', 'show', rev + ':' + path], cwd=REPO)


def originals():
    r = json.loads(blob('proof-work/secp-beta-public/RUN.json'))
    checked = json.loads(blob('proof-work/secp-beta-public/CHECKED.json'))
    if (not checked['recursive_kernel_check'] or checked['kernel']['exit_code'] or
            checked['run_sha256'] != s.sha(blob('proof-work/secp-beta-public/RUN.json')) or
            not checked['whole_beta_jet_proved'] or checked['shared_acceptance']):
        raise ValueError('expected the completed unregistered public beta proof')
    extensions = r['inherited_extension_source_objects'] | r['own_sources_objects']
    if len(r['loaded_local_source_objects']) != 230 or set(extensions) != set(MAPPING):
        raise ValueError('unexpected checked beta source closure')
    return r, extensions


def source_index():
    index = {}
    names = subprocess.check_output(['git', 'ls-tree', '-r', '--name-only', SOURCE_REV,
        'proof-work'], cwd=REPO, text=True).splitlines()
    for name in names:
        path = REPO / name
        if name.endswith('.v.source') and path.is_file():
            index.setdefault(s.sha(path.read_bytes()), []).append(name)
    return index


def source_payloads():
    r, extensions = originals()
    historical = json.loads(blob('proof-work/secp-field-integration/PREPARATION.json'))
    index = source_index()
    sources = {}
    for name, row in r['loaded_local_source_objects'].items():
        target = 'Coq/' + name
        origin, rev = target, SOURCE_REV
        try:
            raw = blob(origin)
        except subprocess.CalledProcessError:
            raw = b''
        if s.sha(raw) != row['source_sha256']:
            parent = historical['sources'][target]
            origin, rev = parent['origin'], historical['source_revision']
            raw = blob(origin, rev)
            if parent['renamed']:
                raw = old.rename(raw.decode(), historical['module_renaming']).encode()
        if s.sha(raw) != row['source_sha256']:
            raise ValueError('cannot reconstruct exact checked source: ' + target)
        sources[target] = dict(origin=origin, origin_revision=rev, raw=raw, renamed=False)
    for module, row in extensions.items():
        matches = [(name, blob(name)) for name in index.get(row['source_sha256'], [])]
        matches = [(name, raw) for name, raw in matches if s.sha(raw) == row['source_sha256']]
        if not matches:
            raise ValueError('missing committed checked extension: ' + module)
        origin, original = matches[0]
        raw = old.rename(original.decode(), MAPPING).encode()
        if old.rename(raw.decode(), {v: k for k, v in MAPPING.items()}) != original.decode():
            raise ValueError('module-only rename not exactly reversible: ' + module)
        s.safe_source(raw.decode(), MAPPING[module])
        sources['Coq/' + MAPPING[module].replace('.', '/') + '.v'] = dict(origin=origin,
            origin_revision=SOURCE_REV, raw=raw, original_module=module,
            original_sha256=s.sha(original), renamed=True)
    return sources


def prepare():
    if (HERE / 'PREPARATION.json').exists():
        raise ValueError('beta integration preparation already completed')
    p.check()
    before, index = s.input_map(), s.index_hash()
    payloads = source_payloads()
    work = Path(tempfile.mkdtemp(prefix='jet-beta-integration-', dir='/private/tmp'))
    raw = subprocess.check_output(['git', 'archive', SOURCE_REV, 'Coq', 'C', 'Haskell'], cwd=REPO)
    with tarfile.open(fileobj=io.BytesIO(raw)) as archive:
        archive.extractall(work, filter='data')
    if any((work / 'Coq').rglob('*.vo')):
        raise ValueError('candidate unexpectedly contains prebuilt local objects')
    sources, changes = {}, {}
    for name, row in payloads.items():
        target = work / name
        if row['renamed'] and target.exists():
            raise ValueError('ordinary module collision: ' + name)
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
        raise ValueError('checkout/staging changed during isolated preparation')
    r = dict(candidate=str(work), source_revision=SOURCE_REV, root=ROOT, sources=sources,
        projects=projects, module_renaming=MAPPING, main_inputs=before, staged_patch_sha256=index,
        parent_checked_sha256=s.sha(blob('proof-work/secp-beta-public/CHECKED.json')),
        assembler_sha256=s.sha(Path(__file__).read_bytes()), rename_helper_sha256=s.sha(Path(old.__file__).read_bytes()),
        normal_registration=False, coverage_added=0)
    s.changed({HERE / 'PREPARATION.json': json.dumps(r, indent=2) + '\n'})
    print('Prepared ' + str(work) + ': 230 exact inherited sources, 19 reversible ordinary-module extensions', flush=True)


def identity():
    r = json.loads((HERE / 'PREPARATION.json').read_text())
    work = Path(r['candidate'])
    if (work == REPO or REPO in work.parents or work.is_symlink() or r['source_revision'] != SOURCE_REV or
            r['assembler_sha256'] != s.sha(Path(__file__).read_bytes()) or
            r['rename_helper_sha256'] != s.sha(Path(old.__file__).read_bytes()) or
            r['parent_checked_sha256'] != s.sha(blob('proof-work/secp-beta-public/CHECKED.json')) or
            r['main_inputs'] != s.input_map() or r['staged_patch_sha256'] != s.index_hash()):
        raise ValueError('beta integration preparation identity differs')
    payloads = source_payloads()
    if set(r['sources']) != set(payloads):
        raise ValueError('ordinary beta source inventory differs')
    for name, row in payloads.items():
        path = work / name
        if path.is_symlink() or path.read_bytes() != row['raw'] or s.sha(path.read_bytes()) != r['sources'][name]['sha256']:
            raise ValueError('ordinary beta source differs from committed checked proof: ' + name)
    for name, row in r['projects'].items():
        if s.sha((work / 'Coq' / name).read_bytes()) != row['sha256']:
            raise ValueError('ordinary beta project changed: ' + name)
    return work, r


def build():
    work, r = identity()
    if (HERE / 'BUILD-LAUNCH.json').exists():
        raise ValueError('normal beta build already launched; poll original process')
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
    for stem, cmd in zip(['beta-normal-makefile', 'beta-normal-build'], commands):
        rows[stem] = s.run(work, cmd, stem, 1800)
        print('Passed ' + stem, flush=True)
    identity()
    objects = {name: s.sha((work / name).with_suffix('.vo').read_bytes()) for name in r['sources']}
    s.changed({HERE / 'BUILT.json': json.dumps(dict(candidate=str(work), complete=True, commands=rows,
        preparation_sha256=s.sha((HERE / 'PREPARATION.json').read_bytes()), source_objects=objects,
        normal_registration=False, coverage_added=0), indent=2) + '\n'})
    print('Normal dependency graph freshly source-built the complete 249-module beta closure', flush=True)


if __name__ == '__main__':
    if len(sys.argv) != 2 or sys.argv[1] not in {'prepare', 'build', 'check'}:
        raise SystemExit('usage: assemble.py prepare|build|check')
    if sys.argv[1] == 'check':
        print(identity()[0])
    else:
        {'prepare': prepare, 'build': build}[sys.argv[1]]()
