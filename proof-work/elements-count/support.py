"""Count-audit utilities without a dependency on an unpushed Git snapshot.

Reuse the repository's standalone scanners, fingerprint, report parser and
kernel-context checker. Missing historical object caches cause fresh builds.
"""
import hashlib
import importlib.util
import os
from pathlib import Path
import re
import subprocess

REPO = Path(__file__).resolve().parents[2]
HERE = REPO / 'proof-work/claude-remainder-integration'


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


patcher = load('count_standalone_patcher', REPO / 'proof-work/nullable-admission/assemble.py')
inputs = load('count_standalone_inputs', REPO / 'Coq/jet-audit-inputs.py')
scanner = load('count_standalone_scanner', REPO / 'Coq/scan-jet-proofs.py')
reports = load('count_standalone_reports', REPO / 'proof-work/scalar-multiply-integration/review-normal.py')
kernel = load('count_standalone_kernel', REPO / 'proof-work/scalar-mul/review.py')
SIX = {'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep',
       'ClassicalDedekindReals.sig_forall_dec', 'ClassicalDedekindReals.sig_not_dec',
       'Events.external_functions_sem', 'Events.inline_assembly_sem'}
ENV = dict(os.environ)
deps = Path(ENV.get('JET_DEPS', str(Path.home() / '.cache/simplicity-jet-deps')))
ENV.setdefault('COMPCERT', str(deps / 'compcert-3.14'))
ENV.setdefault('JET_SYSROOT', str(deps / 'sysroot-glibc-2.36'))
coq_bin = ENV.get('JET_COQ_BIN', '/nix/store/57myhb98wx8k9dr21cf51bsmvxjs67h6-coq-8.17.1/bin')
if Path(coq_bin).is_dir():
    ENV['PATH'] = coq_bin + os.pathsep + ENV.get('PATH', '')


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def changed(changes):
    actual = {p: s for p, s in changes.items() if not p.exists() or p.read_text().splitlines() != s.splitlines()}
    if actual:
        patcher.patch_files(actual)


def safe_source(source, origin):
    code = scanner.code_only(source)
    if scanner.violations(source) or re.search(r'\b(?:vm_cast_no_check|native_cast_no_check)\b', code):
        raise ValueError('forbidden proof construct: ' + origin)
    return code


def index_hash():
    return sha(subprocess.check_output(['git', 'diff', '--cached', '--binary'], cwd=REPO))


def input_map():
    result = {}
    for label, root, suffixes in [
        ('Coq', REPO / 'Coq', {'.v', '.c', '.sh', '.py', '.txt', '.tsv', '.expected'}),
        ('C', REPO / 'C', {'.c', '.h', '.inc', '.S', '.s'}), ('Haskell', REPO / 'Haskell', {'.hs'}),
    ]:
        for p in sorted(root.rglob('*')):
            if p.is_file() and '__pycache__' not in p.parts and (
                p.suffix in suffixes or p.name.startswith('_CoqProject') or p.name == 'clightgen-linux.ini.in'
            ):
                result[label + '/' + str(p.relative_to(root))] = sha(p.read_bytes())
    return result


def run(work, command, stem, timeout=5400):
    with (work / (stem + '.log')).open('wb') as log:
        result = subprocess.run(command, cwd=work / 'Coq', env=ENV, stdout=log,
                                stderr=subprocess.STDOUT, timeout=timeout)
    if result.returncode:
        raise ValueError('failed ' + stem + '; see ' + str(work / (stem + '.log')))
    return {'command': command, 'exit_code': 0, 'log_sha256': sha((work / (stem + '.log')).read_bytes())}


def preservation():
    # This older additive ledger remains a local post-installation check;
    # preparation/compilation/review do not depend on its historical Git ref.
    import json
    baseline = json.loads((HERE / 'BASELINE.json').read_text())
    expected = dict(baseline['inputs'])
    for p in HERE.glob('*/INSTALLATION.json'):
        for name, value in json.loads(p.read_text())['sources'].items():
            if name in expected and expected[name] != value:
                raise ValueError('non-additive source overwrite')
            expected[name] = value
    policy = load('count_checked_conversion_policy', REPO / 'proof-work/secp-checked-conversions/preservation.py')
    expected = policy.apply_reviewed_repairs(expected, REPO)
    if index_hash() != baseline['staged_patch_sha256'] or input_map() != expected:
        raise ValueError('original staged/main inputs changed')
