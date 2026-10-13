"""Check the additive foundation batch, without updating jet registries.

Build in a fresh copy of the completed lambda acceptance tree.  All inherited
proof sources present in the checkout must agree, and all imported new sources
are hash-pinned. The independent kernel traverses the entire dependency chain.
No registry snapshot is generated or accepted by this command.
"""
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import resource
import shutil
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
REPO = HERE.parent.parent
MANIFEST = json.loads((HERE / 'manifest.json').read_text())
COQ_BIN = '/nix/store/57myhb98wx8k9dr21cf51bsmvxjs67h6-coq-8.17.1/bin'
INHERITED = {
    'Classical_Prop.classic',
    'FunctionalExtensionality.functional_extensionality_dep',
    'ClassicalDedekindReals.sig_forall_dec',
    'ClassicalDedekindReals.sig_not_dec',
    'Events.external_functions_sem', 'Events.inline_assembly_sem',
}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def validate_sources():
    scanner = load(REPO / 'Coq/scan-jet-proofs.py', 'foundation_scanner')
    for row in MANIFEST['modules']:
        path = REPO / row['path']
        if sha(path) != row['sha256']:
            raise ValueError('imported source drift: ' + row['path'])
        source = path.read_text()
        if scanner.violations(source) or re.search(r'\b\w*no_check\b', scanner.code_only(source)):
            raise ValueError('proof escape command: ' + row['path'])
        if re.findall(r'^(?:Lemma|Theorem|Corollary)\s+(\w+)', source, re.M) != row['results']:
            raise ValueError('declaration inventory drift')


def parse_assumptions(text, wanted):
    result, current, active = {}, None, False
    for line in text.splitlines():
        if line.startswith(('FOUNDATION_TYPE ', 'FOUNDATION_DEF ')):
            active = False
            current = None
        elif line.startswith('FOUNDATION_ASSUMPTIONS '):
            current = line.split()[1]
            if current in result:
                raise ValueError('duplicate assumption record')
            result[current] = set()
            active = False
        elif line.startswith('Axioms:'):
            active = True
        elif line.startswith('Closed under the global context'):
            active = False
        elif active and line and not line[0].isspace():
            if current is None:
                raise ValueError('orphan assumption')
            result[current].add(line.split()[0])
    if set(result) != set(wanted):
        raise ValueError('missing/extra assumption records')
    if any(values - INHERITED for values in result.values()):
        raise ValueError('unexpected theorem assumptions')
    return {name: sorted(values) for name, values in sorted(result.items())}


def kernel(text):
    for marker in ['Constants/Inductives relying on type-in-type: <none>',
                   'unsafe (co)fixpoints: <none>', 'positivity is assumed: <none>']:
        if marker not in text:
            raise ValueError('missing kernel safety result')
    block = text.split('* Axioms:', 1)[1]
    actual = []
    for line in block.splitlines():
        if not line.strip():
            if actual:
                break
            continue
        actual.append(line.strip().split()[0])
    actual.sort()
    expected = sorted((REPO / 'Coq/C/jet_coqchk_axioms.expected').read_text().split())
    if actual != expected:
        raise ValueError('inherited library kernel context changed')


def contract_records(text, wanted):
    if '...' in text or re.findall(r'(?m)^FOUNDATION_(TYPE|DEF) (\S+)$', text) != wanted:
        raise ValueError('missing, duplicate, reordered or truncated contract records')


def apply_new(path, source):
    patch = '*** Begin Patch\n*** Add File: ' + str(path) + '\n'
    patch += '\n'.join('+' + line for line in source.splitlines())
    patch += '\n*** End Patch\n'
    subprocess.run(['apply_patch'], input=patch, text=True, check=True,
                   stdout=subprocess.DEVNULL)


def build():
    validate_sources()
    soft, hard = resource.getrlimit(resource.RLIMIT_STACK)
    stack = 65520 * 1024
    if soft != resource.RLIM_INFINITY and soft < stack:
        raise ValueError('launch with: ulimit -s 65520; python3 -B check.py --build')
    base = Path(MANIFEST['baseline_coq'])
    audit = load(base / 'jet-audit-inputs.py', 'foundation_baseline_audit')
    if audit.fingerprint(base, REPO) != MANIFEST['baseline_acceptance_fingerprint']:
        raise ValueError('completed acceptance tree drift')
    log = Path(MANIFEST['baseline_acceptance_log']).read_text()
    if not log.rstrip().endswith('all jet acceptance checks passed (build, kernel, reviewed snapshots, negative tests, four ASTs)'):
        raise ValueError('baseline did not finish acceptance')
    for source in base.rglob('*.v'):
        current = REPO / 'Coq' / source.relative_to(base)
        if current.is_file() and current.read_bytes() != source.read_bytes():
            raise ValueError('inherited checkout proof drift: ' + str(current))
    work = Path(tempfile.mkdtemp(prefix='jet-shared-foundations.', dir='/tmp'))
    coq = work / 'Coq'
    shutil.copytree(base, coq, symlinks=True)
    env = dict(os.environ, PATH=COQ_BIN + ':' + os.environ['PATH'], PYTHONDONTWRITEBYTECODE='1')
    print('scratch:', work, flush=True)
    if subprocess.check_output(['coqc', '--version'], env=env, text=True).splitlines()[0] != 'The Coq Proof Assistant, version 8.17.1':
        raise ValueError('wrong compiler')
    records, reports, modules = [], [], []
    for row in MANIFEST['modules']:
        path = Path(row['path']).relative_to('Coq')
        shutil.copyfile(REPO / row['path'], coq / path)
        module = 'C.' + path.stem
        modules.append(module)
        records += [('TYPE', module + '.' + name) for name in row['results']]
        reports += [module + '.' + name for name in row['results']]
    definitions = [('DEF', 'C.' + Path(row['path']).stem + '.' + name)
                   for row in MANIFEST['modules'] for name in row['definitions']]
    records += definitions
    driver = ['Set Warnings "-notation-overridden".']
    driver += ['Require ' + module + '.' for module in modules]
    driver += ['Set Printing All.', 'Set Printing Width 120.', 'Set Printing Depth 1000000.']
    for name in reports:
        driver += ['Goal True. idtac "FOUNDATION_ASSUMPTIONS ' + name + '". exact I. Qed.',
                   'Print Assumptions ' + name + '.']
    for kind, name in records:
        driver += ['Goal True. idtac "FOUNDATION_' + kind + ' ' + name + '". exact I. Qed.',
                   ('Check ' if kind == 'TYPE' else 'Print ') + name + '.']
    apply_new(work / 'foundation_audit.v', '\n'.join(driver) + '\n')
    commands = [(['bash', 'build-jets.sh', '--coqc', '-q', str(Path(row['path']).relative_to('Coq'))],
                 Path(row['path']).stem + '.log') for row in MANIFEST['modules']]
    commands += [(['bash', 'build-jets.sh', '--coqc', '-q', str(work / 'foundation_audit.v')], 'contracts.log'),
                 (['bash', 'build-jets.sh', '--coqchk', '-silent', '-o'] + modules, 'kernel.log')]
    for command, name in commands:
        print('checking:', name, flush=True)
        with (work / name).open('wb') as output:
            done = subprocess.run(command, cwd=coq, env=env, stdout=output, stderr=subprocess.STDOUT,
                                  timeout=1800 if name == 'kernel.log' else 180)
        if done.returncode:
            raise ValueError('failed ' + name + ': ' + (work / name).read_text()[-4000:])
    for row in MANIFEST['modules']:
        if (work / (Path(row['path']).stem + '.log')).read_bytes():
            raise ValueError('unexpected compiler diagnostics')
    text = (work / 'contracts.log').read_text()
    assumptions = parse_assumptions(text, reports)
    contract_records(text, records)
    kernel((work / 'kernel.log').read_text())
    validate_sources()
    evidence = {str(path.relative_to(work)): sha(path) for path in work.glob('*.log')}
    evidence['foundation_audit.v'] = sha(work / 'foundation_audit.v')
    for row in MANIFEST['modules']:
        path = Path(row['path']).relative_to('Coq')
        for suffix in ['.v', '.vo']:
            key = 'Coq/' + str(path.with_suffix(suffix))
            evidence[key] = sha(work / key)
    receipt = {'format': 1, 'scratch': str(work), 'build_exit_code': 0, 'kernel_exit_code': 0,
               'modules': len(modules), 'results': len(reports), 'definitions': len(definitions),
               'assumptions': assumptions, 'closed_results': sum(not values for values in assumptions.values()),
               'evidence_sha256': evidence, 'manifest_sha256': sha(HERE / 'manifest.json'),
               'baseline_acceptance_fingerprint': MANIFEST['baseline_acceptance_fingerprint'],
               'normal_registration': False, 'full_jet_acceptance': False, 'coverage_added': 0}
    print(json.dumps(receipt, indent=2), flush=True)
    return receipt


def verify():
    validate_sources()
    receipt = json.loads((HERE / 'REVIEW.json').read_text())
    if receipt['build_exit_code'] != 0 or receipt['kernel_exit_code'] != 0:
        raise ValueError('failed/nonterminal receipt')
    if receipt['manifest_sha256'] != sha(HERE / 'manifest.json'):
        raise ValueError('manifest drift')
    work = Path(receipt['scratch'])
    for name, value in receipt['evidence_sha256'].items():
        if sha(work / name) != value:
            raise ValueError('checked source/object/driver/log drift: ' + name)
    wanted = [name for row in MANIFEST['modules'] for name in
              ['C.' + Path(row['path']).stem + '.' + result for result in row['results']]]
    if parse_assumptions((work / 'contracts.log').read_text(), wanted) != receipt['assumptions']:
        raise ValueError('assumption snapshot drift')
    records = [('TYPE', name) for name in wanted]
    records += [('DEF', 'C.' + Path(row['path']).stem + '.' + name)
                for row in MANIFEST['modules'] for name in row['definitions']]
    contract_records((work / 'contracts.log').read_text(), records)
    kernel((work / 'kernel.log').read_text())
    print(json.dumps({key: receipt[key] for key in ['modules', 'results', 'definitions',
                     'closed_results', 'build_exit_code', 'kernel_exit_code', 'coverage_added']}, indent=2))


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--build', action='store_true')
    if parser.parse_args().build:
        build()
    else:
        verify()
