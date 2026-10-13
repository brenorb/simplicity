"""Independent fresh SHA startup compilation, deep records and kernel audit."""
import argparse
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('startup_stage', HERE / 'stage.py')
stage = importlib.util.module_from_spec(spec); spec.loader.exec_module(stage)
normal = stage.load('startup_reports', HERE.parent / 'scalar-multiply-integration/review-normal.py')
kernel = stage.load('startup_kernel', HERE.parent / 'scalar-mul/review.py')
ENV = dict(os.environ, PATH='/nix/store/57myhb98wx8k9dr21cf51bsmvxjs67h6-coq-8.17.1/bin:' + os.environ['PATH'],
           PYTHONDONTWRITEBYTECODE='1')


def run(candidate, command, stem, timeout=900, combined=False):
    with (candidate / (stem + '.out')).open('wb') as out, (candidate / (stem + '.err')).open('wb') as err:
        done = subprocess.run(command, cwd=candidate / 'Coq', env=ENV, stdout=out,
                              stderr=subprocess.STDOUT if combined else err, timeout=timeout)
    if done.returncode or (not combined and (candidate / (stem + '.err')).read_bytes()):
        raise ValueError('failed check: ' + stem)
    return {'exit_code': done.returncode, 'output_sha256': stage.patch.sha((candidate / (stem + '.out')).read_bytes())}


def check(candidate):
    meta = json.loads((candidate / 'ASSEMBLY.json').read_text())
    coq = candidate / 'Coq'
    if candidate.resolve() != Path(meta['candidate']).resolve(): raise ValueError('candidate identity')
    for e in meta['modules']:
        if stage.patch.sha((candidate / e['path']).read_bytes()) != e['sha256']: raise ValueError('source drift')
    for path, value in meta['inherited_sha256'].items():
        if stage.patch.sha((candidate / path).read_bytes()) != value: raise ValueError('inherited source drift')
    builds = {}
    for name in meta['compile_order']:
        builds[name] = run(candidate, ['bash', 'build-jets.sh', '--coqc', '-q', 'C/' + name + '.v'], 'compile-' + name)
    require = ['Set Warnings "-notation-overridden".'] + ['Require C.' + e['name'] + '.' for e in meta['modules']]
    results = ['C.' + e['name'] + '.' + n for e in meta['modules'] for n in e['results']]
    definitions = []
    for e in meta['modules']:
        code = stage.scanner.code_only((candidate / e['path']).read_text())
        definitions += ['C.' + e['name'] + '.' + n for n in re.findall(r'^(?:Definition|Fixpoint|Inductive)\s+(\w+)', code, re.M)]
    assumptions = require[:]
    for full in results:
        assumptions += ['Goal True. idtac "JET_ASSUMPTIONS ' + full + '". exact I. Qed.', 'Print Assumptions ' + full + '.']
    types = require + ['Set Printing All.', 'Set Printing Width 120.', 'Set Printing Depth 1000000.']
    wanted = [('TYPE', n) for n in results] + [('DEF', n) for n in definitions]
    for kind, full in wanted:
        types += ['Goal True. idtac "SHA_STARTUP_' + kind + ' ' + full + '". exact I. Qed.',
                  ('Check ' if kind == 'TYPE' else 'Print ') + full + '.']
    stage.patch.patch_files({candidate / 'assumptions.v': '\n'.join(assumptions) + '\n',
                             candidate / 'contracts.v': '\n'.join(types) + '\n'})
    a = run(candidate, ['bash', 'build-jets.sh', '--coqc', '-q', str(candidate / 'assumptions.v')], 'assumptions')
    deps = normal.assumptions((candidate / 'assumptions.out').read_text())
    if set(deps) != set(results): raise ValueError('assumption inventory drift')
    t = run(candidate, ['bash', 'build-jets.sh', '--coqc', '-q', str(candidate / 'contracts.v')], 'contracts')
    text = (candidate / 'contracts.out').read_text()
    if '...' in text or re.findall(r'(?m)^SHA_STARTUP_(TYPE|DEF) (\S+)$', text) != wanted:
        raise ValueError('missing/truncated/reordered deep record')
    k = run(candidate, ['bash', 'build-jets.sh', '--coqchk', '-silent', '-o'] + ['C.' + e['name'] for e in meta['modules']],
            'kernel', timeout=5400, combined=True)
    kernel.kernel((candidate / 'kernel.out').read_text(),
                  sorted((coq / 'C/jet_coqchk_axioms.expected').read_text().split()))
    receipt = {'candidate': str(candidate), 'source_commit': meta['shared_commit'],
               'new_modules': len(meta['modules']), 'results': len(results), 'definitions': len(definitions),
               'closed_results': sum(not d for d in deps.values()), 'builds': builds,
               'assumption_check': a, 'contract_check': t, 'kernel_check': k,
               'assumptions': {n: sorted(ds) for n, ds in deps.items()},
               'main_inputs_untouched': True, 'normal_registry_admission': False, 'coverage_added': 0}
    stage.patch.patch_files({candidate / 'REVIEW.json': json.dumps(receipt, indent=2) + '\n'})
    print(json.dumps({k: v for k, v in receipt.items() if k not in {'builds', 'assumptions'}}, indent=2))


if __name__ == '__main__':
    cli = argparse.ArgumentParser(); cli.add_argument('--candidate', type=Path, required=True)
    check(cli.parse_args().candidate.resolve())
