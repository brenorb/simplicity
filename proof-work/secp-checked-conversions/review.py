"""Validate exact proof-only repairs and the independently checked closure."""
import argparse
import importlib.util
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('checked_conversion_driver', HERE / 'run.py')
run = importlib.util.module_from_spec(spec)
spec.loader.exec_module(run)
gate, REPO = run.gate, run.REPO


def validate(work):
    meta = json.loads((work / 'ASSEMBLY.json').read_text())
    receipt = json.loads((work / 'REVIEW.json').read_text())
    if (meta['candidate'] != str(work) or meta['roots'] != run.ROOTS or
            meta['shared_commit'] != run.SHARED_COMMIT or meta['normal_registration'] is not False or
            meta['coverage_added'] != 0 or receipt['candidate'] != str(work) or
            receipt['assembly_sha256'] != gate.sha((work / 'ASSEMBLY.json').read_bytes()) or
            receipt['main_installation'] is not False or receipt['coverage_added'] != 0 or
            receipt['normal_registration'] is not False):
        raise ValueError('wrong audit scope')
    if meta['staged_patch_sha256'] != gate.index_hash():
        raise ValueError('preexisting index changed')
    compiled = set(re.findall(r'(?m)^COQC (\S+\.v)$', (work / 'build.log').read_text()))
    graph, results, repairs = {}, [], []
    for entry in meta['modules']:
        logical = entry['logical']
        name = logical[2:]
        if entry['relative'] != 'C/' + name + '.v' or entry['origin'] != 'Coq/C/' + name + '.v':
            raise ValueError('incorrect source binding')
        if logical == 'C.jet_frame_constructible_secp':
            original = run.subprocess.check_output(['git', 'show', run.SHARED_COMMIT + ':' + entry['origin']], cwd=REPO).decode()
        else:
            original = (REPO / entry['origin']).read_text()
            if name in run.REPAIRS and gate.sha(original.encode()) != entry['origin_sha256']:
                ledger = json.loads((HERE / 'INSTALLATION.json').read_text())
                if (entry['origin'] not in ledger['repairs'] or
                        ledger['repairs'][entry['origin']]['after_sha256'] != gate.sha(original.encode())):
                    raise ValueError('unreviewed main repair')
                original = run.subprocess.check_output(
                    ['git', 'show', ledger['base_commit'] + ':' + entry['origin']], cwd=REPO).decode()
        if gate.sha(original.encode()) != entry['origin_sha256']:
            raise ValueError('original source changed')
        expected = run.repaired(name, original) if name in run.REPAIRS else original
        actual = (work / 'Coq' / entry['relative']).read_text()
        if expected != actual or gate.sha(actual.encode()) != entry['sha256']:
            raise ValueError('non-proof-only repair or copied-source drift')
        code = gate.safe_source(actual, logical)
        deps = sorted(set(re.findall(r"\b(C\.[\w']+)", code)) - {logical})
        if deps != entry['dependencies'] or logical in graph:
            raise ValueError('dependency graph drift')
        graph[logical] = deps
        if entry['repaired_lemmas'] != run.REPAIRS.get(name, []):
            raise ValueError('incorrect repair inventory')
        repairs += [logical + '.' + lemma for lemma in entry['repaired_lemmas']]
        if logical in run.ROOTS:
            if entry['relative'] not in compiled:
                raise ValueError('repaired/new module not freshly compiled')
            results += [logical + '.' + lemma for lemma in re.findall(r'^(?:Theorem|Lemma)\s+(\w+)', code, re.M)]
        key = str(Path('Coq', entry['relative']).with_suffix('.vo'))
        if key not in receipt['evidence_sha256']:
            raise ValueError('missing compiled object evidence')
    seen = set()
    def visit(logical):
        if logical not in seen:
            seen.add(logical)
            for dep in graph[logical]:
                visit(dep)
    for logical in run.ROOTS:
        visit(logical)
    if seen != set(graph) or receipt['results'] != results or len(repairs) != 4:
        raise ValueError('wrong closure/result inventory')
    for rel, digest in receipt['evidence_sha256'].items():
        path = work / rel
        if not path.is_relative_to(work) or path.is_symlink() or gate.sha(path.read_bytes()) != digest:
            raise ValueError('object/terminal evidence drift')
    deps = gate.reports.assumptions((work / 'assumptions.log').read_text())
    if ({n: sorted(ds) for n, ds in deps.items()} != receipt['dependencies'] or set(deps) != set(results)
            or any(not ds <= gate.SIX for ds in deps.values()) or any(deps[n] for n in repairs)):
        raise ValueError('unreviewed assumptions')
    output = (work / 'contracts.log').read_text()
    if '...' in output or re.findall(r'(?m)^CHECKED_TYPE (\S+)$', output) != results:
        raise ValueError('incomplete types')
    for key, command in {
        'build': ['bash', 'build-jets.sh', '-j2'],
        'assumptions': ['bash', 'build-jets.sh', '--coqc', '-q', str(work / 'assumptions.v')],
        'contracts': ['bash', 'build-jets.sh', '--coqc', '-q', str(work / 'contracts.v')],
        'kernel': ['bash', 'build-jets.sh', '--coqchk', '-o'] + run.ROOTS,
    }.items():
        evidence = receipt[key]
        if (evidence['command'] != command or evidence['exit_code'] != 0 or
                evidence['log_sha256'] != gate.sha((work / (key + '.log')).read_bytes())):
            raise ValueError('wrong command, flags, exit status or terminal log')
    gate.kernel.kernel((work / 'kernel.log').read_text(),
                       sorted((REPO / 'Coq/C/jet_coqchk_axioms.expected').read_text().split()))
    pure = REPO / 'Coq/Simplicity'
    if any(p.read_bytes() != (work / 'Coq/Simplicity' / p.relative_to(pure)).read_bytes() for p in pure.rglob('*.v')):
        raise ValueError('canonical Coq source substitution')
    return meta, receipt


def finish(work):
    meta, receipt = validate(work)
    if gate.inputs.fingerprint(REPO / 'Coq', REPO) != meta['main_inputs_sha256']:
        raise ValueError('main input drift')
    copied = ['regenerate-secp-jets.sh', 'jet_secp_translation_unit.c', 'clightgen-linux.ini.in']
    gate.changed({work / 'Coq/C' / n: (REPO / 'Coq/C' / n).read_text() for n in copied})
    (work / 'C').symlink_to(REPO / 'C', target_is_directory=True) if not (work / 'C').exists() else None
    ast = gate.run(work, ['bash', 'C/regenerate-secp-jets.sh', str(work / 'regenerated.v')], 'AST', 120)
    if (work / 'regenerated.v').read_bytes() != (work / 'Coq/C/jets_secp.v').read_bytes():
        raise ValueError('production secp AST mismatch')
    definitions = ['C.jet_frame_constructible_secp.secp_jet_runs_on_fresh_frames']
    lines = ['Require C.jet_frame_constructible_secp.', 'Set Printing All.',
             'Set Printing Width 120.', 'Set Printing Depth 1000000.']
    for name in definitions:
        lines += ['Goal True. idtac "CHECKED_DEF ' + name + '". exact I. Qed.', 'Print ' + name + '.']
    gate.changed({work / 'definitions.v': '\n'.join(lines) + '\n'})
    printed = gate.run(work, ['bash', 'build-jets.sh', '--coqc', '-q', str(work / 'definitions.v')], 'definitions', 120)
    output = (work / 'definitions.log').read_text()
    if '...' in output or re.findall(r'(?m)^CHECKED_DEF (\S+)$', output) != definitions:
        raise ValueError('incomplete fresh-frame definition')
    tests = gate.run(work, [sys.executable, '-B', str(HERE / 'test-review.py'), str(work)], 'negative-tests', 180)
    for entry in meta['modules']:
        if entry['logical'] in run.ROOTS:
            gate.changed({HERE / 'source' / (Path(entry['relative']).name + '.source'):
                          (work / 'Coq' / entry['relative']).read_text()})
    validate(work)
    record = {'review_sha256': gate.sha((work / 'REVIEW.json').read_bytes()),
              'AST': ast, 'definitions': printed, 'negative_tests': tests,
              'artifact_sha256': {n: gate.sha((work / n).read_bytes()) for n in
                                  ['regenerated.v', 'AST.log', 'definitions.v', 'definitions.log', 'negative-tests.log']},
              'production_input_sha256': {n: gate.sha((REPO / 'Coq/C' / n).read_bytes()) for n in copied},
              'tool_sha256': {n: gate.sha((HERE / n).read_bytes()) for n in
                             ['run.py', 'review.py', 'test-review.py', 'preservation.py', 'install.py']},
              'coverage_added': 0, 'normal_registration': False, 'main_installation': False}
    run.write(HERE / 'EXTRA_REVIEW.json', record)
    print('Exact proof-only delta, fresh-frame predicate and original production AST reviewed', flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('action', choices=['validate', 'finish'])
    parser.add_argument('work')
    args = parser.parse_args()
    globals()[args.action](Path(args.work).resolve())
