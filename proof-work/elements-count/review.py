"""Validate completed count audits and install only their checked new sources."""
import argparse
import importlib.util
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
s = importlib.util.spec_from_file_location('count_finish_driver', HERE / 'run.py')
run = importlib.util.module_from_spec(s)
s.loader.exec_module(run)
gate, REPO = run.gate, run.REPO
NEW = ['jet_elements_count_constructible', 'jet_elements_count_payload']


def validate(work):
    meta = json.loads((work / 'ASSEMBLY.json').read_text())
    receipt = json.loads((work / 'REVIEW.json').read_text())
    if meta.get('group') != 'payload' or meta['roots'] != [run.ROOT, 'C.jet_elements_count_local', 'C.jet_elements_count_payload']:
        raise ValueError('wrong root scope')
    if (receipt['candidate'] != str(work) or receipt['assembly_sha256'] != gate.sha((work / 'ASSEMBLY.json').read_bytes())
            or receipt['normal_registration'] is not False or receipt['coverage_added'] != 0):
        raise ValueError('wrong receipt scope')
    if gate.index_hash() != meta['staged_patch_sha256']:
        raise ValueError('preexisting staged patch changed')
    by_name = {e['logical']: e for e in meta['modules']}
    if len(by_name) != len(meta['modules']):
        raise ValueError('duplicate modules')
    seen = set()
    def visit(name):
        if name not in seen:
            seen.add(name)
            for dep in by_name[name]['dependencies']:
                visit(dep)
    for root in meta['roots']:
        visit(root)
    if seen != set(by_name):
        raise ValueError('wrong dependency closure')
    compiled = set(re.findall(r'(?m)^COQC (\S+\.v)$', (work / 'build.log').read_text()))
    results = []
    for entry in meta['modules']:
        name = entry['logical'][2:]
        archived = name in NEW
        origin = ('proof-work/elements-count/source/' + name + '.v.source') if archived else ('Coq/C/' + name + '.v')
        if entry['origin'] != origin or entry['relative'] != 'C/' + name + '.v':
            raise ValueError('wrong source/program binding')
        raw = (REPO / origin).read_bytes()
        if gate.sha(raw) != entry['sha256'] or raw != (work / 'Coq' / entry['relative']).read_bytes():
            raise ValueError('proof source drift')
        code = gate.safe_source(raw.decode(), origin)
        deps = sorted(set(re.findall(r"\b(C\.[\w']+)", code)) - {entry['logical']})
        if deps != entry['dependencies']:
            raise ValueError('dependency graph drift')
        if (entry['logical'] in run.FRESH or archived) and entry['relative'] not in compiled:
            raise ValueError('new/selected source was not freshly compiled')
        if archived:
            results += [entry['logical'] + '.' + n for n in re.findall(r'^(?:Lemma|Theorem)\s+(\w+)', code, re.M)]
        if 'Coq/' + str(Path(entry['relative']).with_suffix('.vo')) not in receipt['evidence_sha256']:
            raise ValueError('unbound object')
    results += ['C.jet_elements_count_local.elements_num_inputs_local_spec',
                'C.jet_elements_count_local.elements_num_outputs_local_spec']
    if receipt['results'] != results:
        raise ValueError('wrong result inventory')
    for rel, digest in receipt['evidence_sha256'].items():
        path = work / rel
        if not path.is_relative_to(work) or path.is_symlink() or gate.sha(path.read_bytes()) != digest:
            raise ValueError('object/terminal evidence drift')
    dependencies = gate.reports.assumptions((work / 'assumptions.log').read_text())
    if ({n: sorted(d) for n, d in dependencies.items()} != receipt['dependencies'] or set(dependencies) != set(results)
            or any(not d <= gate.SIX for d in dependencies.values())):
        raise ValueError('unreviewed assumptions')
    contracts = (work / 'contracts.log').read_text()
    if '...' in contracts or re.findall(r'(?m)^COUNT_TYPE (\S+)$', contracts) != results:
        raise ValueError('incomplete type inventory')
    expected = {'build': ['bash', 'build-jets.sh', '-j2'],
                'assumptions': ['bash', 'build-jets.sh', '--coqc', '-q', str(work / 'assumptions.v')],
                'contracts': ['bash', 'build-jets.sh', '--coqc', '-q', str(work / 'contracts.v')],
                'AST': ['bash', 'C/regenerate-elements-jets.sh', str(work / 'regenerated.v')],
                'kernel': ['bash', 'build-jets.sh', '--coqchk', '-o'] + meta['roots']}
    for name, command in expected.items():
        evidence = receipt[name]
        if evidence['exit_code'] != 0 or evidence['command'] != command or evidence['log_sha256'] != gate.sha((work / (name + '.log')).read_bytes()):
            raise ValueError('command/exit-status evidence drift')
    if (work / 'regenerated.v').read_bytes() != (REPO / 'Coq/C/jets_elements.v').read_bytes():
        raise ValueError('wrong production AST')
    gate.kernel.kernel((work / 'kernel.log').read_text(), sorted((REPO / 'Coq/C/jet_coqchk_axioms.expected').read_text().split()))
    pure = REPO / 'Coq/Simplicity'
    if any(p.read_bytes() != (work / 'Coq/Simplicity' / p.relative_to(pure)).read_bytes() for p in pure.rglob('*.v')):
        raise ValueError('canonical Coq source substitution')
    return meta, receipt


def finish(work):
    meta, receipt = validate(work)
    if gate.inputs.fingerprint(REPO / 'Coq', REPO) != meta['main_inputs_sha256']:
        raise ValueError('main input drift before installation')
    checks = {}
    for name, script in [('source', 'check-source.py'), ('source-tests', 'test-source.py')]:
        command = [sys.executable, '-B', str(HERE / script)]
        command += ['--repo', str(REPO), '--coq', str(work / 'Coq')] if name == 'source' else [str(REPO), str(work / 'Coq')]
        checks[name] = gate.run(work, command, name, 180)
    checks['evidence-tests'] = gate.run(work, [sys.executable, '-B', str(HERE / 'test-review.py'), str(work)],
                                      'evidence-tests', 180)
    definitions = ['C.jet_elements_count_constructible.elements_constructed_execution',
                   'C.jet_elements_count_payload.elements_count_observation_spec']
    lines = ['Require C.jet_elements_count_constructible C.jet_elements_count_payload.',
             'Set Printing All.', 'Set Printing Width 120.', 'Set Printing Depth 1000000.']
    for name in definitions:
        lines += ['Goal True. idtac "COUNT_DEF ' + name + '". exact I. Qed.', 'Print ' + name + '.']
    gate.changed({work / 'definitions.v': '\n'.join(lines) + '\n'})
    checks['definitions'] = gate.run(work, ['bash', 'build-jets.sh', '--coqc', '-q', str(work / 'definitions.v')], 'definitions', 120)
    output = (work / 'definitions.log').read_text()
    if '...' in output or re.findall(r'(?m)^COUNT_DEF (\S+)$', output) != definitions:
        raise ValueError('incomplete definition inventory')
    validate(work)
    record = {'checks': checks, 'review_sha256': gate.sha((work / 'REVIEW.json').read_bytes()),
              'definitions': definitions, 'normal_registration': False, 'coverage_added': 0,
              'reviewer_sha256': gate.sha(Path(__file__).read_bytes()),
              'source_guard_sha256': gate.sha((HERE / 'check-source.py').read_bytes()),
              'test_guard_sha256': gate.sha((HERE / 'test-source.py').read_bytes())}
    record['evidence_test_sha256'] = gate.sha((HERE / 'test-review.py').read_bytes())
    run.write(HERE / 'payload/EXTRA_REVIEW.json', record)
    print('Full sources, definitions, source correspondence and negative fixtures reviewed', flush=True)


def install(work):
    finish(work)
    before = gate.input_map()
    _, receipt = validate(work)
    sources = {'Coq/C/' + n + '.v': (HERE / 'source' / (n + '.v.source')).read_text() for n in NEW}
    for name in sources:
        if (REPO / name).exists():
            raise ValueError('additive installation would overwrite existing source')
    ledger = {'group': 'elements-count', 'sources': {p: gate.sha(v.encode()) for p, v in sources.items()},
              'new_paths': sorted(sources), 'review_sha256': gate.sha((work / 'REVIEW.json').read_bytes()),
              'current_whole_worktree_full_acceptance': False, 'normal_registration': False, 'coverage_added': 0}
    changes = {REPO / n: value for n, value in sources.items()}
    for directory in [HERE, gate.HERE / 'elements-count', HERE.parent / 'linked-repair/elements-count']:
        changes[directory / 'INSTALLATION.json'] = json.dumps(ledger, indent=2) + '\n'
    gate.changed(changes)
    expected = dict(before)
    expected.update(ledger['sources'])
    if gate.input_map() != expected:
        raise ValueError('non-additive input change')
    gate.preservation()
    print('Two checked count modules installed source-only; normal registration unchanged', flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(); p.add_argument('action', choices=['validate', 'finish', 'install']); p.add_argument('work')
    a = p.parse_args(); globals()[a.action](Path(a.work).resolve())
