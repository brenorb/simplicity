"""Independent whole-delta review before seven-jet full normal acceptance."""
import argparse
import importlib.util
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('seven_registry_gate', HERE / 'admission.py')
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)
support, normal, REPO, MAIN = gate.support, gate.normal, gate.REPO, gate.MAIN


def review(work):
    meta = json.loads((work / 'ASSEMBLY.json').read_text())
    receipt = json.loads((work / 'PREPARATION.json').read_text())
    if (meta['candidate'] != str(work) or receipt['candidate'] != str(work) or
            meta['extensions'] != gate.additions() or meta['coverage_additions'] != gate.COVERAGE or
            meta['new_sources'] != gate.NEW_SOURCES or any(r['coverage_added'] != 7 or r['full_acceptance'] is not False for r in [meta, receipt])):
        raise ValueError('wrong seven-jet admission scope')
    if (support.index_hash() != meta['staged_patch_sha256'] or support.input_map() != meta['main_inputs'] or
            support.inputs.fingerprint(MAIN, REPO) != meta['main_input_sha256']):
        raise ValueError('main source/index drift')
    if meta['prior_preparations_sha256'] != {p.parent.name: support.sha(p.read_bytes()) for p in gate.PRIOR_PATHS}:
        raise ValueError('checked final-name prerequisites changed')
    coq = work / 'Coq'
    mutable = set(gate.METADATA + gate.SCRIPTS)
    for name, digest in meta['main_metadata_sha256'].items():
        if support.sha((MAIN / name).read_bytes()) != digest:
            raise ValueError('original metadata changed')
    for name, digest in meta['main_inputs'].items():
        if name.startswith('Coq/') and name[4:] not in mutable and support.sha((work / name).read_bytes()) != digest:
            raise ValueError('unreviewed inherited source change: ' + name)
    actual = {'Coq/' + str(p.relative_to(coq)) for p in coq.rglob('*') if p.is_file() and '__pycache__' not in p.parts and
              (p.suffix in {'.v', '.c', '.sh', '.py', '.txt', '.tsv', '.expected'} or p.name.startswith('_CoqProject') or p.name == 'clightgen-linux.ini.in')}
    wanted = {n for n in meta['main_inputs'] if n.startswith('Coq/')} | {'Coq/' + n for n in gate.NEW_SOURCES + gate.GUARDS}
    if actual != wanted:
        raise ValueError('unexpected candidate source inventory')
    for n in gate.NEW_SOURCES:
        if (coq / n).read_bytes() != (gate.PRIOR_TREE / 'Coq' / n).read_bytes():
            raise ValueError('new proof differs from checked source')
    for name, rows in meta['extensions'].items():
        if (coq / name).read_text() != (MAIN / name).read_text() + '\n'.join(rows) + '\n':
            raise ValueError('registration is not exact append')
    if (coq / 'C/jet_coverage.tsv').read_text() != (MAIN / 'C/jet_coverage.tsv').read_text() + gate.COVERAGE:
        raise ValueError('wrong coverage additions')
    for name, text in gate.script_changes().items():
        if (coq / name).read_text() != text:
            raise ValueError('unreviewed source/coverage/printer gate edit')
    for name in gate.GUARDS:
        if (coq / name).read_bytes() != (HERE.parent / name).read_bytes():
            raise ValueError('canonical-source/negative test substitution')
    r0, d0 = normal.rows(MAIN / 'C/jet_public_theorems.txt'), normal.rows(MAIN / 'C/jet_contract_definitions.txt')
    r1, d1 = normal.rows(coq / 'C/jet_public_theorems.txt'), normal.rows(coq / 'C/jet_contract_definitions.txt')
    old = normal.contract_records((MAIN / 'C/jet_contracts.expected').read_text(), r0, d0)
    new = normal.contract_records((coq / 'C/jet_contracts.expected').read_text(), r1, d1)
    old_keys = {k for k, _ in old}
    if [(k, t) for k, t in new if k in old_keys] != old:
        raise ValueError('inherited contract bytes/order changed')
    added = [(k, t) for k, t in new if k not in old_keys]
    if len(added) != 516 or len(r1) - len(r0) != 308 or len(d1) - len(d0) != 208:
        raise ValueError('wrong result/definition inventory')
    report = (work / 'new_contracts.log').read_text()
    marks = list(re.finditer(r'(?m)^SEVEN_DEEP_(TYPE|DEF) (\S+)\n', report))
    if [(m[1], m[2]) for m in marks] != [(kind, mod + '.' + name) for (kind, mod, name, _), _ in added]:
        raise ValueError('missing/duplicate/reordered full records')
    supplements = []
    for i, ((_, mod, name, _), compact) in enumerate(added):
        deep = report[marks[i].end():marks[i+1].start() if i+1 < len(marks) else len(report)]
        if '...' in deep or re.search(r'\?[A-Za-z]', deep):
            raise ValueError('truncated/unquantified deep record')
        short, long = re.sub(r'\s+', '', compact), re.sub(r'\s+', '', deep)
        if short == long:
            continue
        position = 0
        fragments = short.split('...')
        for j, fragment in enumerate(fragments):
            offset = len(long) - len(fragment) if j == len(fragments)-1 and long.endswith(fragment) else long.find(fragment, position)
            if offset < position or j == 0 and offset != 0:
                raise ValueError('compact/deep disagreement')
            position = offset + len(fragment)
        if '...' not in short or position != len(long):
            raise ValueError('unexplained compact/deep difference')
        supplements.append(mod + '.' + name)
    old_deps = gate.snapshot_deps((MAIN / 'C/jet_assumptions.expected').read_text())
    new_deps = gate.snapshot_deps((coq / 'C/jet_assumptions.expected').read_text())
    if {n: new_deps.get(n) for n in old_deps} != old_deps:
        raise ValueError('inherited assumption sets changed')
    fresh = normal.assumptions((work / 'new_assumptions.log').read_text())
    prior_deps = {n: ds for r in gate.PRIORS for n, ds in r['dependencies'].items()}
    fresh_sorted = {n: sorted(ds) for n, ds in fresh.items()}
    if (set(fresh) != {m + '.' + n for m, n in r1[len(r0):]} or receipt['new_dependencies'] != fresh_sorted or
            {n: ds for n, ds in new_deps.items() if n not in old_deps} != fresh_sorted or
            any(not ds <= support.SIX or sorted(ds) != prior_deps[n] for n, ds in fresh.items())):
        raise ValueError('checked new dependency sets changed')
    pure = gate.PRIORS[0]['pure_results']
    if len(pure) != 3 or any(fresh[n] for n in pure):
        raise ValueError('pure timelock bridges no longer closed')
    commands = {'build': (receipt['build'], ['bash', 'build-jets.sh', '-j2'], 'build'),
                'contracts': (receipt['contracts'], ['bash', 'build-jets.sh', '--coqc', '-q', str(work / 'new_contracts.v')], 'new_contracts'),
                'assumptions': (receipt['assumptions'], ['bash', 'build-jets.sh', '--coqc', '-q', str(work / 'new_assumptions.v')], 'new_assumptions')}
    if set(receipt['fresh_compiles']) != set(gate.MODULES):
        raise ValueError('incomplete fresh module inventory')
    objects = {}
    for m in gate.MODULES:
        commands[m] = (receipt['fresh_compiles'][m], ['bash', 'build-jets.sh', '--coqc', '-q', 'C/' + m + '.v'], 'fresh-' + m)
        source, obj = coq / 'C' / (m + '.v'), coq / 'C' / (m + '.vo')
        if obj.is_symlink() or not obj.is_file() or source.read_bytes() != (gate.PRIOR_TREE / 'Coq/C' / (m + '.v')).read_bytes():
            raise ValueError('missing/shared object or unchecked source')
        if meta['source_sha256'].get('Coq/C/' + m + '.v') != support.sha(source.read_bytes()):
            raise ValueError('checked source hash drift')
        objects['Coq/C/' + m + '.vo'] = support.sha(obj.read_bytes())
    if receipt['new_objects_sha256'] != objects:
        raise ValueError('fresh object evidence changed')
    for evidence, command, stem in commands.values():
        if evidence['command'] != command or evidence['exit_code'] != 0 or evidence['log_sha256'] != support.sha((work / (stem + '.log')).read_bytes()):
            raise ValueError('wrong compiler command/exit/log')
    return {'candidate': str(work), 'coverage_added': 7, 'new_results': 308, 'new_definitions': 208,
            'inherited_contracts_byte_identical': len(old), 'inherited_dependencies_unchanged': len(old_deps),
            'untruncated_new_records': 516, 'compact_deep_supplements': supplements,
            'main_index_preserved': True, 'full_acceptance': False}


def finish(work):
    result, checks = review(work), {}
    tasks = [('coverage', [sys.executable, '-B', 'jet-coverage.py']),
             ('coverage-tests', [sys.executable, '-B', 'test-jet-coverage.py']),
             ('normal-contract-comparison', ['bash', 'audit-jet-contracts.sh'])]
    for directory, flags, positional in [
        ('elements-finality', [], []),
        ('elements-lock', ['--literal', 'C/jet_elements_lock_literal.v'], ['C/jet_elements_lock_literal.v']),
        ('elements-check-lock', ['--literal', 'C/jet_elements_check_lock_literal.v', '--transport', 'C/jet_application_partial_transport.v'],
         ['C/jet_elements_check_lock_literal.v', 'C/jet_application_partial_transport.v']),
        ('elements-pegin', ['--literal', 'C/jet_elements_pegin_literal.v'], ['C/jet_elements_pegin_literal.v']),
    ]:
        tasks += [(directory + '-source', [sys.executable, '-B', directory + '/check-source.py', '--repo', str(work), '--coq', '.'] + flags),
                  (directory + '-negative', [sys.executable, '-B', directory + '/test-source.py', str(work), '.'] + positional)]
    tasks += [('evidence-tests', [sys.executable, '-B', str(HERE / 'test-review.py'), str(work)])]
    for name, command in tasks:
        checks[name] = gate.command(work, command, name, 1800)
    review(work)
    record = {'review': result, 'checks': checks, 'assembly_sha256': support.sha((work / 'ASSEMBLY.json').read_bytes()),
              'preparation_sha256': support.sha((work / 'PREPARATION.json').read_bytes()),
              'tools_sha256': {n: support.sha((HERE / n).read_bytes()) for n in ['admission.py', 'review.py', 'test-review.py']},
              'candidate_input_sha256': support.inputs.fingerprint(work / 'Coq', work),
              'evidence_sha256': {str(p.relative_to(work)): support.sha(p.read_bytes()) for p in work.rglob('*')
                                  if p.is_file() and p.suffix in ['.log', '.vo']}, 'full_acceptance': False}
    gate.write(work / 'REVIEW.json', record)
    gate.write(HERE / 'REVIEW.json', record)
    print('Seven-jet full registration delta reviewed; full acceptance may start', flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('action', choices=['review', 'finish'])
    p.add_argument('work')
    args = p.parse_args()
    work = Path(args.work).resolve()
    finish(work) if args.action == 'finish' else print(json.dumps(review(work), indent=2))
