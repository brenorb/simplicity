"""Review exact count admission deltas before full normal acceptance."""
import argparse
import importlib.util
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('count_registry_review_driver', HERE / 'admission.py')
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)
support, REPO, MAIN, normal = gate.support, gate.REPO, gate.MAIN, gate.normal


def review(work):
    meta = json.loads((work / 'ASSEMBLY.json').read_text())
    receipt = json.loads((work / 'PREPARATION.json').read_text())
    if (meta['candidate'] != str(work) or meta['extensions'] != gate.additions() or
            meta['coverage_additions'] != gate.COVERAGE or meta['coverage_added'] != 2 or
            meta['full_acceptance'] is not False or receipt['candidate'] != str(work) or
            receipt['coverage_added'] != 2 or receipt['full_acceptance'] is not False):
        raise ValueError('wrong two-jet admission scope')
    if support.index_hash() != meta['staged_patch_sha256'] or support.input_map() != meta['main_inputs']:
        raise ValueError('main source/index drift')
    if support.inputs.fingerprint(MAIN, REPO) != meta['main_input_sha256']:
        raise ValueError('main fingerprint drift')
    coq = work / 'Coq'
    expected = dict(meta['main_inputs'])
    mutable = set(gate.METADATA + gate.SCRIPTS)
    for name, value in meta['main_metadata_sha256'].items():
        if support.sha((MAIN / name).read_bytes()) != value:
            raise ValueError('original metadata drift')
    for name, digest in expected.items():
        if name.startswith('Coq/') and name[4:] not in mutable:
            if support.sha((work / name).read_bytes()) != digest:
                raise ValueError('unreviewed source/infrastructure change: ' + name)
    actual_paths = {'Coq/' + str(p.relative_to(coq)) for p in coq.rglob('*') if p.is_file()
                    and '__pycache__' not in p.parts and (p.suffix in {'.v', '.c', '.sh', '.py', '.txt', '.tsv', '.expected'}
                    or p.name.startswith('_CoqProject') or p.name == 'clightgen-linux.ini.in')}
    if actual_paths != {n for n in expected if n.startswith('Coq/')} | {'Coq/' + n for n in gate.GUARDS}:
        raise ValueError('unexpected source inventory')
    for name, rows in meta['extensions'].items():
        if (coq / name).read_text() != (MAIN / name).read_text() + '\n'.join(rows) + '\n':
            raise ValueError('inventory not an exact append')
    if (coq / 'C/jet_coverage.tsv').read_text() != (MAIN / 'C/jet_coverage.tsv').read_text() + gate.COVERAGE:
        raise ValueError('coverage not exactly the two checked count contracts')
    for name, text in gate.script_changes().items():
        if (coq / name).read_text() != text:
            raise ValueError('unexpected coverage/gate code change')
    for name in gate.GUARDS:
        if (coq / name).read_bytes() != (HERE.parent / 'elements-count' / Path(name).name).read_bytes():
            raise ValueError('source/negative gate substitution')
    r0, d0 = normal.rows(MAIN / 'C/jet_public_theorems.txt'), normal.rows(MAIN / 'C/jet_contract_definitions.txt')
    r1, d1 = normal.rows(coq / 'C/jet_public_theorems.txt'), normal.rows(coq / 'C/jet_contract_definitions.txt')
    old = normal.contract_records((MAIN / 'C/jet_contracts.expected').read_text(), r0, d0)
    new = normal.contract_records((coq / 'C/jet_contracts.expected').read_text(), r1, d1)
    old_keys = {key for key, _ in old}
    if [(key, text) for key, text in new if key in old_keys] != old:
        raise ValueError('inherited contract bytes/order changed')
    added = [(key, text) for key, text in new if key not in old_keys]
    if len(added) != 24 or len(r1) - len(r0) != 18 or len(d1) - len(d0) != 6:
        raise ValueError('wrong new result/definition inventory')
    report = (work / 'new_contracts.log').read_text()
    marks = list(re.finditer(r'(?m)^COUNT_DEEP_(TYPE|DEF) (\S+)\n', report))
    if [(m[1], m[2]) for m in marks] != [(kind, mod + '.' + name) for (kind, mod, name, _), _ in added]:
        raise ValueError('missing/duplicate/reordered full records')
    supplements = []
    for i, ((_, mod, name, _), compact) in enumerate(added):
        deep = report[marks[i].end():marks[i+1].start() if i+1 < len(marks) else len(report)]
        if '...' in deep:
            raise ValueError('truncated deep record')
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
    if {name: new_deps.get(name) for name in old_deps} != old_deps:
        raise ValueError('inherited assumption sets changed')
    fresh = normal.assumptions((work / 'new_assumptions.log').read_text())
    if (receipt['new_dependencies'] != {n: sorted(ds) for n, ds in fresh.items()} or
            {n: ds for n, ds in new_deps.items() if n not in old_deps} != receipt['new_dependencies'] or
            set(fresh) != {m + '.' + n for m, n in r1[len(r0):]} or
            any(not ds <= support.SIX for ds in fresh.values())):
        raise ValueError('new dependency discrepancy')
    commands = {'build': (receipt['build'], ['bash', 'build-jets.sh', '-j2'], 'build'),
                'contracts': (receipt['contracts'], ['bash', 'build-jets.sh', '--coqc', '-q', str(work / 'new_contracts.v')], 'new_contracts'),
                'assumptions': (receipt['assumptions'], ['bash', 'build-jets.sh', '--coqc', '-q', str(work / 'new_assumptions.v')], 'new_assumptions')}
    if set(receipt['fresh_compiles']) != set(gate.MODULES):
        raise ValueError('missing fresh compile inventory')
    for name in gate.MODULES:
        commands[name] = (receipt['fresh_compiles'][name], ['bash', 'build-jets.sh', '--coqc', '-q', 'C/' + name + '.v'], 'fresh-' + name)
        if not (coq / 'C' / (name + '.vo')).is_file() or (coq / 'C' / (name + '.vo')).is_symlink():
            raise ValueError('missing or shared compiled object')
        key = 'Coq/C/' + name + '.vo'
        if receipt['new_objects_sha256'].get(key) != support.sha((work / key).read_bytes()):
            raise ValueError('fresh object changed')
        if support.sha((MAIN / 'C' / (name + '.v')).read_bytes()) != meta['source_sha256']['Coq/C/' + name + '.v']:
            raise ValueError('reviewed proof source changed')
    for evidence, command, stem in commands.values():
        if (evidence['command'] != command or evidence['exit_code'] != 0 or
                evidence['log_sha256'] != support.sha((work / (stem + '.log')).read_bytes())):
            raise ValueError('wrong command/flags/terminal evidence')
    return {'candidate': str(work), 'new_results': 18, 'new_definitions': 6, 'coverage_added': 2,
            'inherited_contracts_byte_identical': len(old), 'inherited_dependencies_unchanged': len(old_deps),
            'untruncated_new_records': 24, 'compact_deep_supplements': supplements,
            'main_index_preserved': True, 'full_acceptance': False}


def finish(work):
    result = review(work)
    checks = {}
    for name, command in [
        ('coverage', [sys.executable, '-B', 'jet-coverage.py']),
        ('coverage-tests', [sys.executable, '-B', 'test-jet-coverage.py']),
        ('source', [sys.executable, '-B', 'elements-count-review/check-source.py', '--repo', str(work), '--coq', '.']),
        ('source-tests', [sys.executable, '-B', 'elements-count-review/test-source.py', str(work), '.']),
        ('evidence-tests', [sys.executable, '-B', str(HERE / 'test-review.py'), str(work)]),
    ]:
        checks[name] = gate.command(work, command, name, 600)
    review(work)
    record = {'review': result, 'checks': checks, 'assembly_sha256': support.sha((work / 'ASSEMBLY.json').read_bytes()),
              'preparation_sha256': support.sha((work / 'PREPARATION.json').read_bytes()),
              'tools_sha256': {n: support.sha((HERE / n).read_bytes()) for n in ['admission.py', 'review.py', 'test-review.py']},
              'candidate_input_sha256': support.inputs.fingerprint(work / 'Coq', work),
              'evidence_sha256': {str(p.relative_to(work)): support.sha(p.read_bytes()) for p in work.rglob('*')
                                  if p.is_file() and p.suffix in ['.log', '.vo']},
              'full_acceptance': False}
    gate.write(work / 'REVIEW.json', record)
    gate.write(HERE / 'REVIEW.json', record)
    print('Exact inherited/new contract and assumption deltas reviewed; full acceptance may start', flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('action', choices=['review', 'finish'])
    parser.add_argument('work')
    args = parser.parse_args()
    work = Path(args.work).resolve()
    if args.action == 'finish':
        finish(work)
    else:
        print(json.dumps(review(work), indent=2))
