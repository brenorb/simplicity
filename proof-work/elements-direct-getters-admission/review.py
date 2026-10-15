"""Review the complete direct-getter admission delta before normal acceptance."""
import argparse
import importlib.util
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('direct_registry_gate', HERE / 'admission.py')
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)
support, REPO, MAIN, normal = gate.support, gate.REPO, gate.MAIN, gate.normal


def review(work):
    meta = json.loads((work / 'ASSEMBLY.json').read_text())
    receipt = json.loads((work / 'PREPARATION.json').read_text())
    if (meta['candidate'] != str(work) or meta['extensions'] != gate.additions() or
            meta['coverage_additions'] != gate.COVERAGE or meta['new_sources'] != gate.NEW_SOURCES or
            meta['coverage_added'] != 3 or meta['full_acceptance'] is not False or
            receipt['candidate'] != str(work) or receipt['coverage_added'] != 3 or receipt['full_acceptance'] is not False):
        raise ValueError('wrong direct-getter admission scope')
    if (support.index_hash() != meta['staged_patch_sha256'] or support.input_map() != meta['main_inputs'] or
            support.inputs.fingerprint(MAIN, REPO) != meta['main_input_sha256']):
        raise ValueError('main source/index drift')
    if (meta['prior_preparation_sha256'] != support.sha((HERE.parent / 'elements-direct-getters-normal/PREPARATION.json').read_bytes())):
        raise ValueError('reviewed final-name proof dependency changed')
    coq = work / 'Coq'
    expected = dict(meta['main_inputs'])
    mutable = set(gate.METADATA + gate.SCRIPTS)
    for name, digest in meta['main_metadata_sha256'].items():
        if support.sha((MAIN / name).read_bytes()) != digest:
            raise ValueError('original normal metadata drift')
    for name, digest in expected.items():
        if name.startswith('Coq/') and name[4:] not in mutable:
            if support.sha((work / name).read_bytes()) != digest:
                raise ValueError('unreviewed inherited source change: ' + name)
    actual_paths = {'Coq/' + str(p.relative_to(coq)) for p in coq.rglob('*') if p.is_file()
                    and '__pycache__' not in p.parts and (p.suffix in {'.v', '.c', '.sh', '.py', '.txt', '.tsv', '.expected'}
                    or p.name.startswith('_CoqProject') or p.name == 'clightgen-linux.ini.in')}
    wanted_paths = {n for n in expected if n.startswith('Coq/')} | {'Coq/' + n for n in gate.NEW_SOURCES + gate.GUARDS}
    if actual_paths != wanted_paths:
        raise ValueError('unexpected source inventory')
    for name in gate.NEW_SOURCES:
        if (coq / name).read_bytes() != (gate.PRIOR_TREE / 'Coq' / name).read_bytes():
            raise ValueError('new proof differs from final-name checked source')
    for name, rows in meta['extensions'].items():
        if (coq / name).read_text() != (MAIN / name).read_text() + '\n'.join(rows) + '\n':
            raise ValueError('registration is not an exact append')
    if (coq / 'C/jet_coverage.tsv').read_text() != (MAIN / 'C/jet_coverage.tsv').read_text() + gate.COVERAGE:
        raise ValueError('coverage is not exactly the three canonical direct-getter contracts')
    for name, text in gate.script_changes().items():
        if (coq / name).read_text() != text:
            raise ValueError('unexpected coverage/source/printer gate edit')
    for name in gate.GUARDS:
        if (coq / name).read_bytes() != (HERE.parent / name).read_bytes():
            raise ValueError('selected source/negative test substitution')
    r0, d0 = normal.rows(MAIN / 'C/jet_public_theorems.txt'), normal.rows(MAIN / 'C/jet_contract_definitions.txt')
    r1, d1 = normal.rows(coq / 'C/jet_public_theorems.txt'), normal.rows(coq / 'C/jet_contract_definitions.txt')
    old = normal.contract_records((MAIN / 'C/jet_contracts.expected').read_text(), r0, d0)
    new = normal.contract_records((coq / 'C/jet_contracts.expected').read_text(), r1, d1)
    old_keys = {key for key, _ in old}
    if [(key, text) for key, text in new if key in old_keys] != old:
        raise ValueError('inherited contract bytes/order changed')
    added = [(key, text) for key, text in new if key not in old_keys]
    if len(added) != 109 or len(r1) - len(r0) != 75 or len(d1) - len(d0) != 34:
        raise ValueError('wrong new result/definition inventory')
    report = (work / 'new_contracts.log').read_text()
    marks = list(re.finditer(r'(?m)^DIRECT_DEEP_(TYPE|DEF) (\S+)\n', report))
    if [(m[1], m[2]) for m in marks] != [(kind, mod + '.' + name) for (kind, mod, name, _), _ in added]:
        raise ValueError('missing/duplicate/reordered full records')
    supplements = []
    for i, ((_, mod, name, _), compact) in enumerate(added):
        deep = report[marks[i].end():marks[i+1].start() if i+1 < len(marks) else len(report)]
        if '...' in deep or re.search(r'\?[A-Za-z]', deep):
            raise ValueError('truncated or incompletely quantified deep record')
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
        raise ValueError('inherited dependency sets changed')
    fresh = normal.assumptions((work / 'new_assumptions.log').read_text())
    if (receipt['new_dependencies'] != {n: sorted(ds) for n, ds in fresh.items()} or
            {n: ds for n, ds in new_deps.items() if n not in old_deps} != receipt['new_dependencies'] or
            set(fresh) != {m + '.' + n for m, n in r1[len(r0):]} or any(not ds <= support.SIX for ds in fresh.values())):
        raise ValueError('new dependency disagreement')
    pure = {m + '.' + n for m, n in r1[len(r0):] if m == 'C.jet_haskell_hash_word'}
    if len(pure) != 27 or any(fresh[n] for n in pure):
        raise ValueError('shared digest-conversion lemmas are not closed')
    for original, final in [
        ('C.jet_elements_tapleaf_version_local.elements_tapleaf_version_local_spec',
         'C.jet_elements_tapleaf_literal.elements_tapleaf_version_literal_local_spec'),
        ('C.jet_elements_script_cmr_local.elements_script_cmr_local_spec',
         'C.jet_elements_hash_literal.elements_script_cmr_literal_local_spec'),
        ('C.jet_elements_genesis_hash_local.elements_genesis_block_hash_local_spec',
         'C.jet_elements_hash_literal.elements_genesis_hash_literal_local_spec'),
    ]:
        if fresh[original] != fresh[final]:
            raise ValueError('literal contract changed the original assumption set')
    commands = {'build': (receipt['build'], ['bash', 'build-jets.sh', '-j2'], 'build'),
                'contracts': (receipt['contracts'], ['bash', 'build-jets.sh', '--coqc', '-q', str(work / 'new_contracts.v')], 'new_contracts'),
                'assumptions': (receipt['assumptions'], ['bash', 'build-jets.sh', '--coqc', '-q', str(work / 'new_assumptions.v')], 'new_assumptions')}
    if set(receipt['fresh_compiles']) != set(gate.MODULES):
        raise ValueError('incomplete fresh module inventory')
    for name in gate.MODULES:
        commands[name] = (receipt['fresh_compiles'][name], ['bash', 'build-jets.sh', '--coqc', '-q', 'C/' + name + '.v'], 'fresh-' + name)
        source, obj = coq / 'C' / (name + '.v'), coq / 'C' / (name + '.vo')
        if obj.is_symlink() or not obj.is_file():
            raise ValueError('missing/shared compiled object')
        if (receipt['new_objects_sha256'].get('Coq/C/' + name + '.vo') != support.sha(obj.read_bytes()) or
                meta['source_sha256'].get('Coq/C/' + name + '.v') != support.sha(source.read_bytes()) or
                source.read_bytes() != (gate.PRIOR_TREE / 'Coq/C' / (name + '.v')).read_bytes()):
            raise ValueError('fresh source/object evidence changed')
    for evidence, command, stem in commands.values():
        if (evidence['command'] != command or evidence['exit_code'] != 0 or
                evidence['log_sha256'] != support.sha((work / (stem + '.log')).read_bytes())):
            raise ValueError('wrong compiler command/flags/terminal evidence')
    return {'candidate': str(work), 'new_results': 75, 'new_definitions': 34, 'coverage_added': 3,
            'inherited_contracts_byte_identical': len(old), 'inherited_dependencies_unchanged': len(old_deps),
            'untruncated_new_records': 109, 'closed_digest_lemmas': len(pure), 'compact_deep_supplements': supplements,
            'main_index_preserved': True, 'full_acceptance': False}


def finish(work):
    result = review(work)
    checks = {}
    tasks = [('coverage', [sys.executable, '-B', 'jet-coverage.py']),
             ('coverage-tests', [sys.executable, '-B', 'test-jet-coverage.py']),
             ('normal-contract-comparison', ['bash', 'audit-jet-contracts.sh'])]
    for directory, flags, positional in [
        ('elements-tapleaf-literal', ['--literal', 'C/jet_elements_tapleaf_literal.v'],
         ['C/jet_elements_tapleaf_literal.v']),
        ('elements-hash-literal', ['--helper', 'C/jet_haskell_hash_word.v', '--endpoint', 'C/jet_elements_hash_literal.v'],
         ['C/jet_haskell_hash_word.v', 'C/jet_elements_hash_literal.v']),
    ]:
        tasks += [(directory + '-source', [sys.executable, '-B', directory + '/check-source.py', '--repo', str(work), '--coq', '.'] + flags),
                  (directory + '-negative', [sys.executable, '-B', directory + '/test-source.py', str(work), '.'] + positional)]
    tasks += [('evidence-tests', [sys.executable, '-B', str(HERE / 'test-review.py'), str(work)])]
    for name, command in tasks:
        checks[name] = gate.command(work, command, name, 1800)
    review(work)
    record = {'review': result, 'checks': checks, 'assembly_sha256': support.sha((work / 'ASSEMBLY.json').read_bytes()),
              'preparation_sha256': support.sha((work / 'PREPARATION.json').read_bytes()),
              'tools_sha256': {name: support.sha((HERE / name).read_bytes()) for name in ['admission.py', 'review.py', 'test-review.py']},
              'candidate_input_sha256': support.inputs.fingerprint(work / 'Coq', work),
              'evidence_sha256': {str(p.relative_to(work)): support.sha(p.read_bytes()) for p in work.rglob('*')
                                  if p.is_file() and p.suffix in ['.log', '.vo']}, 'full_acceptance': False}
    gate.write(work / 'REVIEW.json', record)
    gate.write(HERE / 'REVIEW.json', record)
    print('Direct-getter registration and inherited/new snapshots reviewed; full acceptance may start', flush=True)


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
