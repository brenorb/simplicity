"""Review the thirteen-getter delta over its fingerprint-bound virtual predecessor."""
import argparse
import importlib.util
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('digest_getters_review_gate', HERE / 'admission.py')
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)
support, normal, BASE = gate.support, gate.normal, gate.BASE


def baseline_inputs():
    result = dict(gate.PRED_META['baseline_inputs'])
    paths = gate.predecessor.METADATA + gate.predecessor.SCRIPTS + gate.predecessor.GUARDS + gate.predecessor.NEW_SOURCES
    result.update({'Coq/' + n: support.sha((BASE / n).read_bytes()) for n in paths})
    return result


def review(work):
    meta = json.loads((work / 'ASSEMBLY.json').read_text())
    r = json.loads((work / 'PREPARATION.json').read_text())
    gate.predecessor_source()
    for module, prior in zip(gate.MODULES, [gate.PRIORS[0], gate.PRIORS[0], gate.PRIORS[1], gate.PRIORS[2], gate.PRIORS[3], gate.PRIORS[3]]):
        hashes = prior['source_sha256']
        expected = hashes['C.' + module] if isinstance(hashes, dict) else hashes
        if support.sha(gate.ORIGINS[module].read_bytes()) != expected:
            raise ValueError('source differs from checked proof receipt: ' + module)
    baseline = baseline_inputs()
    if (meta['candidate'] != str(work) or r['candidate'] != str(work) or meta['extensions'] != gate.additions() or
            meta['coverage_additions'] != gate.COVERAGE or meta['new_sources'] != gate.NEW_SOURCES or
            any(x['coverage_added'] != 13 or x['full_acceptance'] is not False for x in [meta, r]) or
            meta['predecessor_candidate'] != str(gate.BASE_TREE) or meta['predecessor_input_sha256'] != gate.PRED_REVIEW['candidate_input_sha256'] or
            meta['predecessor_review_sha256'] != support.sha((gate.PRED / 'REVIEW.json').read_bytes()) or meta['baseline_inputs'] != baseline or
            meta['main_inputs'] not in [gate.PRED_META['baseline_inputs'], baseline] or
            meta['prior_preparations_sha256'] != {str(p.relative_to(HERE.parent)): support.sha(p.read_bytes()) for p in gate.PRIOR_PATHS}):
        raise ValueError('wrong thirteen-getter/predecessor/proof scope')
    if support.input_map() not in [meta['main_inputs'], baseline] or support.index_hash() != meta['staged_patch_sha256']:
        raise ValueError('main source/index is not a preserved known checkpoint')
    expected_main_fp = (gate.PRED_META['predecessor_input_sha256'] if meta['main_inputs'] == gate.PRED_META['baseline_inputs']
                        else gate.PRED_REVIEW['candidate_input_sha256'])
    if meta['main_input_sha256'] != expected_main_fp or meta['staged_patch_sha256'] != gate.PRED_META['staged_patch_sha256']:
        raise ValueError('historical main fingerprint/index identity differs')
    for n, h in meta['baseline_metadata_sha256'].items():
        if support.sha((BASE / n).read_bytes()) != h:
            raise ValueError('predecessor metadata drift')
    if set(meta['baseline_metadata_sha256']) != set(gate.METADATA + gate.SCRIPTS):
        raise ValueError('incomplete baseline metadata binding')
    coq, mutable = work / 'Coq', set(gate.METADATA + gate.SCRIPTS)
    for n, h in baseline.items():
        if n.startswith('Coq/') and n[4:] not in mutable and support.sha((work / n).read_bytes()) != h:
            raise ValueError('unreviewed inherited source change: ' + n)
    paths = support.load('digest_review_source_paths', HERE.parent / 'elements-pegin-normal/review.py').source_paths
    if {'Coq/' + n for n in paths(coq)} != {n for n in baseline if n.startswith('Coq/')} | {'Coq/' + n for n in gate.NEW_SOURCES + gate.GUARDS}:
        raise ValueError('unexpected candidate source inventory')
    for n in gate.NEW_SOURCES:
        if (coq / n).read_bytes() != gate.ORIGINS[Path(n).stem].read_bytes():
            raise ValueError('new source differs from checked endpoint proof')
    for n, rows in meta['extensions'].items():
        if (coq / n).read_text() != (BASE / n).read_text() + '\n'.join(rows) + '\n':
            raise ValueError('public inventory is not exact append')
    if (coq / 'C/jet_coverage.tsv').read_text() != (BASE / 'C/jet_coverage.tsv').read_text() + gate.COVERAGE:
        raise ValueError('coverage is not exactly eight reviewed getters')
    for n, text in gate.script_changes().items():
        if (coq / n).read_text() != text:
            raise ValueError('unreviewed coverage/source/printer gate change')
    for n in gate.GUARDS:
        if (coq / n).read_bytes() != (HERE.parent / n).read_bytes():
            raise ValueError('selected guard/negative substitution')
    r0, d0 = normal.rows(BASE / 'C/jet_public_theorems.txt'), normal.rows(BASE / 'C/jet_contract_definitions.txt')
    r1, d1 = normal.rows(coq / 'C/jet_public_theorems.txt'), normal.rows(coq / 'C/jet_contract_definitions.txt')
    old = normal.contract_records((BASE / 'C/jet_contracts.expected').read_text(), r0, d0)
    new = normal.contract_records((coq / 'C/jet_contracts.expected').read_text(), r1, d1)
    old_keys = {k for k, _ in old}
    if [(k, t) for k, t in new if k in old_keys] != old:
        raise ValueError('inherited type/definition bytes or order changed')
    added = [(k, t) for k, t in new if k not in old_keys]
    if (len(added), len(r1)-len(r0), len(d1)-len(d0)) != (90, 48, 42):
        raise ValueError('wrong new declaration/contract inventory')
    report = (work / 'new_contracts.log').read_text()
    marks = list(re.finditer(r'(?m)^DIGEST_DEEP_(TYPE|DEF) (\S+)\n', report))
    if [(m[1], m[2]) for m in marks] != [(k, m + '.' + n) for (k, m, n, _), _ in added]:
        raise ValueError('missing/duplicate/reordered full contracts')
    supplements = []
    for i, ((_, mod, name, _), compact) in enumerate(added):
        deep = report[marks[i].end():marks[i+1].start() if i+1 < len(marks) else len(report)]
        if '...' in deep or re.search(r'\?[A-Za-z]', deep):
            raise ValueError('truncated/unquantified deep record')
        short, long = re.sub(r'\s+', '', compact), re.sub(r'\s+', '', deep)
        if short == long:
            continue
        position, fragments = 0, short.split('...')
        for j, fragment in enumerate(fragments):
            offset = len(long)-len(fragment) if j == len(fragments)-1 and long.endswith(fragment) else long.find(fragment, position)
            if offset < position or j == 0 and offset != 0:
                raise ValueError('compact/deep disagreement')
            position = offset + len(fragment)
        if '...' not in short or position != len(long):
            raise ValueError('unexplained compact/deep difference')
        supplements.append(mod + '.' + name)
    old_deps = gate.snapshot_deps((BASE / 'C/jet_assumptions.expected').read_text())
    new_deps = gate.snapshot_deps((coq / 'C/jet_assumptions.expected').read_text())
    if {n: new_deps.get(n) for n in old_deps} != old_deps:
        raise ValueError('inherited assumption sets changed')
    fresh = normal.assumptions((work / 'new_assumptions.log').read_text())
    expected = {n: ds for p in gate.PRIORS[:4] for n, ds in p['dependencies'].items()}
    fresh_sorted = {n: sorted(ds) for n, ds in fresh.items()}
    if (set(fresh) != {m + '.' + n for m, n in r1[len(r0):]} or r['new_dependencies'] != fresh_sorted or
            {n: ds for n, ds in new_deps.items() if n not in old_deps} != fresh_sorted or
            any(not ds <= support.SIX or sorted(ds) != expected[n] for n, ds in fresh.items())):
        raise ValueError('new dependency sets differ from checked proofs')
    pure = ['C.jet_elements_optional_digest_literal.elements_input_optional_digest_literal_matches',
            'C.jet_elements_optional_digest_literal.elements_pegin_literal_uses_optional_digest',
            'C.jet_elements_issuance_digest_literal.elements_issuance_optional_digest_literal_matches',
            'C.jet_elements_indexed_literal.elements_indexed_literal_matches',
            'C.jet_elements_indexed_literal.haskell_encode_outpoint_matches',
            'C.jet_elements_output_proof_literal.haskell_confidential_proof_view_matches',
            'C.jet_elements_output_proof_literal.elements_output_proof_digest_literal_matches']
    if any(fresh[n] for n in pure):
        raise ValueError('shared conversion/view lemmas are not closed')
    for function, module, theorem, _, _ in gate.ENDPOINTS:
        new_module = 'C.jet_elements_' + ('optional_digest_literal' if 'annex' in function else
                      'issuance_digest_literal' if function.removeprefix('current_') in
                      ['reissuance_blinding', 'new_issuance_contract', 'reissuance_entropy'] else 'output_proof_literal' if function in ['output_surjection_proof', 'output_range_proof'] else 'indexed_literal')
        final = 'elements_' + function + '_literal_local_spec'
        if sorted(fresh[new_module + '.' + final]) != expected['C.' + module + '.' + theorem]:
            raise ValueError('endpoint changed original assumption set')
    commands = {'build': (r['build'], ['bash', 'build-jets.sh', '-j2'], 'build'),
                **{n: (r[n], ['bash', 'build-jets.sh', '--coqc', '-q', str(work / ('new_' + n + '.v'))], 'new_' + n)
                   for n in ['contracts', 'assumptions']}}
    if set(r['fresh_compiles']) != set(gate.MODULES):
        raise ValueError('incomplete fresh module inventory')
    sources, objects = {}, {}
    for m in gate.MODULES:
        commands[m] = (r['fresh_compiles'][m], ['bash', 'build-jets.sh', '--coqc', '-q', 'C/' + m + '.v'], 'fresh-' + m)
        source, obj = coq / 'C' / (m + '.v'), coq / 'C' / (m + '.vo')
        if obj.is_symlink() or not obj.is_file():
            raise ValueError('missing/shared object')
        sources['Coq/C/' + m + '.v'], objects['Coq/C/' + m + '.vo'] = support.sha(source.read_bytes()), support.sha(obj.read_bytes())
    if meta['source_sha256'] != sources or r['new_objects_sha256'] != objects:
        raise ValueError('fresh source/object hashes drifted')
    for evidence, command, stem in commands.values():
        if evidence['command'] != command or evidence['exit_code'] != 0 or evidence['log_sha256'] != support.sha((work / (stem + '.log')).read_bytes()):
            raise ValueError('wrong compiler flags/command/exit/log')
    return {'candidate': str(work), 'coverage_added': 13, 'new_results': 48, 'new_definitions': 42,
            'inherited_contracts_byte_identical': len(old), 'inherited_dependencies_unchanged': len(old_deps),
            'untruncated_new_records': 90, 'compact_deep_supplements': supplements, 'closed_shared_lemmas': 7,
            'main_index_preserved': True, 'predecessor_terminal_acceptance_required': True, 'full_acceptance': False}


def finish(work):
    result, checks = review(work), {}
    tasks = [('coverage', [sys.executable, '-B', 'jet-coverage.py']),
             ('coverage-tests', [sys.executable, '-B', 'test-jet-coverage.py']),
             ('normal-contract-comparison', ['bash', 'audit-jet-contracts.sh'])]
    for directory, module in gate.GUARD_MODULES:
        literal = 'C/' + module + '.v'
        tasks += [(directory + '-source', [sys.executable, '-B', directory + '/check-source.py', '--repo', str(work), '--coq', '.', '--literal', literal]),
                  (directory + '-negative', [sys.executable, '-B', directory + '/test-source.py', str(work), '.', literal])]
    tasks += [('evidence-tests', [sys.executable, '-B', str(HERE / 'test-review.py'), str(work)])]
    for n, c in tasks:
        checks[n] = gate.command(work, c, n, 1800)
    review(work)
    r = {'review': result, 'checks': checks, 'assembly_sha256': support.sha((work / 'ASSEMBLY.json').read_bytes()),
         'preparation_sha256': support.sha((work / 'PREPARATION.json').read_bytes()),
         'tools_sha256': {n: support.sha((HERE / n).read_bytes()) for n in ['admission.py', 'review.py', 'test-review.py']},
         'candidate_input_sha256': support.inputs.fingerprint(work / 'Coq', work),
         'evidence_sha256': {str(p.relative_to(work)): support.sha(p.read_bytes()) for p in work.rglob('*') if p.is_file() and p.suffix in ['.log', '.vo']},
         'full_acceptance': False}
    gate.write(work / 'REVIEW.json', r)
    gate.write(HERE / 'REVIEW.json', r)
    print('Thirteen-getter delta reviewed; predecessor acceptance/installation and own full acceptance remain required', flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('action', choices=['review', 'finish'])
    p.add_argument('work')
    args = p.parse_args()
    work = Path(args.work).resolve()
    finish(work) if args.action == 'finish' else print(json.dumps(review(work), indent=2))
