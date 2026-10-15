"""Independently inspect terminal tap-getter evidence; never register coverage."""
import importlib.util
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('tap_checker', HERE / 'check.py')
c = importlib.util.module_from_spec(sp)
sp.loader.exec_module(c)
s = c.s


def chunks(text, results, definitions):
    marks = list(re.finditer(r'(?m)^TAP_(TYPE|DEF) (\S+)\n', text))
    if ('...' in text or re.search(r'\?[A-Za-z]', text) or
        [(m[1], m[2]) for m in marks] != [('TYPE', n) for n in results] + [('DEF', n) for n in definitions]):
        raise ValueError('incomplete/changed deep contract inventory')
    return {(m[1], m[2]): text[m.end():marks[i+1].start() if i+1 < len(marks) else len(text)] for i, m in enumerate(marks)}


def review():
    receipt = HERE / 'PREPARATION.json'
    r = json.loads(receipt.read_text())
    prior_path = HERE.parent / 'elements-output-proof/PREPARATION.json'
    prior = json.loads(prior_path.read_text())
    work, coq = Path(r['candidate']), Path(r['candidate']) / 'Coq'
    inherited = c.check_tree(work, prior)
    if (r['base_candidate'] != prior['candidate'] or r['base_receipt_sha256'] != s.sha(prior_path.read_bytes()) or
        r['base_input_sha256'] != prior['candidate_input_sha256'] or
        r['roots'] != c.ROOTS or r['new_sources'] != [c.NEW] or r['reviewed_source_generalization'] != [c.MODIFIED] or
        r['endpoints'] != c.ENDPOINTS or r['closed_shared_lemmas'] != c.PURE or
        r['normal_registration'] is not False or r['coverage_added'] != 0 or r['full_acceptance'] is not False):
        raise ValueError('wrong proof/base/coverage scope')
    if (s.inputs.fingerprint(coq, work) != r['candidate_input_sha256'] or
        s.index_hash() != r['staged_patch_sha256'] or s.input_map() != r['main_inputs']):
        raise ValueError('candidate/main/index drift')
    order = c.closure(coq)
    if r['fresh_modules'] != order or len(order) != 11:
        raise ValueError('changed fresh dependency closure')
    results, definitions = [], []
    for m in order:
        path = coq / (m.replace('.', '/') + '.v')
        a, b = c.declarations(path.read_text(), m)
        results += a
        definitions += b
        if path.with_suffix('.vo').is_symlink():
            raise ValueError('object is a mutable external link')
    if (r['results'] != results or r['definitions'] != definitions or
        sum(n.startswith(c.LM + '.') for n in results) != 9 or
        sum(n.startswith(c.LM + '.') for n in definitions) != 4 or
        r['source_sha256'] != {m: s.sha((coq / (m.replace('.', '/') + '.v')).read_bytes()) for m in order} or
        r['object_sha256'] != {m: s.sha((coq / (m.replace('.', '/') + '.vo')).read_bytes()) for m in order}):
        raise ValueError('incomplete or changed result/definition/source/object inventory')
    baseline = work / 'baseline/NullableBaseline.v'
    if baseline.read_bytes() != (Path(prior['candidate']) / 'Coq' / c.MODIFIED).read_bytes():
        raise ValueError('baseline is not the exact old proof')
    br, bd = c.declarations(baseline.read_text(), 'TappathBaseline.NullableBaseline')
    olddeps = s.reports.assumptions((work / 'baseline-assumptions.log').read_text())
    deps = s.reports.assumptions((work / 'tap-assumptions.log').read_text())
    if (r['baseline_results'] != br or r['baseline_definitions'] != bd or set(olddeps) != set(br) or
        {n: sorted(ds) for n, ds in olddeps.items()} != r['baseline_dependencies'] or set(deps) != set(results) or
        {n: sorted(ds) for n, ds in deps.items()} != r['dependencies'] or
        any(not ds <= s.SIX for ds in deps.values()) or any(deps[n] for n in c.PURE)):
        raise ValueError('assumption inventory or closed shared lemma changed')
    current = chunks((work / 'tap-contracts.log').read_text(), results, definitions)
    original = chunks((work / 'baseline-contracts.log').read_text(), br, bd)
    for n in br:
        new = n.replace('TappathBaseline.NullableBaseline.', c.NULLABLE + '.')
        oldtype = re.sub(r'\s+', '', original['TYPE', n].replace('NullableBaseline.', 'jet_elements_tappath_nullable.'))
        newtype = re.sub(r'\s+', '', current['TYPE', new])
        if oldtype != newtype or olddeps[n] != deps[new]:
            raise ValueError('original nullable whole type or assumptions changed')
    inherited_deps = {}
    for folder, file in [('elements-annex-hash', 'PREPARATION.json'),
                         ('elements-outpoint-output', 'CHECKED.json'), ('elements-output-proof', 'PREPARATION.json')]:
        inherited_deps.update(json.loads((HERE.parent / folder / file).read_text())['dependencies'])
    for n, ds in deps.items():
        if n in inherited_deps and sorted(ds) != inherited_deps[n]:
            raise ValueError('inherited assumption drift')
    for n, old in zip(c.ENDPOINTS, ['C.jet_elements_hash_field_jets.elements_internal_key_local_spec',
                                  c.NULLABLE + '.elements_tappath_nullable_local_spec',
                                  c.NULLABLE + '.elements_tappath_u8_local_spec']):
        if deps[n] != deps[old]:
            raise ValueError('endpoint assumption set changed')
    extra = ['-Q', str(baseline.parent), 'TappathBaseline']
    commands = {m: ['bash', 'build-jets.sh', '--coqc', '-q', m.replace('.', '/') + '.v'] for m in order}
    commands['baseline'] = ['bash', 'build-jets.sh', '--coqc', '-q', *extra, str(baseline)]
    for prefix in ['baseline', 'tap']:
        for report in ['assumptions', 'contracts']:
            stem = prefix + '-' + report
            commands[stem] = ['bash', 'build-jets.sh', '--coqc', '-q', *(extra if prefix == 'baseline' else []),
                              str(work / (stem.replace('-', '_') + '.v'))]
    commands.update(source=[sys.executable, '-B', str(HERE / 'check-source.py'), str(work)],
                    **{'source-negative': [sys.executable, '-B', str(HERE / 'test-source.py'), str(work)],
                       'ast': ['bash', 'C/check-elements-jets-generation.sh'],
                       'kernel': ['bash', 'build-jets.sh', '--coqchk', '-silent', '-o', *extra,
                                  'TappathBaseline.NullableBaseline', *c.ROOTS]})
    if set(r['commands']) != set(commands):
        raise ValueError('missing or unexpected checker stage')
    for stem, command in commands.items():
        row = r['commands'][stem]
        if row['command'] != command or row['exit_code'] != 0 or row['log_sha256'] != s.sha((work / (stem + '.log')).read_bytes()):
            raise ValueError('changed command/flags/exit/log: ' + stem)
    if r['tools_sha256'] != {n: s.sha((HERE / n).read_bytes()) for n in ['check.py', 'check-source.py', 'test-source.py']}:
        raise ValueError('checked tool changed')
    for stem in ['baseline-assumptions', 'baseline-contracts', 'tap-assumptions', 'tap-contracts', 'source', 'source-negative', 'ast', 'kernel']:
        if (HERE / (stem + '.log')).read_bytes() != (work / (stem + '.log')).read_bytes():
            raise ValueError('archived evidence differs: ' + stem)
    s.kernel.kernel((work / 'kernel.log').read_text(), sorted((coq / 'C/jet_coqchk_axioms.expected').read_text().split()))
    gate = s.load('tap_review_source', HERE / 'check-source.py')
    gate.check(work)
    return dict(candidate=str(work), candidate_input_sha256=r['candidate_input_sha256'], jets_checked=2,
                whole_c_endpoints=3, fresh_modules=len(order), results=len(results), definitions=len(definitions),
                new_literal_results=9, closed_shared_lemmas=4, old_nullable_types_and_assumptions_unchanged=True,
                inherited_sources_byte_identical=len(inherited)-1, reviewed_source_generalizations=1,
                normal_registration=False, coverage_added=0, full_acceptance=False)


if __name__ == '__main__':
    result = review()
    s.changed({HERE / 'REVIEW.json': json.dumps(result, indent=2) + '\n'})
    print(json.dumps(result, indent=2))
