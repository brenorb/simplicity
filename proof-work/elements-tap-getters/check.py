"""Fresh isolated tap-getter proofs; no normal registration or coverage update."""
import importlib.util
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
sp = importlib.util.spec_from_file_location('tap_support', HERE.parent / 'elements-count/support.py')
s = importlib.util.module_from_spec(sp)
sp.loader.exec_module(s)
LM = 'C.jet_elements_tap_getters_literal'
NULLABLE = 'C.jet_elements_tappath_nullable'
NEW = 'C/jet_elements_tap_getters_literal.v'
MODIFIED = 'C/jet_elements_tappath_nullable.v'
ROOTS = ['C.jet_elements_hash_field_jets', 'C.jet_elements_tappath_local', NULLABLE, LM]
PURE = [LM + '.' + x for x in ['haskell_encode_pubkey_matches',
        'nth_error_is_list_to_maybe_drop', 'word_indexed_digest_literal_matches',
        'tappath_literal_index_range']]
ENDPOINTS = [LM + '.elements_internal_key_literal_local_spec',
             LM + '.elements_tappath_nullable_literal_local_spec',
             LM + '.elements_tappath_u8_literal_local_spec']


def inventory(coq):
    return s.load('tap_inventory', HERE.parent / 'elements-pegin-normal/review.py').source_paths(coq)


def declarations(source, module):
    code = s.safe_source(source, module)
    return ([module + '.' + n for n in re.findall(r"^(?:Lemma|Theorem|Corollary)\s+([A-Za-z_][\w']*)", code, re.M)],
            [module + '.' + n for n in re.findall(r"^(?:Definition|Fixpoint|Record)\s+([A-Za-z_][\w']*)", code, re.M)])


def closure(coq):
    seen, active, order = set(), set(), []
    manifest = set((coq / '_CoqProject.jets').read_text().splitlines())
    def visit(m):
        if m in seen:
            return
        if m in active:
            raise ValueError('cyclic dependency: ' + m)
        active.add(m)
        code = s.safe_source((coq / (m.replace('.', '/') + '.v')).read_text(), m)
        for block in re.findall(r'\bRequire(?:\s+(?:Import|Export))?\s+(.*?)\.(?=\s|$)', code, re.S):
            for d in block.split():
                if d.startswith('C.'):
                    visit(d)
        active.remove(m)
        seen.add(m)
        if m.replace('.', '/') + '.v' not in manifest:
            order.append(m)
    visit(LM)
    return order


def check_tree(work, prior):
    base, coq = Path(prior['candidate']), work / 'Coq'
    if work == base or work == REPO or REPO in work.parents:
        raise ValueError('use a distinct external proof tree')
    if s.inputs.fingerprint(base / 'Coq', base) != prior['candidate_input_sha256']:
        raise ValueError('completed base changed')
    inherited = inventory(base / 'Coq')
    if inventory(coq) != inherited | {NEW}:
        raise ValueError('unexpected source/metadata inventory')
    for name in inherited - {MODIFIED}:
        if (coq / name).read_bytes() != (base / 'Coq' / name).read_bytes():
            raise ValueError('unreviewed inherited change: ' + name)
    for name in [NEW, MODIFIED]:
        if (coq / name).read_bytes() != (HERE / 'source' / (Path(name).name + '.source')).read_bytes():
            raise ValueError('archive/private proof differ: ' + name)
    return inherited


def reports(work, modules, prefix, commands, extra=()):
    results, definitions = [], []
    for m, path in modules:
        a, b = declarations(path.read_text(), m)
        results += a
        definitions += b
    header = ['Require ' + ' '.join(m for m, _ in modules) + '.']
    axioms = header[:]
    contracts = header + ['Set Printing All.', 'Set Printing Width 120.', 'Set Printing Depth 1000000.']
    for n in results:
        axioms += ['Goal True. idtac "JET_ASSUMPTIONS ' + n + '". exact I. Qed.', 'Print Assumptions ' + n + '.']
    for kind, names in [('TYPE', results), ('DEF', definitions)]:
        for n in names:
            contracts += ['Goal True. idtac "TAP_' + kind + ' ' + n + '". exact I. Qed.',
                          ('Check @' if kind == 'TYPE' else 'Print ') + n + '.']
    for stem, source in [(prefix + '-assumptions', axioms), (prefix + '-contracts', contracts)]:
        path = work / (stem.replace('-', '_') + '.v')
        s.changed({path: '\n'.join(source) + '\n'})
        commands[stem] = s.run(work, ['bash', 'build-jets.sh', '--coqc', '-q', *extra, str(path)], stem, 180)
    deps = s.reports.assumptions((work / (prefix + '-assumptions.log')).read_text())
    if set(deps) != set(results) or any(not v <= s.SIX for v in deps.values()):
        raise ValueError('incomplete or unreviewed assumptions')
    text = (work / (prefix + '-contracts.log')).read_text()
    if ('...' in text or re.search(r'\?[A-Za-z]', text) or
        re.findall(r'(?m)^TAP_(TYPE|DEF) (\S+)$', text) != [('TYPE', n) for n in results] + [('DEF', n) for n in definitions]):
        raise ValueError('incomplete full contracts')
    return results, definitions, deps


def main(work):
    receipt = HERE.parent / 'elements-output-proof/PREPARATION.json'
    prior = json.loads(receipt.read_text())
    inherited = check_tree(work, prior)
    before, index = s.input_map(), s.index_hash()
    coq, base = work / 'Coq', Path(prior['candidate'])
    fingerprint = s.inputs.fingerprint(coq, work)
    order, commands = closure(coq), {}
    print('Fresh tap-getter closure: ' + ', '.join(order), flush=True)
    for m in order:
        commands[m] = s.run(work, ['bash', 'build-jets.sh', '--coqc', '-q', m.replace('.', '/') + '.v'], m, 180)
        print('compiled ' + m, flush=True)
    # Compile the exact old nullable module separately, without overwriting any
    # completed base objects or the generalized module being checked.
    original = work / 'baseline/NullableBaseline.v'
    s.changed({original: (base / 'Coq' / MODIFIED).read_text()})
    extra = ['-Q', str(original.parent), 'TappathBaseline']
    commands['baseline'] = s.run(work, ['bash', 'build-jets.sh', '--coqc', '-q', *extra, str(original)], 'baseline', 180)
    baseline = reports(work, [('TappathBaseline.NullableBaseline', original)], 'baseline', commands, extra)
    results, definitions, deps = reports(work,
        [(m, coq / (m.replace('.', '/') + '.v')) for m in order], 'tap', commands)
    for name, ds in baseline[2].items():
        new = name.replace('TappathBaseline.NullableBaseline.', NULLABLE + '.')
        if deps[new] != ds:
            raise ValueError('old nullable result assumptions changed: ' + name)
    for n in PURE:
        if deps[n]:
            raise ValueError('nonclosed shared conversion: ' + n)
    old_ends = ['C.jet_elements_hash_field_jets.elements_internal_key_local_spec',
                NULLABLE + '.elements_tappath_nullable_local_spec', NULLABLE + '.elements_tappath_u8_local_spec']
    if any(deps[a] != deps[b] for a, b in zip(ENDPOINTS, old_ends)):
        raise ValueError('literal endpoint changed execution assumptions')
    inherited_deps = {}
    for folder, filename in [('elements-annex-hash', 'PREPARATION.json'),
                             ('elements-outpoint-output', 'CHECKED.json'), ('elements-output-proof', 'PREPARATION.json')]:
        inherited_deps.update(json.loads((HERE.parent / folder / filename).read_text())['dependencies'])
    for n, ds in deps.items():
        if n in inherited_deps and sorted(ds) != inherited_deps[n]:
            raise ValueError('inherited assumption drift: ' + n)
    for stem, command, timeout in [
        ('source', [sys.executable, '-B', str(HERE / 'check-source.py'), str(work)], 180),
        ('source-negative', [sys.executable, '-B', str(HERE / 'test-source.py'), str(work)], 180),
        ('ast', ['bash', 'C/check-elements-jets-generation.sh'], 180),
        ('kernel', ['bash', 'build-jets.sh', '--coqchk', '-silent', '-o', *extra,
                    'TappathBaseline.NullableBaseline', *ROOTS], 1800)]:
        print(stem, flush=True)
        commands[stem] = s.run(work, command, stem, timeout)
    s.kernel.kernel((work / 'kernel.log').read_text(), sorted((coq / 'C/jet_coqchk_axioms.expected').read_text().split()))
    check_tree(work, prior)
    if s.input_map() != before or s.index_hash() != index or s.inputs.fingerprint(coq, work) != fingerprint:
        raise ValueError('main/index/private inputs changed')
    record = dict(candidate=str(work), base_candidate=str(base), base_receipt_sha256=s.sha(receipt.read_bytes()),
                  candidate_input_sha256=fingerprint, base_input_sha256=prior['candidate_input_sha256'],
                  main_inputs=before, staged_patch_sha256=index, roots=ROOTS, fresh_modules=order,
                  new_sources=[NEW], reviewed_source_generalization=[MODIFIED],
                  results=results, definitions=definitions, endpoints=ENDPOINTS,
                  closed_shared_lemmas=PURE, dependencies={n: sorted(v) for n, v in deps.items()},
                  baseline_results=baseline[0], baseline_definitions=baseline[1],
                  baseline_dependencies={n: sorted(v) for n, v in baseline[2].items()},
                  commands=commands, source_sha256={m: s.sha((coq / (m.replace('.', '/') + '.v')).read_bytes()) for m in order},
                  object_sha256={m: s.sha((coq / (m.replace('.', '/') + '.vo')).read_bytes()) for m in order},
                  tools_sha256={n: s.sha((HERE / n).read_bytes()) for n in ['check.py', 'check-source.py', 'test-source.py']},
                  normal_registration=False, coverage_added=0, full_acceptance=False)
    changes = {HERE / 'PREPARATION.json': json.dumps(record, indent=2) + '\n'}
    for n in ['baseline-assumptions', 'baseline-contracts', 'tap-assumptions', 'tap-contracts', 'source', 'source-negative', 'ast', 'kernel']:
        changes[HERE / (n + '.log')] = (work / (n + '.log')).read_text()
    s.changed(changes)
    print('Two jets, three whole C endpoints checked; coverage not registered', flush=True)


if __name__ == '__main__':
    main(Path(sys.argv[1]).resolve())
