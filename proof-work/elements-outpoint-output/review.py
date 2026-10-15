"""Review the three-endpoint kernel checkpoint, not canonical-source admission."""
import importlib.util
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('indexed_literal_review_support', HERE.parent / 'elements-count/support.py')
s = importlib.util.module_from_spec(spec)
spec.loader.exec_module(s)


def review():
    r = json.loads((HERE / 'CHECKED.json').read_text())
    work, base = Path(r['candidate']), Path(r['base_candidate'])
    coq = work / 'Coq'
    priorpath = HERE.parent / 'elements-annex-hash/PREPARATION.json'
    prior = json.loads(priorpath.read_text())
    module, source = 'C.jet_elements_indexed_literal', 'C/jet_elements_indexed_literal.v'
    roots = ['C.jet_elements_indexed_ptr_jets', 'C.jet_elements_current_input_jets', module]
    if (r['namespace'] != 'C' or r['roots'] != roots or r['new_sources'] != [source] or r['fresh_modules'] != [module] or
            r['canonical_source_review_complete'] is not False or r['normal_registration'] is not False or
            r['coverage_added'] != 0 or r['full_acceptance'] is not False or
            str(base) != prior['candidate'] or r['base_input_sha256'] != prior['candidate_input_sha256'] or
            r['prior_preparation_sha256'] != s.sha(priorpath.read_bytes()) or
            r['checkpoint_driver_sha256'] != s.sha((HERE / 'checkpoint.py').read_bytes())):
        raise ValueError('wrong checkpoint/base/admission scope')
    if (s.inputs.fingerprint(base / 'Coq', base) != r['base_input_sha256'] or
            s.inputs.fingerprint(coq, work) != r['candidate_input_sha256'] or
            s.input_map() != r['main_inputs'] or s.index_hash() != r['staged_patch_sha256']):
        raise ValueError('source/main/index drift')
    paths = s.load('indexed_literal_review_paths', HERE.parent / 'elements-pegin-normal/review.py').source_paths
    inherited = paths(base / 'Coq')
    if paths(coq) != inherited | {source}:
        raise ValueError('unexpected source/registry inventory')
    for name in inherited:
        if (coq / name).read_bytes() != (base / 'Coq' / name).read_bytes():
            raise ValueError('inherited source changed: ' + name)
    path = coq / source
    if (path.read_bytes() != (HERE / 'source/jet_elements_indexed_literal.v.source').read_bytes() or
            s.sha(path.read_bytes()) != r['source_sha256'] or path.with_suffix('.vo').is_symlink() or
            s.sha(path.with_suffix('.vo').read_bytes()) != r['object_sha256']):
        raise ValueError('new archive/source/object drift')
    if r['reused_objects_sha256'] != prior['object_sha256']:
        raise ValueError('incomplete inherited object inventory')
    for m, digest in r['reused_objects_sha256'].items():
        obj = coq / (m.replace('.', '/') + '.vo')
        if obj.is_symlink() or s.sha(obj.read_bytes()) != digest:
            raise ValueError('inherited object drift')
    code = s.safe_source(path.read_text(), module)
    results = [module + '.' + n for n in re.findall(r"^(?:Lemma|Theorem|Corollary)\s+([A-Za-z_][\w']*)", code, re.M)]
    definitions = [module + '.' + n for n in re.findall(r"^(?:Definition|Fixpoint|Record)\s+([A-Za-z_][\w']*)", code, re.M)]
    if (len(results), len(definitions)) != (8, 5) or r['results'] != results or r['definitions'] != definitions:
        raise ValueError('wrong public inventory')
    deps = s.reports.assumptions((work / 'assumptions.log').read_text())
    pure = [module + '.elements_indexed_literal_matches', module + '.haskell_encode_outpoint_matches']
    endpoints = [module + '.elements_' + n + '_literal_local_spec' for n in ['input_prev_outpoint', 'current_prev_outpoint', 'output_script_hash']]
    originals = ['C.jet_elements_indexed_ptr_jets.elements_input_prev_outpoint_local_spec',
                 'C.jet_elements_current_input_jets.elements_current_prev_outpoint_local_spec',
                 'C.jet_elements_indexed_ptr_jets.elements_output_script_hash_local_spec']
    if (set(deps) != set(results) or {n: sorted(d) for n, d in deps.items()} != r['dependencies'] or
            any(not d <= s.SIX for d in deps.values()) or r['closed_shared_lemmas'] != pure or r['endpoints'] != endpoints or
            any(deps[n] for n in pure) or
            any(sorted(deps[n]) != prior['dependencies'][old] for n, old in zip(endpoints, originals))):
        raise ValueError('new/unreviewed assumptions or nonclosed shared lemmas')
    report = (work / 'contracts.log').read_text()
    if ('...' in report or re.search(r'\?[A-Za-z]', report) or re.findall(r'(?m)^INDEXED_LITERAL_(TYPE|DEF) (\S+)$', report) !=
            [('TYPE', n) for n in results] + [('DEF', n) for n in definitions]):
        raise ValueError('incomplete full contract report')
    commands = {'literal': ['bash', 'build-jets.sh', '--coqc', '-q', source],
                **{n: ['bash', 'build-jets.sh', '--coqc', '-q', str(work / (n + '.v'))] for n in ['assumptions', 'contracts']},
                'kernel': ['bash', 'build-jets.sh', '--coqchk', '-silent', '-o', *roots]}
    if set(r['commands']) != set(commands):
        raise ValueError('missing compilation/check stage')
    for n, cmd in commands.items():
        row = r['commands'][n]
        if (row['command'] != cmd or row['exit_code'] != 0 or row['log_sha256'] != s.sha((work / (n + '.log')).read_bytes()) or
                (HERE / (n + '.log')).read_bytes() != (work / (n + '.log')).read_bytes()):
            raise ValueError('command/flags/status/log evidence changed')
    s.kernel.kernel((work / 'kernel.log').read_text(), sorted((coq / 'C/jet_coqchk_axioms.expected').read_text().split()))
    return {'candidate': str(work), 'jets_kernel_checked': 3, 'new_results': 8, 'new_definitions': 5,
            'closed_shared_lemmas': 2, 'fresh_modules': 1, 'reused_immutable_modules': len(r['reused_objects_sha256']),
            'canonical_source_review_complete': False, 'normal_registration': False, 'coverage_added': 0, 'full_acceptance': False}


if __name__ == '__main__':
    print(json.dumps(review(), indent=2))
