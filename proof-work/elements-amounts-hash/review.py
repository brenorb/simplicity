"""Reconcile both complete amounts-hash C proofs, kernel and canonical sources."""
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('amounts_hash_checked_review', HERE / 'check.py')
g = importlib.util.module_from_spec(sp)
sp.loader.exec_module(g)
s = g.s
SOURCE = HERE.parent / 'elements-amounts-hash-source'
previous = s.load('amounts_hash_report_parser', HERE.parent / 'elements-stream/review.py')
kd = s.load('amounts_hash_kernel_driver', HERE / 'kernel.py')
history = s.load('amounts_hash_completed_base_review', HERE.parent / 'elements-nonces/review.py')


def source_review(work):
    r = json.loads((SOURCE / 'SOURCE-REVIEW.json').read_text())
    result = s.load('amounts_hash_selected_source', SOURCE / 'check-source.py').check(work)
    if (r['candidate'] != str(work) or r['source_review'] != result or
        r['candidate_input_sha256'] != s.inputs.fingerprint(work / 'Coq', work) or
        r['compile_receipt_sha256'] != s.sha((HERE / 'RUN.json').read_bytes()) or
        r['staged_patch_sha256'] != s.index_hash() or
        r['inherited_source_review_sha256'] != s.sha((history.SOURCE / 'SOURCE-REVIEW.json').read_bytes()) or
        r['tools_sha256'] != {n: s.sha((SOURCE / n).read_bytes()) for n in
            ['check-source.py', 'test-source.py', 'source-model.py', 'finish-source.py']} or
        r['canonical_source_review_complete'] is not True or r['coverage_added'] != 0 or
        any(r[n] is not False for n in ['recursive_kernel_result_checked_by_this_tool',
                                     'normal_registration', 'full_acceptance'])):
        raise ValueError('amounts source evidence identity/scope differs')
    if (result['canonical_amounts_source_review_complete'] is not True or
        result['whole_contracts_reviewed'] is not True or result['original_c_getters'] != 2 or
        result['selected_jets'] != ['Elements.OutputAmountsHash', 'Elements.InputAmountsHash'] or
        result['selected_primitives'] != ['Elements.OutputAmount', 'Elements.OutputAsset',
                                         'Elements.InputAmount', 'Elements.InputAsset'] or
        (result['explicit_amount_bytes'], result['confidential_amount_bytes']) != (8, 32) or
        result['confidential_payload_interface'] != 'existing packed-field projection' or
        any(result[n] is not True for n in ['canonical_amount_pair_program_reused',
            'shared_tagged_absorber_reviewed', 'literal_asset_amount_serializers_reviewed']) or
        any(result[n] is not False for n in ['caller_cached_hashes_established',
            'arbitrary_word256_is_valid_field_element', 'formal_host_library_equivalence', 'normal_registration'])):
        raise ValueError('amounts canonical/caller boundary differs')
    commands = {'amounts-hash-source': 'check-source.py', 'amounts-hash-negative': 'test-source.py'}
    if set(r['commands']) != set(commands):
        raise ValueError('incomplete amounts source command inventory')
    for stem, name in commands.items():
        row, log = r['commands'][stem], work / (stem + '.log')
        if (row != dict(command=[sys.executable, '-B', str(SOURCE / name), str(work)],
                        exit_code=0, log_sha256=s.sha(log.read_bytes())) or
            (SOURCE / log.name).read_bytes() != log.read_bytes()):
            raise ValueError('amounts source command/exit/log differs')
    return r


def review(work):
    r = json.loads((HERE / 'CHECKED.json').read_text())
    compiled = json.loads((HERE / 'RUN.json').read_text())
    launch = json.loads((HERE / 'KERNEL-RUN.json').read_text())
    if (r != dict(compiled, commands=r['commands'], recursive_kernel_check=True,
                  kernel_launch_sha256=s.sha((HERE / 'KERNEL-RUN.json').read_bytes())) or
        compiled['recursive_kernel_check'] is not False or r['modules'] != g.MODULES or
        r['new_sources'] != g.NAMES or r['endpoints'] != g.ENDPOINTS or r['whole_c_endpoints'] != 2 or
        (r['explicit_amount_bytes'], r['confidential_amount_bytes']) != (8, 32) or
        any(r[n] is not True for n in ['shared_tagged_absorber', 'canonical_amount_pair_program_reused']) or
        r['coverage_added'] != 0 or any(r[n] is not False for n in ['caller_cached_hashes_established',
            'canonical_source_review_complete', 'normal_registration', 'full_acceptance'])):
        raise ValueError('amounts proof phase/scope differs')
    expected_launch = dict(candidate=str(work), command=kd.COMMAND,
        compiled_receipt_sha256=s.sha((HERE / 'RUN.json').read_bytes()),
        candidate_input_sha256=r['candidate_input_sha256'], staged_patch_sha256=r['staged_patch_sha256'],
        driver_sha256=s.sha((HERE / 'kernel.py').read_bytes()), recursive_kernel_check=False)
    if (launch != expected_launch or r['candidate'] != str(work) or
        r['staged_patch_sha256'] != s.index_hash() or r['main_inputs'] != g.BASE_RECORD['main_inputs'] or
        r['tools_sha256'] != {'check.py': s.sha((HERE / 'check.py').read_bytes())} or
        r['base_candidate'] != str(g.BASE) or r['base_checked_sha256'] != s.sha(g.RECEIPT.read_bytes()) or
        r['base_review_sha256'] != s.sha((history.HERE / 'EVIDENCE-REVIEW.json').read_bytes())):
        raise ValueError('amounts launch/candidate/base/main/index identity differs')
    results, definitions = [], []
    for module, name in zip(g.MODULES, g.NAMES):
        a, b = g.shared.declarations((work / 'Coq' / name).read_text(), module)
        results += a
        definitions += b
    closed = [n for n in results if n not in g.FUNEXT + g.EXECUTION]
    if ((len(results), len(definitions), len(closed)) != (22, 23, 16) or
        r['results'] != results or r['definitions'] != definitions or r['closed_results'] != closed):
        raise ValueError('incomplete amounts declarations or reports')
    for field, suffix in [('source_sha256', '.v'), ('object_sha256', '.vo')]:
        if set(r[field]) != set(g.MODULES):
            raise ValueError('incomplete amounts source/object inventory')
        for module, digest in r[field].items():
            p = work / 'Coq' / (module.replace('.', '/') + suffix)
            if p.is_symlink() or s.sha(p.read_bytes()) != digest:
                raise ValueError('amounts source/object differs')
    commands = {m: ['bash', 'build-jets.sh', '--coqc', '-q', n] for m, n in zip(g.MODULES, g.NAMES)}
    for name in ['assumptions', 'contracts']:
        commands['elements-amounts-hash-' + name] = ['bash', 'build-jets.sh', '--coqc', '-q',
            str(work / ('elements_amounts_hash_' + name + '.v'))]
    commands.update(ast=['bash', 'C/check-elements-jets-generation.sh'], kernel=kd.COMMAND)
    if set(r['commands']) != set(commands) or set(compiled['commands']) != set(commands) - {'ast', 'kernel'}:
        raise ValueError('incomplete amounts proof command inventory')
    for stem, command in commands.items():
        row, log = r['commands'][stem], work / (stem + '.log')
        if (row != dict(command=command, exit_code=0, log_sha256=s.sha(log.read_bytes())) or
            (HERE / log.name).read_bytes() != log.read_bytes() or
            stem in compiled['commands'] and compiled['commands'][stem] != row):
            raise ValueError('amounts proof command/exit/log differs')
    deps = {n: set() for n in closed}
    deps.update({n: {'FunctionalExtensionality.functional_extensionality_dep'} for n in g.FUNEXT})
    deps.update({n: s.SIX for n in g.EXECUTION})
    if r['dependencies'] != previous.report(work, 'elements-amounts-hash', g.MODULES, results, definitions, deps):
        raise ValueError('amounts reported assumptions differ')
    s.kernel.kernel((work / 'kernel.log').read_text(),
                    sorted((work / 'Coq/C/jet_coqchk_axioms.expected').read_text().split()))
    source_review(work)
    g.tree(work)
    inherited = json.loads((history.HERE / 'EVIDENCE-REVIEW.json').read_text())
    if (inherited['review'] != history.review(g.BASE) or
        r['candidate_input_sha256'] != s.inputs.fingerprint(work / 'Coq', work)):
        raise ValueError('inherited evidence or immutable amounts sources differ')
    return dict(candidate=str(work), results=22, definitions=23, closed_results=16,
        pure_funext_results=3, execution_results=3, whole_c_endpoints=2, endpoint_inherited_assumptions=6,
        recursive_kernel_check=True, inherited_source_changes=0,
        canonical_amounts_source_review_complete=True, shared_tagged_absorber=True,
        canonical_amount_pair_program_reused=True, explicit_amount_bytes=8, confidential_amount_bytes=32,
        caller_cached_hashes_established=False, formal_host_library_equivalence=False,
        normal_registration=False, coverage_added=0, full_acceptance=False)


def finish(work):
    if (HERE / 'EVIDENCE-REVIEW.json').exists():
        raise ValueError('amounts evidence review already recorded; inspect existing evidence')
    before, index = s.input_map(), s.index_hash()
    result = review(work)
    row = s.run(work, [sys.executable, '-B', str(HERE / 'test-review.py'), str(work)], 'evidence-tests', 900)
    if review(work) != result or s.input_map() != before or s.index_hash() != index:
        raise ValueError('amounts evidence review changed main/index/private inputs')
    record = dict(review=result, checked_sha256=s.sha((HERE / 'CHECKED.json').read_bytes()),
        compile_sha256=s.sha((HERE / 'RUN.json').read_bytes()),
        kernel_launch_sha256=s.sha((HERE / 'KERNEL-RUN.json').read_bytes()),
        source_review_sha256=s.sha((SOURCE / 'SOURCE-REVIEW.json').read_bytes()),
        checks={'evidence-tests': row}, candidate_input_sha256=s.inputs.fingerprint(work / 'Coq', work),
        tools_sha256={n: s.sha((HERE / n).read_bytes()) for n in ['check.py', 'kernel.py', 'review.py', 'test-review.py']},
        canonical_source_review_complete=True, normal_registration=False, full_acceptance=False)
    s.changed({HERE / 'EVIDENCE-REVIEW.json': json.dumps(record, indent=2) + '\n',
               HERE / 'evidence-tests.log': (work / 'evidence-tests.log').read_text()})
    print('Both amounts-hash C proof/kernel/source records independently reviewed; registration remains', flush=True)


if __name__ == '__main__':
    if len(sys.argv) == 2:
        print(json.dumps(review(Path(sys.argv[1]).resolve()), indent=2))
    elif len(sys.argv) == 3 and sys.argv[1] == 'finish':
        finish(Path(sys.argv[2]).resolve())
    else:
        raise ValueError('usage: review.py [finish] PRIVATE_TREE')
