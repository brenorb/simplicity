"""Independent complete proof/kernel/source review of the tapleaf endpoint."""
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('tapleaf_checked_review', HERE / 'check.py')
g = importlib.util.module_from_spec(sp)
sp.loader.exec_module(g)
s = g.s
SOURCE = HERE.parent / 'elements-tapleaf-source'
previous = s.load('tapleaf_previous_evidence', HERE.parent / 'elements-stream/review.py')
kd = s.load('tapleaf_kernel_driver', HERE / 'kernel.py')
CLOSED = [g.MODULE + '.' + n for n in ['elements_tapleaf_ascii_string',
    'elements_tapleaf_prefix_matches', 'elements_tapleaf_size_matches',
    'elements_tapleaf_hash_spec_parametric']]
FUNEXT = [g.MODULE + '.elements_tapleaf_hash_spec_sem']


def source_review(work):
    r = json.loads((SOURCE / 'SOURCE-REVIEW.json').read_text())
    result = s.load('tapleaf_selected_source', SOURCE / 'check-source.py').check(work)
    if (r['candidate'] != str(work) or r['source_review'] != result or
        r['candidate_input_sha256'] != s.inputs.fingerprint(work / 'Coq', work) or
        r['compile_receipt_sha256'] != s.sha((HERE / 'RUN.json').read_bytes()) or
        r['staged_patch_sha256'] != s.index_hash() or
        r['inherited_source_review_sha256'] != s.sha((previous.SOURCE / 'SOURCE-REVIEW.json').read_bytes()) or
        r['tools_sha256'] != {n: s.sha((SOURCE / n).read_bytes()) for n in
            ['check-source.py', 'test-source.py', 'source-model.py', 'finish-source.py']} or
        r['canonical_source_review_complete'] is not True or r['coverage_added'] != 0 or
        any(r[n] is not False for n in ['recursive_kernel_result_checked_by_this_tool',
                                     'normal_registration', 'full_acceptance'])):
        raise ValueError('tapleaf source review identity/scope differs')
    if (result['canonical_tapleaf_source_review_complete'] is not True or
        result['whole_contracts_reviewed'] is not True or result['original_c_getters'] != 1 or
        result['tagged_midstate_literal'] is not True or
        result['selected_sha_tag_helpers_reviewed'] is not True or
        any(result[n] is not False for n in ['caller_cached_hashes_established',
            'formal_host_library_equivalence', 'normal_registration'])):
        raise ValueError('tapleaf canonical/caller boundary differs')
    expected = {'tapleaf-source': 'check-source.py', 'tapleaf-negative': 'test-source.py'}
    if set(r['commands']) != set(expected):
        raise ValueError('incomplete tapleaf source command inventory')
    for stem, script in expected.items():
        row, log = r['commands'][stem], work / (stem + '.log')
        if (row['command'] != [sys.executable, '-B', str(SOURCE / script), str(work)] or
            row['exit_code'] != 0 or row['log_sha256'] != s.sha(log.read_bytes()) or
            (SOURCE / log.name).read_bytes() != log.read_bytes()):
            raise ValueError('tapleaf source command/exit/log differs')
    return r


def review(work):
    r = json.loads((HERE / 'CHECKED.json').read_text())
    compiled = json.loads((HERE / 'RUN.json').read_text())
    launch = json.loads((HERE / 'KERNEL-RUN.json').read_text())
    if (r != dict(compiled, commands=r['commands'], recursive_kernel_check=True,
                  kernel_launch_sha256=s.sha((HERE / 'KERNEL-RUN.json').read_bytes())) or
        compiled['recursive_kernel_check'] is not False or r['modules'] != [g.MODULE] or
        r['new_sources'] != [g.NAME] or r['endpoints'] != [g.ENDPOINT] or
        r['closed_results'] != CLOSED or r['whole_c_endpoints'] != 1 or
        r['tag_derived_from_literal_ascii'] is not True or r['coverage_added'] != 0 or
        any(r[n] is not False for n in ['caller_cached_hashes_established',
            'canonical_source_review_complete', 'normal_registration', 'full_acceptance'])):
        raise ValueError('tapleaf proof phase/scope differs')
    expected_launch = dict(candidate=str(work), command=kd.COMMAND,
        compiled_receipt_sha256=s.sha((HERE / 'RUN.json').read_bytes()),
        candidate_input_sha256=r['candidate_input_sha256'], staged_patch_sha256=r['staged_patch_sha256'],
        driver_sha256=s.sha((HERE / 'kernel.py').read_bytes()), recursive_kernel_check=False)
    if (launch != expected_launch or r['candidate'] != str(work) or
        r['staged_patch_sha256'] != s.index_hash() or
        r['main_inputs'] != g.BASE_RECORD['main_inputs_at_compile'] or
        r['tools_sha256'] != {'check.py': s.sha((HERE / 'check.py').read_bytes())} or
        r['base_candidate'] != str(g.BASE) or
        r['base_checked_sha256'] != s.sha(g.RECEIPT.read_bytes()) or
        r['base_review_sha256'] != s.sha((previous.HERE / 'EVIDENCE-REVIEW.json').read_bytes())):
        raise ValueError('tapleaf launch/candidate/base/main/index identity differs')
    results, definitions = [], []
    for module, name in zip([g.MODULE], [g.NAME]):
        a, b = g.shared.declarations((work / 'Coq' / name).read_text(), module)
        results += a
        definitions += b
    if ((len(results), len(definitions)) != (6, 8) or r['results'] != results or
        r['definitions'] != definitions or set(results) != set(CLOSED + FUNEXT + [g.ENDPOINT])):
        raise ValueError('incomplete tapleaf declarations or reports')
    for field, suffix in [('source_sha256', '.v'), ('object_sha256', '.vo')]:
        if set(r[field]) != set([g.MODULE]):
            raise ValueError('incomplete tapleaf source/object inventory')
        for module, digest in r[field].items():
            p = work / 'Coq' / (module.replace('.', '/') + suffix)
            if p.is_symlink() or s.sha(p.read_bytes()) != digest:
                raise ValueError('tapleaf source/object differs')
    commands = {m: ['bash', 'build-jets.sh', '--coqc', '-q', n] for m, n in zip([g.MODULE], [g.NAME])}
    for name in ['assumptions', 'contracts']:
        commands['elements-tapleaf-' + name] = ['bash', 'build-jets.sh', '--coqc', '-q',
            str(work / ('elements_tapleaf_' + name + '.v'))]
    commands.update(ast=['bash', 'C/check-elements-jets-generation.sh'], kernel=kd.COMMAND)
    if set(r['commands']) != set(commands) or set(compiled['commands']) != set(commands) - {'ast', 'kernel'}:
        raise ValueError('incomplete tapleaf proof command inventory')
    for stem, command in commands.items():
        row, log = r['commands'][stem], work / (stem + '.log')
        if (row['command'] != command or row['exit_code'] != 0 or row['log_sha256'] != s.sha(log.read_bytes()) or
            (HERE / log.name).read_bytes() != log.read_bytes() or
            stem in compiled['commands'] and compiled['commands'][stem] != row):
            raise ValueError('tapleaf proof command/exit/log differs')
    deps = {n: set() for n in CLOSED}
    deps.update({n: {'FunctionalExtensionality.functional_extensionality_dep'} for n in FUNEXT})
    deps[g.ENDPOINT] = s.SIX
    if r['dependencies'] != previous.report(work, 'elements-tapleaf', [g.MODULE], results, definitions, deps):
        raise ValueError('tapleaf reported assumptions differ')
    s.kernel.kernel((work / 'kernel.log').read_text(), sorted((work / 'Coq/C/jet_coqchk_axioms.expected').read_text().split()))
    source_review(work)
    g.tree(work)
    base = json.loads((previous.HERE / 'EVIDENCE-REVIEW.json').read_text())
    # The original main420 map is historical evidence, not a requirement that
    # today's main stay420 forever. Verify its actual bytes in this immutable
    # private tree; finish() separately checks live main/index preservation.
    baseline = json.loads(previous.g.reader.BASE_RECEIPT.read_text())
    if (base['review'] != previous.review(g.BASE) or
        previous.fingerprint_known_sources(work, r['main_inputs']) != baseline['audit_input_sha256'] or
        r['candidate_input_sha256'] != s.inputs.fingerprint(work / 'Coq', work)):
        raise ValueError('inherited Elements evidence or immutable tapleaf source differs')
    return dict(candidate=str(work), results=6, definitions=8, closed_results=4,
        pure_funext_results=1, whole_c_endpoints=1, endpoint_inherited_assumptions=6,
        recursive_kernel_check=True, inherited_source_changes=0,
        canonical_tapleaf_source_review_complete=True, literal_tag_derived_from_ascii=True,
        tagged_hash_semantics_reused=True, caller_cached_hashes_established=False,
        formal_host_library_equivalence=False, normal_registration=False,
        coverage_added=0, full_acceptance=False)


def finish(work):
    if (HERE / 'EVIDENCE-REVIEW.json').exists():
        raise ValueError('tapleaf evidence review already recorded; inspect existing evidence')
    before, index = s.input_map(), s.index_hash()
    result = review(work)
    row = s.run(work, [sys.executable, '-B', str(HERE / 'test-review.py'), str(work)], 'evidence-tests', 900)
    if review(work) != result or s.input_map() != before or s.index_hash() != index:
        raise ValueError('tapleaf evidence review changed main/index/private inputs')
    record = dict(review=result, checked_sha256=s.sha((HERE / 'CHECKED.json').read_bytes()),
        compile_sha256=s.sha((HERE / 'RUN.json').read_bytes()),
        kernel_launch_sha256=s.sha((HERE / 'KERNEL-RUN.json').read_bytes()),
        source_review_sha256=s.sha((SOURCE / 'SOURCE-REVIEW.json').read_bytes()),
        checks={'evidence-tests': row}, candidate_input_sha256=s.inputs.fingerprint(work / 'Coq', work),
        tools_sha256={n: s.sha((HERE / n).read_bytes()) for n in ['check.py', 'kernel.py', 'review.py', 'test-review.py']},
        canonical_source_review_complete=True, normal_registration=False, full_acceptance=False)
    s.changed({HERE / 'EVIDENCE-REVIEW.json': json.dumps(record, indent=2) + '\n',
               HERE / 'evidence-tests.log': (work / 'evidence-tests.log').read_text()})
    print('Original C tapleaf proof/kernel/source evidence independently reviewed; registration remains', flush=True)


if __name__ == '__main__':
    if len(sys.argv) == 2:
        print(json.dumps(review(Path(sys.argv[1]).resolve()), indent=2))
    elif len(sys.argv) == 3 and sys.argv[1] == 'finish':
        finish(Path(sys.argv[2]).resolve())
    else:
        raise ValueError('usage: review.py [finish] PRIVATE_TREE')
