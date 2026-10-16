"""Independent complete proof/kernel/source review of the tapenv endpoint."""
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('tapenv_checked_review', HERE / 'check.py')
g = importlib.util.module_from_spec(sp)
sp.loader.exec_module(g)
s = g.s
SOURCE = HERE.parent / 'elements-tapenv-source'
previous = s.load('tapenv_previous_evidence', HERE.parent / 'elements-tapleaf/review.py')
common = previous.previous
CLOSED = [g.MODULE + '.elements_tap_env_hash_spec_parametric']
FUNEXT = [g.MODULE + '.elements_tap_env_hash_spec_sem']


def source_review(work):
    r = json.loads((SOURCE / 'SOURCE-REVIEW.json').read_text())
    result = s.load('tapenv_selected_source', SOURCE / 'check-source.py').check(work)
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
        raise ValueError('tapenv source review identity/scope differs')
    if (result['canonical_tapenv_source_review_complete'] is not True or
        result['whole_contracts_reviewed'] is not True or result['original_c_getters'] != 1 or
        result['native_word_internal_key'] is not True or
        result['field_or_point_validity_not_assumed'] is not True or
        any(result[n] is not False for n in ['caller_cached_hashes_established',
            'formal_host_library_equivalence', 'normal_registration'])):
        raise ValueError('tapenv canonical/caller boundary differs')
    expected = {'tapenv-source': 'check-source.py', 'tapenv-negative': 'test-source.py'}
    if set(r['commands']) != set(expected):
        raise ValueError('incomplete tapenv source command inventory')
    for stem, script in expected.items():
        row, log = r['commands'][stem], work / (stem + '.log')
        if (row['command'] != [sys.executable, '-B', str(SOURCE / script), str(work)] or
            row['exit_code'] != 0 or row['log_sha256'] != s.sha(log.read_bytes()) or
            (SOURCE / log.name).read_bytes() != log.read_bytes()):
            raise ValueError('tapenv source command/exit/log differs')
    return r


def review(work):
    r = json.loads((HERE / 'CHECKED.json').read_text())
    compiled = json.loads((HERE / 'RUN.json').read_text())
    launch = json.loads((HERE / 'KERNEL-RUN.json').read_text())
    if (r != dict(compiled, commands=r['commands'], recursive_kernel_check=True,
                  kernel_launch_sha256=s.sha((HERE / 'KERNEL-RUN.json').read_bytes())) or
        compiled['recursive_kernel_check'] is not False or r['modules'] != [g.MODULE] or
        r['new_sources'] != g.NEW or r['fresh_modules'] != g.FRESH or r['endpoints'] != [g.ENDPOINT] or
        r['closed_results'] != CLOSED or r['whole_c_endpoints'] != 1 or
        r['tapleaf_and_tappath_program_semantics_reused'] is not True or r['native_word_internal_key'] is not True or r['coverage_added'] != 0 or
        any(r[n] is not False for n in ['caller_cached_hashes_established',
            'canonical_source_review_complete', 'normal_registration', 'full_acceptance'])):
        raise ValueError('tapenv proof phase/scope differs')
    expected_launch = dict(candidate=str(work), command=g.KERNEL,
        compiled_receipt_sha256=s.sha((HERE / 'RUN.json').read_bytes()),
        candidate_input_sha256=r['candidate_input_sha256'], staged_patch_sha256=r['staged_patch_sha256'],
        recursive_kernel_check=False)
    if (launch != expected_launch or r['candidate'] != str(work) or
        r['staged_patch_sha256'] != s.index_hash() or
        r['main_inputs'] != g.leaf.BASE_RECORD['main_inputs_at_compile'] or
        r['tools_sha256'] != {'check.py': s.sha((HERE / 'check.py').read_bytes())} or
        r['base_candidate'] != str(g.BASE) or
        r['base_checked_sha256'] != s.sha(g.leaf.RECEIPT.read_bytes()) or
        r['tapleaf_compile_sha256'] != s.sha((previous.HERE / 'RUN.json').read_bytes())):
        raise ValueError('tapenv launch/candidate/base/main/index identity differs')
    results, definitions = [], []
    for module, name in zip([g.MODULE], [g.NAME]):
        a, b = g.shared.declarations((work / 'Coq' / name).read_text(), module)
        results += a
        definitions += b
    if ((len(results), len(definitions)) != (3, 2) or r['results'] != results or
        r['definitions'] != definitions or set(results) != set(CLOSED + FUNEXT + [g.ENDPOINT])):
        raise ValueError('incomplete tapenv declarations or reports')
    for field, suffix in [('source_sha256', '.v'), ('object_sha256', '.vo')]:
        if set(r[field]) != set(g.FRESH):
            raise ValueError('incomplete tapenv source/object inventory')
        for module, digest in r[field].items():
            p = work / 'Coq' / (module.replace('.', '/') + suffix)
            if p.is_symlink() or s.sha(p.read_bytes()) != digest:
                raise ValueError('tapenv source/object differs')
    commands = {m: ['bash', 'build-jets.sh', '--coqc', '-q', m.replace('.', '/') + '.v'] for m in g.FRESH}
    for name in ['assumptions', 'contracts']:
        commands['elements-tapenv-' + name] = ['bash', 'build-jets.sh', '--coqc', '-q',
            str(work / ('elements_tapenv_' + name + '.v'))]
    commands.update(ast=['bash', 'C/check-elements-jets-generation.sh'], kernel=g.KERNEL)
    if set(r['commands']) != set(commands) or set(compiled['commands']) != set(commands) - {'ast', 'kernel'}:
        raise ValueError('incomplete tapenv proof command inventory')
    for stem, command in commands.items():
        row, log = r['commands'][stem], work / (stem + '.log')
        if (row['command'] != command or row['exit_code'] != 0 or row['log_sha256'] != s.sha(log.read_bytes()) or
            (HERE / log.name).read_bytes() != log.read_bytes() or
            stem in compiled['commands'] and compiled['commands'][stem] != row):
            raise ValueError('tapenv proof command/exit/log differs')
    deps = {n: set() for n in CLOSED}
    deps.update({n: {'FunctionalExtensionality.functional_extensionality_dep'} for n in FUNEXT})
    deps[g.ENDPOINT] = s.SIX
    if r['dependencies'] != common.report(work, 'elements-tapenv', [g.MODULE], results, definitions, deps):
        raise ValueError('tapenv reported assumptions differ')
    s.kernel.kernel((work / 'kernel.log').read_text(), sorted((work / 'Coq/C/jet_coqchk_axioms.expected').read_text().split()))
    source_review(work)
    g.tree(work)
    base = json.loads((previous.HERE / 'EVIDENCE-REVIEW.json').read_text())
    # The original main420 map is historical evidence, not a requirement that
    # today's main stay420 forever. Verify its actual bytes in this immutable
    # private tree; finish() separately checks live main/index preservation.
    baseline = json.loads(common.g.reader.BASE_RECEIPT.read_text())
    if (base['review'] != previous.review(Path(json.loads((previous.HERE / 'RUN.json').read_text())['candidate'])) or
        common.fingerprint_known_sources(work, r['main_inputs']) != baseline['audit_input_sha256'] or
        r['candidate_input_sha256'] != s.inputs.fingerprint(work / 'Coq', work)):
        raise ValueError('inherited Elements evidence or immutable tapenv source differs')
    return dict(candidate=str(work), results=3, definitions=2, closed_results=1,
        pure_funext_results=1, whole_c_endpoints=1, endpoint_inherited_assumptions=6,
        recursive_kernel_check=True, inherited_source_changes=0,
        canonical_tapenv_source_review_complete=True, native_word_internal_key=True,
        tapleaf_and_tappath_program_semantics_reused=True, caller_cached_hashes_established=False,
        formal_host_library_equivalence=False, normal_registration=False,
        coverage_added=0, full_acceptance=False)


def finish(work):
    if (HERE / 'EVIDENCE-REVIEW.json').exists():
        raise ValueError('tapenv evidence review already recorded; inspect existing evidence')
    before, index = s.input_map(), s.index_hash()
    result = review(work)
    row = s.run(work, [sys.executable, '-B', str(HERE / 'test-review.py'), str(work)], 'evidence-tests', 900)
    if review(work) != result or s.input_map() != before or s.index_hash() != index:
        raise ValueError('tapenv evidence review changed main/index/private inputs')
    record = dict(review=result, checked_sha256=s.sha((HERE / 'CHECKED.json').read_bytes()),
        compile_sha256=s.sha((HERE / 'RUN.json').read_bytes()),
        kernel_launch_sha256=s.sha((HERE / 'KERNEL-RUN.json').read_bytes()),
        source_review_sha256=s.sha((SOURCE / 'SOURCE-REVIEW.json').read_bytes()),
        checks={'evidence-tests': row}, candidate_input_sha256=s.inputs.fingerprint(work / 'Coq', work),
        tools_sha256={n: s.sha((HERE / n).read_bytes()) for n in ['check.py', 'review.py', 'test-review.py']},
        canonical_source_review_complete=True, normal_registration=False, full_acceptance=False)
    s.changed({HERE / 'EVIDENCE-REVIEW.json': json.dumps(record, indent=2) + '\n',
               HERE / 'evidence-tests.log': (work / 'evidence-tests.log').read_text()})
    print('Original C tapenv proof/kernel/source evidence independently reviewed; registration remains', flush=True)


if __name__ == '__main__':
    if len(sys.argv) == 2:
        print(json.dumps(review(Path(sys.argv[1]).resolve()), indent=2))
    elif len(sys.argv) == 3 and sys.argv[1] == 'finish':
        finish(Path(sys.argv[2]).resolve())
    else:
        raise ValueError('usage: review.py [finish] PRIVATE_TREE')
