# Historical-only adapter of the frozen annexes reviewer. The original
# recorder/reviewer and receipt stay untouched. Only the live-main420 equality
# is replaced by the exact accepted historical map plus actual private bytes;
# all original proof/source/object/type/assumption/kernel/command checks stay.
# Frozen donor SHA-256: 053ea381c7efd1c0ffe8969ce5563b096533d04320b080ea7e8a47ba6f85f5dc
"""Independent complete proof/kernel/source review of the annexes endpoint."""
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent.parent / 'elements-annexes'
sp = importlib.util.spec_from_file_location('annexes_checked_review', HERE / 'check.py')
g = importlib.util.module_from_spec(sp)
sp.loader.exec_module(g)
s = g.s
SOURCE = HERE.parent / 'elements-annexes-source'
previous = s.load('annexes_previous_evidence', HERE.parent / 'elements-stream/review.py')
CLOSED = [g.MODULES[0] + '.hash_elems_spec_parametric',
          g.MODULES[1] + '.elements_input_annexes_hash_spec_parametric',
          g.MODULES[1] + '.elements_annexes_of_sem']
FUNEXT = [g.MODULES[0] + '.' + n for n in
          ['gen_loop_body_reader_sem', 'gen_loop_run_reader_sem', 'hr_copair', 'hash_elems_reader_sem']]
FUNEXT += [g.MODULES[1] + '.elements_input_annexes_hash_spec_sem']


def source_review(work):
    r = json.loads((SOURCE / 'SOURCE-REVIEW.json').read_text())
    result = s.load('annexes_selected_source', SOURCE / 'check-source.py').check(work)
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
        raise ValueError('annexes source review identity/scope differs')
    if (result['canonical_annex_loop_source_review_complete'] is not True or
        result['whole_contracts_reviewed'] is not True or result['original_c_getters'] != 1 or
        result['absent_and_empty_annex_distinct'] is not True or
        result['shared_bitcoin_annex_program_matches_elements'] is not True or
        any(result[n] is not False for n in ['caller_cached_hashes_established',
            'formal_host_library_equivalence', 'normal_registration'])):
        raise ValueError('annexes canonical/caller boundary differs')
    expected = {'annexes-source': 'check-source.py', 'annexes-negative': 'test-source.py'}
    if set(r['commands']) != set(expected):
        raise ValueError('incomplete annexes source command inventory')
    for stem, script in expected.items():
        row, log = r['commands'][stem], work / (stem + '.log')
        if (row['command'] != [sys.executable, '-B', str(SOURCE / script), str(work)] or
            row['exit_code'] != 0 or row['log_sha256'] != s.sha(log.read_bytes()) or
            (SOURCE / log.name).read_bytes() != log.read_bytes()):
            raise ValueError('annexes source command/exit/log differs')
    return r


def review(work):
    r = json.loads((HERE / 'CHECKED.json').read_text())
    compiled = json.loads((HERE / 'RUN.json').read_text())
    launch = json.loads((HERE / 'KERNEL-RUN.json').read_text())
    if (r != dict(compiled, commands=r['commands'], recursive_kernel_check=True,
                  kernel_launch_sha256=s.sha((HERE / 'KERNEL-RUN.json').read_bytes())) or
        compiled['recursive_kernel_check'] is not False or r['modules'] != g.MODULES or
        r['new_sources'] != g.NEW or r['endpoints'] != [g.ENDPOINT] or
        r['closed_results'] != CLOSED or r['whole_c_endpoints'] != 1 or
        r['environment_generic_loop'] is not True or
        r['existing_pure_prefix_and_counter_proofs_reused'] is not True or r['coverage_added'] != 0 or
        any(r[n] is not False for n in ['caller_cached_hashes_established',
            'canonical_source_review_complete', 'normal_registration', 'full_acceptance'])):
        raise ValueError('annexes proof phase/scope differs')
    expected_launch = dict(candidate=str(work), command=g.KERNEL,
        compiled_receipt_sha256=s.sha((HERE / 'RUN.json').read_bytes()),
        candidate_input_sha256=r['candidate_input_sha256'], staged_patch_sha256=r['staged_patch_sha256'],
        recursive_kernel_check=False)
    if (launch != expected_launch or r['candidate'] != str(work) or
        r['staged_patch_sha256'] != s.index_hash() or r['main_inputs'] != g.BASE_RECORD['main_inputs_at_compile'] or
        r['tools_sha256'] != {'check.py': s.sha((HERE / 'check.py').read_bytes())} or
        r['base_candidate'] != str(g.BASE) or
        r['base_checked_sha256'] != s.sha(g.BASE_RECEIPT.read_bytes()) or
        r['base_review_sha256'] != s.sha((previous.HERE / 'EVIDENCE-REVIEW.json').read_bytes())):
        raise ValueError('annexes launch/candidate/base/main/index identity differs')
    results, definitions = [], []
    for module, name in zip(g.MODULES, g.NEW):
        a, b = g.shared.declarations((work / 'Coq' / name).read_text(), module)
        results += a
        definitions += b
    if ((len(results), len(definitions)) != (9, 4) or r['results'] != results or
        r['definitions'] != definitions or set(results) != set(CLOSED + FUNEXT + [g.ENDPOINT])):
        raise ValueError('incomplete annexes declarations or reports')
    for field, suffix in [('source_sha256', '.v'), ('object_sha256', '.vo')]:
        if set(r[field]) != set(g.MODULES):
            raise ValueError('incomplete annexes source/object inventory')
        for module, digest in r[field].items():
            p = work / 'Coq' / (module.replace('.', '/') + suffix)
            if p.is_symlink() or s.sha(p.read_bytes()) != digest:
                raise ValueError('annexes source/object differs')
    commands = {m: ['bash', 'build-jets.sh', '--coqc', '-q', n] for m, n in zip(g.MODULES, g.NEW)}
    for name in ['assumptions', 'contracts']:
        commands['elements-annexes-' + name] = ['bash', 'build-jets.sh', '--coqc', '-q',
            str(work / ('elements_annexes_' + name + '.v'))]
    commands.update(ast=['bash', 'C/check-elements-jets-generation.sh'], kernel=g.KERNEL)
    if set(r['commands']) != set(commands) or set(compiled['commands']) != set(commands) - {'ast', 'kernel'}:
        raise ValueError('incomplete annexes proof command inventory')
    for stem, command in commands.items():
        row, log = r['commands'][stem], work / (stem + '.log')
        if (row['command'] != command or row['exit_code'] != 0 or row['log_sha256'] != s.sha(log.read_bytes()) or
            (HERE / log.name).read_bytes() != log.read_bytes() or
            stem in compiled['commands'] and compiled['commands'][stem] != row):
            raise ValueError('annexes proof command/exit/log differs')
    deps = {n: set() for n in CLOSED}
    deps.update({n: {'FunctionalExtensionality.functional_extensionality_dep'} for n in FUNEXT})
    deps[g.ENDPOINT] = s.SIX
    if r['dependencies'] != previous.report(work, 'elements-annexes', g.MODULES, results, definitions, deps):
        raise ValueError('annexes reported assumptions differ')
    s.kernel.kernel((work / 'kernel.log').read_text(), sorted((work / 'Coq/C/jet_coqchk_axioms.expected').read_text().split()))
    source_review(work)
    g.tree(work)
    base = json.loads((previous.HERE / 'EVIDENCE-REVIEW.json').read_text())
    baseline = json.loads(previous.g.reader.BASE_RECEIPT.read_text())
    if (base['review'] != previous.review(g.BASE) or
        previous.fingerprint_known_sources(work, r['main_inputs']) != baseline['audit_input_sha256'] or
        r['candidate_input_sha256'] != s.inputs.fingerprint(work / 'Coq', work)):
        raise ValueError('inherited Elements evidence or immutable annexes source differs')
    return dict(candidate=str(work), results=9, definitions=4, closed_results=3,
        pure_funext_results=5, whole_c_endpoints=1, endpoint_inherited_assumptions=6,
        recursive_kernel_check=True, inherited_source_changes=0,
        canonical_annex_loop_source_review_complete=True, environment_generic_loop=True,
        shared_prefix_counter_proofs_reused=True, caller_cached_hashes_established=False,
        formal_host_library_equivalence=False, normal_registration=False,
        coverage_added=0, full_acceptance=False)

