"""Independent review of the real SHA execution/startup/source evidence.

Review historical input bytes in the immutable private tree, not today's main
checkout. finish() separately checks live-main/index preservation. No kernel
job is restarted and no assumption/contract is replaced by a weaker claim.
"""
import importlib.util
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('sha_canonical_independent_review', HERE / 'check.py')
g = importlib.util.module_from_spec(sp)
sp.loader.exec_module(g)
s = g.s
kd = s.load('sha_canonical_reviewed_kernel', HERE / 'kernel.py')
SOURCE = HERE.parent / 'sha-canonical-startup-source'
history = s.load('sha_canonical_historical_bytes', HERE.parent / 'elements-stream/review.py')
INHERITED = {
    'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep',
    'ClassicalDedekindReals.sig_forall_dec', 'ClassicalDedekindReals.sig_not_dec',
    'Events.external_functions_sem', 'Events.external_functions_properties',
    'Events.inline_assembly_sem', 'Events.inline_assembly_properties',
}


def command(work, folder, stem, row, expected):
    path = work / (stem + '.log')
    if (row != dict(command=expected, exit_code=0, log_sha256=s.sha(path.read_bytes())) or
        (folder / path.name).read_bytes() != path.read_bytes()):
        raise ValueError('SHA command/exit/log/archive differs: ' + stem)


def report(work, prefix, modules, results, definitions, expected_deps):
    header = ['Require ' + m + '.' for m in modules]
    axioms = header[:]
    contracts = header + ['Set Printing All.', 'Set Printing Width 120.', 'Set Printing Depth 1000000.']
    for n in results:
        axioms += ['Goal True. idtac "JET_ASSUMPTIONS ' + n + '". exact I. Qed.', 'Print Assumptions ' + n + '.']
        contracts += ['Goal True. idtac "TAP_TYPE ' + n + '". exact I. Qed.', 'Check @' + n + '.']
    for n in definitions:
        contracts += ['Goal True. idtac "TAP_DEF ' + n + '". exact I. Qed.', 'Print ' + n + '.']
    for kind, lines in [('assumptions', axioms), ('contracts', contracts)]:
        path = work / ((prefix + '-' + kind).replace('-', '_') + '.v')
        if path.read_text() != '\n'.join(lines) + '\n':
            raise ValueError('SHA full-report driver differs')
    text = (work / (prefix + '-contracts.log')).read_text()
    if ('...' in text or re.search(r'\?[A-Za-z]', text) or
        re.findall(r'(?m)^TAP_(TYPE|DEF) (\S+)$', text) !=
        [('TYPE', n) for n in results] + [('DEF', n) for n in definitions] or
        s.reports.assumptions((work / (prefix + '-assumptions.log')).read_text()) != expected_deps):
        raise ValueError('SHA full reports/closedness/assumptions differ')


def review(work):
    r, compiled, launch = [json.loads((HERE / name).read_text()) for name in
                            ['CHECKED.json', 'RUN.json', 'KERNEL-RUN.json']]
    if (g.EIGHT != INHERITED or
        g.FOUR != INHERITED - {'Events.external_functions_sem', 'Events.inline_assembly_sem',
                              'Events.external_functions_properties', 'Events.inline_assembly_properties'} or
        r != dict(compiled, commands=r['commands'], recursive_kernel_check=True,
                  kernel_launch_sha256=s.sha((HERE / 'KERNEL-RUN.json').read_bytes())) or
        r['candidate'] != str(work) or r['modules'] != [g.MODULE] or r['new_sources'] != [g.NAME] or
        r['freshly_compiled_support'] != g.SUPPORT or r['definitions'] or r['closed_results'] or
        r['whole_c_endpoints'] != 18 or r['conditional_memcpy_endpoints'] != 17 or
        r['inherited_endpoint_assumptions'] != 8 or r['new_axioms'] != 0 or r['coverage_added'] != 0 or
        any(r[n] is not True for n in ['existing_execution_and_startup_proofs_reused',
                                     'named_original_startup_state', 'actual_initial_memory_exists']) or
        any(r[n] is not False for n in ['canonical_source_review_complete', 'normal_registration', 'full_acceptance'])):
        raise ValueError('SHA completed proof phase/scope/dependency boundary differs')
    expected_launch = dict(candidate=str(work), command=kd.COMMAND,
        compiled_receipt_sha256=s.sha((HERE / 'RUN.json').read_bytes()),
        candidate_input_sha256=r['candidate_input_sha256'], staged_patch_sha256=r['staged_patch_sha256'],
        driver_sha256=s.sha((HERE / 'kernel.py').read_bytes()), recursive_kernel_check=False)
    if (launch != expected_launch or r['base_candidate'] != str(g.BASE) or
        r['base_checked_sha256'] != s.sha(g.RECEIPT.read_bytes()) or
        r['base_review_sha256'] != s.sha((HERE.parent / 'elements-inputs/EVIDENCE-REVIEW.json').read_bytes()) or
        r['main_inputs'] != g.BASE_RECORD['main_inputs'] or
        r['tools_sha256'] != {'check.py': s.sha((HERE / 'check.py').read_bytes())}):
        raise ValueError('SHA actual launch/base/compiler provenance differs')
    results, definitions = g.shared.declarations((work / 'Coq' / g.NAME).read_text(), g.MODULE)
    if (len(results) != 19 or definitions or r['results'] != results or r['endpoints'] != results[1:] or
        results[0] != g.MODULE + '.sha_canonical_startup_nonvacuous'):
        raise ValueError('incomplete SHA public C-target/nonvacuity inventory')
    expected_deps = {n: g.FOUR if n == results[0] else INHERITED for n in results}
    if r['dependencies'] != {n: sorted(ds) for n, ds in expected_deps.items()}:
        raise ValueError('SHA explicit endpoint/nonvacuity assumptions differ')
    all_modules = g.SUPPORT + [g.MODULE]
    for field, suffix in [('source_sha256', '.v'), ('object_sha256', '.vo')]:
        if set(r[field]) != set(all_modules):
            raise ValueError('incomplete fresh SHA support/adapter source/object inventory')
        for m, digest in r[field].items():
            path = work / 'Coq' / (m.replace('.', '/') + suffix)
            if path.is_symlink() or s.sha(path.read_bytes()) != digest:
                raise ValueError('SHA checked source/object differs')
    expected_commands = {m: ['bash', 'build-jets.sh', '--coqc', '-q', m.replace('.', '/') + '.v'] for m in all_modules}
    for kind in ['assumptions', 'contracts']:
        expected_commands['sha-canonical-' + kind] = ['bash', 'build-jets.sh', '--coqc', '-q', str(work / ('sha_canonical_' + kind + '.v'))]
    expected_commands.update(ast=['bash', 'C/check-sha-jets-generation.sh'], kernel=kd.COMMAND)
    if (set(r['commands']) != set(expected_commands) or set(compiled['commands']) != set(expected_commands) - {'ast', 'kernel'}):
        raise ValueError('incomplete SHA actual command inventory')
    for stem, cmd in expected_commands.items():
        command(work, HERE, stem, r['commands'][stem], cmd)
        if stem in compiled['commands'] and compiled['commands'][stem] != r['commands'][stem]:
            raise ValueError('SHA fresh/kernel command phase changed')
    report(work, 'sha-canonical', [g.MODULE], results, [], expected_deps)
    s.kernel.kernel((work / 'kernel.log').read_text(), sorted((work / 'Coq/C/jet_coqchk_axioms.expected').read_text().split()))

    support = json.loads((HERE / 'SUPPORT-REPORT.json').read_text())
    sr, sd = [], []
    for m in g.SUPPORT:
        a, b = g.shared.declarations((work / 'Coq' / (m.replace('.', '/') + '.v')).read_text(), m)
        sr += a
        sd += b
    if ((len(sr), len(sd)) != (104, 15) or support['results'] != sr or support['definitions'] != sd or
        support['modules'] != g.SUPPORT or support['candidate'] != str(work) or
        support['candidate_input_sha256'] != r['candidate_input_sha256'] or
        support['staged_patch_sha256'] != r['staged_patch_sha256'] or
        support['checked_sha256'] != s.sha((HERE / 'CHECKED.json').read_bytes()) or
        support['tool_sha256'] != s.sha((HERE / 'report-support.py').read_bytes()) or
        support['new_axioms'] != 0 or support['full_types_and_definitions'] is not True or
        support['coverage_added'] != 0 or support['normal_registration'] is not False or support['full_acceptance'] is not False or
        any(support[f] != {m: r[f][m] for m in g.SUPPORT} for f in ['source_sha256', 'object_sha256'])):
        raise ValueError('SHA fresh dependency-closure report differs')
    support_deps = {n: set(ds) for n, ds in support['dependencies'].items()}
    if (set(support_deps) != set(sr) or any(not ds <= INHERITED for ds in support_deps.values()) or
        support['closed_results'] != [n for n in sr if not support_deps[n]] or len(support['closed_results']) != 12):
        raise ValueError('SHA support dependency/closedness boundary differs')
    if set(support['commands']) != {'sha-startup-support-assumptions', 'sha-startup-support-contracts'}:
        raise ValueError('incomplete SHA dependency-closure command inventory')
    for stem, row in support['commands'].items():
        command(work, HERE, stem, row, ['bash', 'build-jets.sh', '--coqc', '-q', str(work / (stem.replace('-', '_') + '.v'))])
    report(work, 'sha-startup-support', g.SUPPORT, sr, sd, support_deps)

    source = json.loads((SOURCE / 'SOURCE-REVIEW.json').read_text())
    actual = s.load('sha_canonical_selected_source', SOURCE / 'check-source.py').check(work)
    expected_tools = ['check-source.py', 'test-source.py', 'source-model.py', 'create-model.py', 'finish-source.py']
    if (source['candidate'] != str(work) or source['source_review'] != actual or
        source['candidate_input_sha256'] != r['candidate_input_sha256'] or source['staged_patch_sha256'] != r['staged_patch_sha256'] or
        source['compile_receipt_sha256'] != s.sha((HERE / 'RUN.json').read_bytes()) or
        source['checked_receipt_sha256'] != s.sha((HERE / 'CHECKED.json').read_bytes()) or
        source['kernel_launch_sha256'] != s.sha((HERE / 'KERNEL-RUN.json').read_bytes()) or
        source['tools_sha256'] != {n: s.sha((SOURCE / n).read_bytes()) for n in expected_tools} or
        source['canonical_source_review_complete'] is not True or source['prior_recursive_kernel_evidence_validated'] is not True or
        source['coverage_added'] != 0 or any(source[n] is not False for n in
          ['independent_evidence_review_complete', 'formal_host_library_equivalence', 'normal_registration', 'full_acceptance'])):
        raise ValueError('SHA completed canonical-source review differs')
    source_commands = {'sha-canonical-source': 'check-source.py', 'sha-canonical-negative': 'test-source.py'}
    if set(source['commands']) != set(source_commands):
        raise ValueError('incomplete SHA source command inventory')
    for stem, script in source_commands.items():
        command(work, SOURCE, stem, source['commands'][stem], [sys.executable, '-B', str(SOURCE / script), str(work)])
    if ((actual['selected_endpoints'], actual['explicit_memcpy_endpoints'], actual['public_endpoint_inherited_assumptions']) != (18, 17, 8) or
        not actual['whole_contracts_reviewed'] or not actual['named_startup_state_reviewed'] or
        any(actual[n] is not False for n in ['arbitrary_ready_parameter', 'formal_host_library_equivalence',
             'optimized_dispatch_support', 'assertion_enabled_build_proved', 'normal_registration'])):
        raise ValueError('SHA source-scope or host/runtime boundary differs')
    g.tree(work)
    main = json.loads((HERE.parent / 'scalar-lambda-admission/MAIN-ACCEPTANCE.json').read_text())
    if (history.fingerprint_known_sources(work, r['main_inputs']) != main['audit_input_sha256'] or
        s.inputs.fingerprint(work / 'Coq', work) != r['candidate_input_sha256']):
        raise ValueError('SHA actual historical main/private input bytes differ')
    return dict(candidate=str(work), results=19, definitions=0, support_modules=9,
        support_results=104, support_definitions=15, closed_support_results=12,
        whole_c_endpoints=18, conditional_memcpy_endpoints=17, endpoint_inherited_assumptions=8,
        nonvacuity_inherited_assumptions=4, new_axioms=0, recursive_kernel_check=True,
        canonical_source_review_complete=True, named_original_startup_state=True,
        actual_initial_memory_exists=True, support_public_inventory_reported=True,
        inherited_source_changes=0, formal_host_library_equivalence=False,
        optimized_dispatch_support=False, assertion_enabled_build_proved=False,
        normal_registration=False, coverage_added=0, full_acceptance=False)


def finish(work):
    if (HERE / 'EVIDENCE-REVIEW.json').exists():
        raise ValueError('SHA independent review already recorded; inspect its existing result')
    before, index = s.input_map(), s.index_hash()
    result = review(work)
    check = s.run(work, [sys.executable, '-B', str(HERE / 'test-review.py'), str(work)], 'evidence-tests', 1800)
    if review(work) != result or s.input_map() != before or s.index_hash() != index:
        raise ValueError('SHA independent review changed main/index/source/evidence')
    record = dict(candidate=str(work), review=result, checks={'evidence-tests': check},
        checked_sha256=s.sha((HERE / 'CHECKED.json').read_bytes()),
        compile_sha256=s.sha((HERE / 'RUN.json').read_bytes()),
        kernel_launch_sha256=s.sha((HERE / 'KERNEL-RUN.json').read_bytes()),
        support_report_sha256=s.sha((HERE / 'SUPPORT-REPORT.json').read_bytes()),
        source_review_sha256=s.sha((SOURCE / 'SOURCE-REVIEW.json').read_bytes()),
        tools_sha256={n: s.sha((HERE / n).read_bytes()) for n in ['check.py', 'kernel.py', 'report-support.py', 'review.py', 'test-review.py']},
        candidate_input_sha256=s.inputs.fingerprint(work / 'Coq', work), staged_patch_sha256=index,
        independent_evidence_review_complete=True, normal_registration=False, coverage_added=0, full_acceptance=False)
    s.changed({HERE / 'EVIDENCE-REVIEW.json': json.dumps(record, indent=2) + '\n',
        HERE / 'evidence-tests.log': (work / 'evidence-tests.log').read_text()})
    print('SHA C/startup/nonvacuity/support/kernel/source evidence independently reviewed; normal admission remains', flush=True)


if __name__ == '__main__':
    if len(sys.argv) != 3 or sys.argv[1] not in ['review', 'finish']:
        raise ValueError('usage: review.py review|finish COMPLETED_SHA_TREE')
    work = Path(sys.argv[2]).resolve()
    if sys.argv[1] == 'finish':
        finish(work)
    else:
        print(json.dumps(review(work), indent=2))
