"""Independent raw-program proof/source/object/type/command/kernel review.

Compilation, kernel checking, canonical source review, normal registration
and full acceptance are distinct checkpoints. This reviewer admits none of
the last two and never rebuilds or changes the checked private sources.
"""
import importlib.util
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('raw_program_checked', HERE / 'check.py')
g = importlib.util.module_from_spec(sp)
sp.loader.exec_module(g)
s = g.s
SOURCE = HERE.parent / 'bitcoin-raw-program-source'
PURE_CLOSED = [g.MODULES[0] + '.raw_full_projection',
               g.MODULES[1] + '.tapleaf_hash_literal_parametric']
PURE_FUNEXT = [g.MODULES[0] + '.' + n for n in [
    'raw_core_relation_class', 'raw_assertion_relation_class',
    'raw_program_relation_class', 'bitcoin_program_raw_projection']]


def review(work):
    r = json.loads((HERE / 'CHECKED.json').read_text())
    compiled = json.loads((HERE / 'RUN.json').read_text())
    launch = json.loads((HERE / 'KERNEL-RUN.json').read_text())
    if (r['modules'] != g.MODULES or r['fresh_modules'] != g.FRESH or r['new_sources'] != g.NEW or
        r['endpoints'] != g.ENDPOINTS or r['closed_results'] != PURE_CLOSED or
        r['whole_c_endpoints'] != 16 or r['raw_data_interpretation'] is not True or
        r['recursive_kernel_check'] is not True or compiled['recursive_kernel_check'] is not False or
        r['coverage_added'] != 0 or any(r[n] is not False for n in [
            'all_caller_setup_proved', 'canonical_family_source_review_complete',
            'normal_registration', 'full_acceptance'])):
        raise ValueError('wrong raw-program proof/admission scope')
    for name, value in compiled.items():
        if name not in ['commands', 'recursive_kernel_check'] and r[name] != value:
            raise ValueError('raw-program compile/terminal identity differs')
    expected_launch = dict(candidate=str(work), command=g.KERNEL,
        compiled_receipt_sha256=s.sha((HERE / 'RUN.json').read_bytes()),
        candidate_input_sha256=r['candidate_input_sha256'],
        main_inputs_at_kernel=r['main_inputs_at_kernel'],
        staged_patch_sha256=r['staged_patch_sha256'], recursive_kernel_check=False)
    if launch != expected_launch or r['kernel_launch_sha256'] != s.sha((HERE / 'KERNEL-RUN.json').read_bytes()):
        raise ValueError('raw-program once-only kernel launch differs')
    if (r['candidate'] != str(work) or r['staged_patch_sha256'] != s.index_hash() or
        r['tools_sha256'] != {'check.py': s.sha((HERE / 'check.py').read_bytes())}):
        raise ValueError('raw-program candidate/index/checker identity differs')
    results, definitions = [], []
    for m, name in zip(g.MODULES, g.NEW):
        a, b = g.shared.declarations((work / 'Coq' / name).read_text(), m)
        results += a
        definitions += b
    generic = g.MODULES[0] + '.application_raw_program_local_spec_sep'
    if (r['results'] != results or r['definitions'] != definitions or
        (len(results), len(definitions)) != (23, 4) or
        set(results) != set(PURE_CLOSED + PURE_FUNEXT + [generic] + g.ENDPOINTS)):
        raise ValueError('wrong complete raw-program declaration inventory')
    for field, suffix in [('source_sha256', '.v'), ('object_sha256', '.vo')]:
        if set(r[field]) != set(g.FRESH):
            raise ValueError('incomplete raw-program fresh source/object inventory')
        for m, digest in r[field].items():
            p = work / 'Coq' / (m.replace('.', '/') + suffix)
            if p.is_symlink() or s.sha(p.read_bytes()) != digest:
                raise ValueError('fresh raw-program source/object differs')
    commands = {m: ['bash', 'build-jets.sh', '--coqc', '-q', m.replace('.', '/') + '.v'] for m in g.FRESH}
    for n in ['assumptions', 'contracts']:
        commands['raw-program-' + n] = ['bash', 'build-jets.sh', '--coqc', '-q',
                                      str(work / ('raw_program_' + n + '.v'))]
    commands.update(ast=['bash', 'C/check-bitcoin-jets-generation.sh'], kernel=g.KERNEL)
    if set(r['commands']) != set(commands) or set(compiled['commands']) != set(commands) - {'ast', 'kernel'}:
        raise ValueError('incomplete raw-program command inventory')
    for n, command in commands.items():
        row, log = r['commands'][n], work / (n + '.log')
        if (row['command'] != command or row['exit_code'] != 0 or
            row['log_sha256'] != s.sha(log.read_bytes()) or
            (HERE / log.name).read_bytes() != log.read_bytes() or
            n in compiled['commands'] and compiled['commands'][n] != row):
            raise ValueError('raw-program terminal command/exit/log differs')
    # Independently reconstruct the exact reporting drivers, including every
    # declaration, rather than trusting a receipt's declared inventory.
    header = ['Require ' + ' '.join(g.MODULES) + '.']
    axioms = header[:]
    contracts = header + ['Set Printing All.', 'Set Printing Width 120.', 'Set Printing Depth 1000000.']
    for n in results:
        axioms += ['Goal True. idtac "JET_ASSUMPTIONS ' + n + '". exact I. Qed.', 'Print Assumptions ' + n + '.']
    for kind, names in [('TYPE', results), ('DEF', definitions)]:
        for n in names:
            contracts += ['Goal True. idtac "TAP_' + kind + ' ' + n + '". exact I. Qed.',
                          ('Check @' if kind == 'TYPE' else 'Print ') + n + '.']
    for stem, lines in [('assumptions', axioms), ('contracts', contracts)]:
        if (work / ('raw_program_' + stem + '.v')).read_text() != '\n'.join(lines) + '\n':
            raise ValueError('raw-program reporting driver differs')
    report = (work / 'raw-program-contracts.log').read_text()
    if ('...' in report or re.search(r'\?[A-Za-z]', report) or
        re.findall(r'(?m)^TAP_(TYPE|DEF) (\S+)$', report) !=
        [('TYPE', n) for n in results] + [('DEF', n) for n in definitions]):
        raise ValueError('incomplete full raw-program type/definition reports')
    deps = s.reports.assumptions((work / 'raw-program-assumptions.log').read_text())
    expected = {n: set() for n in PURE_CLOSED}
    expected.update({n: {'FunctionalExtensionality.functional_extensionality_dep'} for n in PURE_FUNEXT})
    expected.update({n: s.SIX for n in [generic] + g.ENDPOINTS})
    if deps != expected or r['dependencies'] != {n: sorted(ds) for n, ds in deps.items()}:
        raise ValueError('raw-program closedness/assumptions differ')
    s.kernel.kernel((work / 'kernel.log').read_text(), sorted((work / 'Coq/C/jet_coqchk_axioms.expected').read_text().split()))
    source = s.load('raw_program_canonical_source', SOURCE / 'check-source.py').check(work)
    if (source['canonical_raw_program_source_review_complete'] is not True or
        source['whole_contracts_reviewed'] is not True or source['original_c_getters'] != 16 or
        any(source[n] is not False for n in ['caller_environment_construction_proved',
            'formal_host_library_equivalence', 'normal_registration'])):
        raise ValueError('raw-program canonical/caller source-review scope differs')
    base, prior = g.tree(work)
    if (r['base_candidate'] != str(base) or
        r['base_receipt_sha256'] != s.sha(g.BASE_RECEIPT.read_bytes()) or
        r['candidate_input_sha256'] != s.inputs.fingerprint(work / 'Coq', work) or
        r['base_input_sha256'] != prior['candidate_input_sha256']):
        raise ValueError('raw-program immutable source/base checkpoint differs')
    return dict(candidate=str(work), results=23, definitions=4, closed_results=2,
        pure_funext_results=4, whole_c_endpoints=16, endpoint_inherited_assumptions=6,
        recursive_kernel_check=True, inherited_source_changes=0,
        canonical_raw_program_source_review_complete=True,
        caller_environment_construction_proved=False, formal_host_library_equivalence=False,
        normal_registration=False, coverage_added=0, full_acceptance=False)


def finish(work):
    if (HERE / 'EVIDENCE-REVIEW.json').exists():
        raise ValueError('raw-program review already recorded; inspect existing receipt')
    before, index = s.input_map(), s.index_hash()
    result, commands = review(work), {}
    for stem, command in [
        ('raw-family-source', [sys.executable, '-B', str(SOURCE / 'check-source.py'), str(work)]),
        ('raw-family-negative', [sys.executable, '-B', str(SOURCE / 'test-source.py'), str(work)]),
        ('raw-evidence-tests', [sys.executable, '-B', str(HERE / 'test-review.py'), str(work)]),
    ]:
        commands[stem] = s.run(work, command, stem, 600)
        print('Passed ' + stem, flush=True)
    if review(work) != result or s.input_map() != before or s.index_hash() != index:
        raise ValueError('raw-program evidence/source/main/index changed during review')
    files = [HERE / n for n in ['check.py', 'review.py', 'test-review.py']]
    files += [SOURCE / n for n in ['check-source.py', 'source-model.py', 'test-source.py']]
    record = dict(review=result, checked_sha256=s.sha((HERE / 'CHECKED.json').read_bytes()),
        compile_sha256=s.sha((HERE / 'RUN.json').read_bytes()),
        kernel_launch_sha256=s.sha((HERE / 'KERNEL-RUN.json').read_bytes()), commands=commands,
        candidate_input_sha256=s.inputs.fingerprint(work / 'Coq', work),
        tools_sha256={str(p.relative_to(HERE.parent)): s.sha(p.read_bytes()) for p in files},
        canonical_source_gate_complete=True, normal_registration=False, full_acceptance=False)
    s.changed({HERE / 'EVIDENCE-REVIEW.json': json.dumps(record, indent=2) + '\n',
        **{HERE / (n + '.log'): (work / (n + '.log')).read_text() for n in commands}})
    print('Sixteen raw Bitcoin C hash-program proofs independently reviewed; normal registration remains', flush=True)


if __name__ == '__main__':
    if len(sys.argv) == 2:
        print(json.dumps(review(Path(sys.argv[1]).resolve()), indent=2))
    elif len(sys.argv) == 3 and sys.argv[1] == 'finish':
        finish(Path(sys.argv[2]).resolve())
    else:
        raise ValueError('usage: review.py [finish] PRIVATE_TREE')
