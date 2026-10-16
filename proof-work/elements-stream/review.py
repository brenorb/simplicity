"""Independent proof/kernel/source review of seven Elements stream getters.

The earlier Reader-only phase and the later two-module phase are checked
separately; adding the endpoint module does not rewrite the earlier receipt.
"""
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('elements_stream_checked', HERE / 'check.py')
g = importlib.util.module_from_spec(sp)
sp.loader.exec_module(g)
s = g.s
SOURCE = HERE.parent / 'elements-stream-source'
RM, EM = g.MODULES
CLOSED = [RM + '.hr_iden', RM + '.hr_unit'] + [EM + '.' + n for n in [
    'elements_prim_words_hash_spec_parametric', 'elements_hash_words_bound_32',
    'elements_hash_words_bound_4', 'elements_hash_words_bound_path',
    'elements_output_scripts_words_sem', 'elements_output_range_proofs_words_sem',
    'elements_output_surjection_proofs_words_sem', 'elements_input_scripts_words_sem',
    'elements_input_sequences_words_sem', 'elements_input_script_sigs_words_sem',
    'elements_tappath_words_sem']]
FUNEXT = [RM + '.' + n for n in [
    'hr_comp', 'hr_pair', 'hr_take', 'hr_drop', 'hr_case', 'hr_injl', 'hr_injr',
    'hr_copair_iden', 'hr_assert', 'hr_core', 'hash_loop_body_reader_sem',
    'hash_loop_reader_sem', 'hash_words_reader_sem']]
FUNEXT += [EM + '.elements_hash_prim', EM + '.elements_prim_words_hash_spec_sem']
EXECUTION = g.ENDPOINTS + [EM + '.elements_tx_words_hash_jet']


def fingerprint_known_sources(work, expected):
    """Reconstruct a historical source phase from checked present file bytes.

    Use the audit's exact group/path ordering and length-prefixed serialization.
    Unknown/missing keys cannot be discarded to make a previous phase pass.
    """
    digest, seen = hashlib.sha256(), set()
    for label in ['Coq', 'C', 'Haskell']:
        prefix = label + '/'
        names = sorted((Path(n[len(prefix):]) for n in expected if n.startswith(prefix)))
        for relative in names:
            name = prefix + str(relative)
            raw = (work / label / relative).read_bytes()
            if s.sha(raw) != expected[name]:
                raise ValueError('historical stream source bytes differ: ' + name)
            for part in [name.encode(), raw]:
                digest.update(len(part).to_bytes(8, 'big'))
                digest.update(part)
            seen.add(name)
    if seen != set(expected):
        raise ValueError('unknown historical stream source group')
    return digest.hexdigest()


def report(work, prefix, modules, results, definitions, expected_deps):
    header = ['Require ' + ' '.join(modules) + '.']
    axioms = header[:]
    contracts = header + ['Set Printing All.', 'Set Printing Width 120.', 'Set Printing Depth 1000000.']
    for name in results:
        axioms += ['Goal True. idtac "JET_ASSUMPTIONS ' + name + '". exact I. Qed.',
                   'Print Assumptions ' + name + '.']
    for kind, names in [('TYPE', results), ('DEF', definitions)]:
        for name in names:
            contracts += ['Goal True. idtac "TAP_' + kind + ' ' + name + '". exact I. Qed.',
                          ('Check @' if kind == 'TYPE' else 'Print ') + name + '.']
    for kind, lines in [('assumptions', axioms), ('contracts', contracts)]:
        if (work / ((prefix + '-' + kind).replace('-', '_') + '.v')).read_text() != '\n'.join(lines) + '\n':
            raise ValueError('Elements stream reporting driver differs')
    text = (work / (prefix + '-contracts.log')).read_text()
    if ('...' in text or re.search(r'\?[A-Za-z]', text) or
        re.findall(r'(?m)^TAP_(TYPE|DEF) (\S+)$', text) !=
        [('TYPE', n) for n in results] + [('DEF', n) for n in definitions]):
        raise ValueError('incomplete full Elements stream type/definition report')
    deps = s.reports.assumptions((work / (prefix + '-assumptions.log')).read_text())
    if deps != expected_deps:
        raise ValueError('Elements stream closedness/assumptions differ')
    return {n: sorted(ds) for n, ds in deps.items()}


def source_review(work):
    r = json.loads((SOURCE / 'SOURCE-REVIEW.json').read_text())
    actual = s.load('reviewed_elements_stream_source', SOURCE / 'check-source.py').check(work)
    files = ['check-source.py', 'test-source.py', 'source-model.py', 'finish-source.py']
    if (r['candidate'] != str(work) or r['source_review'] != actual or
        r['compile_receipt_sha256'] != s.sha((HERE / 'RUN.json').read_bytes()) or
        r['candidate_input_sha256'] != s.inputs.fingerprint(work / 'Coq', work) or
        r['staged_patch_sha256'] != s.index_hash() or
        r['canonical_source_review_complete'] is not True or
        r['recursive_kernel_result_checked_by_this_tool'] is not False or
        r['normal_registration'] is not False or r['full_acceptance'] is not False or r['coverage_added'] != 0 or
        r['tools_sha256'] != {n: s.sha((SOURCE / n).read_bytes()) for n in files}):
        raise ValueError('completed selected Elements stream source review differs')
    if (actual['canonical_stream_source_review_complete'] is not True or
        actual['whole_contracts_reviewed'] is not True or actual['original_c_getters'] != 7 or
        any(actual[n] is not False for n in ['caller_cached_hashes_established',
            'formal_host_lens_equivalence', 'formal_host_crypto_equivalence', 'normal_registration'])):
        raise ValueError('Elements stream canonical/caller boundary differs')
    expected = {'stream-source': 'check-source.py', 'stream-source-negative': 'test-source.py'}
    if set(r['commands']) != set(expected):
        raise ValueError('incomplete selected Elements source command inventory')
    for stem, script in expected.items():
        row, log = r['commands'][stem], work / (stem + '.log')
        if (row['command'] != [sys.executable, '-B', str(SOURCE / script), str(work)] or
            row['exit_code'] != 0 or row['log_sha256'] != s.sha(log.read_bytes()) or
            (SOURCE / log.name).read_bytes() != log.read_bytes()):
            raise ValueError('Elements stream source command/exit/log differs')
    return r


def review(work):
    r = json.loads((HERE / 'CHECKED.json').read_text())
    compiled = json.loads((HERE / 'RUN.json').read_text())
    launch = json.loads((HERE / 'KERNEL-RUN.json').read_text())
    rd = json.loads((HERE / 'READER-CHECKED.json').read_text())
    if (r['modules'] != g.MODULES or r['fresh_modules'] != g.FRESH or r['new_sources'] != g.NEW or
        r['endpoints'] != g.ENDPOINTS or r['closed_results'] != CLOSED or r['whole_c_endpoints'] != 7 or
        r['literal_programs_over_raw_elements_data'] is not True or r['recursive_kernel_check'] is not True or
        compiled['recursive_kernel_check'] is not False or r['coverage_added'] != 0 or
        any(r[n] is not False for n in ['caller_cached_hashes_established',
            'canonical_family_source_review_complete', 'normal_registration', 'full_acceptance'])):
        raise ValueError('wrong Elements stream proof/admission scope')
    for name, value in compiled.items():
        if name not in ['commands', 'recursive_kernel_check'] and r[name] != value:
            raise ValueError('Elements stream compile/terminal identity differs')
    expected_launch = dict(candidate=str(work), command=g.KERNEL,
        compiled_receipt_sha256=s.sha((HERE / 'RUN.json').read_bytes()),
        candidate_input_sha256=r['candidate_input_sha256'], main_inputs_at_kernel=r['main_inputs_at_kernel'],
        staged_patch_sha256=r['staged_patch_sha256'], recursive_kernel_check=False)
    if launch != expected_launch or r['kernel_launch_sha256'] != s.sha((HERE / 'KERNEL-RUN.json').read_bytes()):
        raise ValueError('Elements stream once-only kernel launch differs')
    if (r['candidate'] != str(work) or r['staged_patch_sha256'] != s.index_hash() or
        r['tools_sha256'] != {'check.py': s.sha((HERE / 'check.py').read_bytes())} or
        r['reader_checkpoint_sha256'] != s.sha((HERE / 'READER-CHECKED.json').read_bytes()) or
        rd['main_inputs'] != r['main_inputs_at_compile'] or
        r['main_inputs_at_kernel'] != r['main_inputs_at_compile']):
        raise ValueError('Elements stream candidate/index/checker/phase identity differs')
    results, definitions = [], []
    for module, name in zip(g.MODULES, g.NEW):
        a, b = g.shared.declarations((work / 'Coq' / name).read_text(), module)
        results += a
        definitions += b
    if ((len(results), len(definitions)) != (36, 10) or r['results'] != results or
        r['definitions'] != definitions or set(results) != set(CLOSED + FUNEXT + EXECUTION)):
        raise ValueError('wrong complete Elements stream declaration inventory')
    for field, suffix in [('source_sha256', '.v'), ('object_sha256', '.vo')]:
        if set(r[field]) != set(g.FRESH):
            raise ValueError('incomplete Elements stream fresh source/object inventory')
        for module, digest in r[field].items():
            path = work / 'Coq' / (module.replace('.', '/') + suffix)
            if path.is_symlink() or s.sha(path.read_bytes()) != digest:
                raise ValueError('fresh Elements stream source/object differs')
    commands = {m: ['bash', 'build-jets.sh', '--coqc', '-q', m.replace('.', '/') + '.v'] for m in g.FRESH}
    for name in ['assumptions', 'contracts']:
        commands['elements-stream-' + name] = ['bash', 'build-jets.sh', '--coqc', '-q',
                                             str(work / ('elements_stream_' + name + '.v'))]
    commands.update(ast=['bash', 'C/check-elements-jets-generation.sh'], kernel=g.KERNEL)
    if set(r['commands']) != set(commands) or set(compiled['commands']) != set(commands) - {'ast', 'kernel'}:
        raise ValueError('incomplete Elements stream command inventory')
    for name, command in commands.items():
        row, log = r['commands'][name], work / (name + '.log')
        if (row['command'] != command or row['exit_code'] != 0 or row['log_sha256'] != s.sha(log.read_bytes()) or
            (HERE / log.name).read_bytes() != log.read_bytes() or
            name in compiled['commands'] and compiled['commands'][name] != row):
            raise ValueError('Elements stream terminal command/exit/log differs')
    expected = {n: set() for n in CLOSED}
    expected.update({n: {'FunctionalExtensionality.functional_extensionality_dep'} for n in FUNEXT})
    expected.update({n: s.SIX for n in EXECUTION})
    if r['dependencies'] != report(work, 'elements-stream', g.MODULES, results, definitions, expected):
        raise ValueError('reported Elements stream dependencies differ')
    reader_results = [n for n in results if n.startswith(RM + '.')]
    reader_definitions = [n for n in definitions if n.startswith(RM + '.')]
    if (rd['module'] != RM or rd['new_source'] != g.reader.NAME or rd['results'] != reader_results or
        rd['definitions'] != reader_definitions or rd['closed_results'] != CLOSED[:2] or
        rd['source_sha256'] != r['source_sha256'][RM] or rd['object_sha256'] != r['object_sha256'][RM] or
        rd['base_acceptance_sha256'] != r['base_acceptance_sha256'] or
        rd['whole_c_endpoints'] != 0 or rd['any_environment_type'] is not True or
        rd['existing_pure_traversal_reused'] is not True or rd['coverage_added'] != 0 or
        any(rd[n] is not False for n in ['recursive_kernel_check', 'normal_registration', 'full_acceptance'])):
        raise ValueError('original Reader-only checkpoint differs')
    reader_commands = {RM: commands[RM]}
    for name in ['assumptions', 'contracts']:
        reader_commands['elements-reader-' + name] = ['bash', 'build-jets.sh', '--coqc', '-q',
                                                     str(work / ('elements_reader_' + name + '.v'))]
    if set(rd['commands']) != set(reader_commands):
        raise ValueError('incomplete original Reader command inventory')
    for name, command in reader_commands.items():
        row, log = rd['commands'][name], work / (name + '.log')
        if (row['command'] != command or row['exit_code'] != 0 or row['log_sha256'] != s.sha(log.read_bytes()) or
            (HERE / log.name).read_bytes() != log.read_bytes()):
            raise ValueError('original Reader command/exit/log differs')
    if rd['dependencies'] != report(work, 'elements-reader', [RM], reader_results, reader_definitions,
                                   {n: expected[n] for n in reader_results}):
        raise ValueError('original Reader complete reports differ')
    # The original phase has the base plus one source; the later phase adds
    # the endpoint source. Verify both historical fingerprints from actual
    # immutable bytes, without changing files or faking a filesystem view.
    if fingerprint_known_sources(work, rd['main_inputs']) != rd['base_input_sha256']:
        raise ValueError('original Reader baseline source map differs')
    old = dict(rd['main_inputs'])
    old['Coq/' + g.reader.NAME] = rd['source_sha256']
    if fingerprint_known_sources(work, old) != rd['candidate_input_sha256']:
        raise ValueError('original Reader-only source fingerprint differs')
    s.kernel.kernel((work / 'kernel.log').read_text(), sorted((work / 'Coq/C/jet_coqchk_axioms.expected').read_text().split()))
    source_review(work)
    base, _ = g.tree(work)
    if (r['base_candidate'] != str(base) or r['base_acceptance_sha256'] != s.sha(g.reader.BASE_RECEIPT.read_bytes()) or
        r['candidate_input_sha256'] != s.inputs.fingerprint(work / 'Coq', work)):
        raise ValueError('Elements stream immutable proof/base source differs')
    return dict(candidate=str(work), results=36, definitions=10, closed_results=13,
        pure_funext_results=15, whole_c_endpoints=7, endpoint_inherited_assumptions=6,
        recursive_kernel_check=True, inherited_source_changes=0,
        canonical_stream_source_review_complete=True, original_reader_phase_verified=True,
        caller_cached_hashes_established=False, formal_host_library_equivalence=False,
        normal_registration=False, coverage_added=0, full_acceptance=False)


def finish(work):
    if (HERE / 'EVIDENCE-REVIEW.json').exists():
        raise ValueError('Elements stream proof review already recorded; inspect existing evidence')
    before, index = s.input_map(), s.index_hash()
    result = review(work)
    row = s.run(work, [sys.executable, '-B', str(HERE / 'test-review.py'), str(work)], 'evidence-tests', 900)
    if review(work) != result or s.input_map() != before or s.index_hash() != index:
        raise ValueError('Elements stream evidence/source/main/index changed during review')
    record = dict(review=result, checked_sha256=s.sha((HERE / 'CHECKED.json').read_bytes()),
        compile_sha256=s.sha((HERE / 'RUN.json').read_bytes()),
        reader_checkpoint_sha256=s.sha((HERE / 'READER-CHECKED.json').read_bytes()),
        kernel_launch_sha256=s.sha((HERE / 'KERNEL-RUN.json').read_bytes()),
        source_review_sha256=s.sha((SOURCE / 'SOURCE-REVIEW.json').read_bytes()),
        checks={'evidence-tests': row}, candidate_input_sha256=s.inputs.fingerprint(work / 'Coq', work),
        tools_sha256={n: s.sha((HERE / n).read_bytes()) for n in ['check-reader.py', 'check.py', 'review.py', 'test-review.py']},
        source_review_complete=True, normal_registration=False, full_acceptance=False)
    s.changed({HERE / 'EVIDENCE-REVIEW.json': json.dumps(record, indent=2) + '\n',
               HERE / 'evidence-tests.log': (work / 'evidence-tests.log').read_text()})
    print('Seven Elements C hash-word proofs/source/kernel evidence independently reviewed; normal admission remains', flush=True)


if __name__ == '__main__':
    if len(sys.argv) == 2:
        print(json.dumps(review(Path(sys.argv[1]).resolve()), indent=2))
    elif len(sys.argv) == 3 and sys.argv[1] == 'finish':
        finish(Path(sys.argv[2]).resolve())
    else:
        raise ValueError('usage: review.py [finish] PRIVATE_TREE')
