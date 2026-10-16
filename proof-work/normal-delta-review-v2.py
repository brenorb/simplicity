"""Read-only normal delta review, with explicit historical checkpoint resolution.

Preserve inherited declarations, types, definitions and dependency sets; bind
new full reports, sources, fresh objects and command exits. This does not run
acceptance, install sources, or mutate a predecessor reviewer's globals.
"""
import json
import re


def review(g, work):
    s, normal = g.s, g.normal
    g.boundaries()
    meta = json.loads((work / 'ASSEMBLY.json').read_text())
    r = json.loads((work / 'PREPARATION.json').read_text())
    if (meta['candidate'] != str(work) or r['candidate'] != str(work) or
        meta['predecessor_candidate'] != str(g.BASE_TREE) or
        meta['predecessor_input_sha256'] != g.PRED_REVIEW['candidate_input_sha256'] or
        meta['predecessor_review_sha256'] != s.sha((g.PRED / 'REVIEW.json').read_bytes()) or
        meta['proof_checked_sha256'] != s.sha((g.PROOF / 'CHECKED.json').read_bytes()) or
        meta['proof_review_sha256'] != s.sha((g.PROOF / 'EVIDENCE-REVIEW.json').read_bytes()) or
        meta['preparation_engine_sha256'] != s.sha(g.PREPARE_ENGINE.read_bytes()) or
        meta['extensions'] != g.additions() or meta['coverage_additions'] != g.COVERAGE or
        meta['new_sources'] != g.NEW_SOURCES or meta['baseline_inputs'] != g.baseline_inputs() or
        any(x['coverage_added'] != g.COVERAGE_ADDED or x['full_acceptance'] is not False for x in [meta, r])):
        raise ValueError('wrong predecessor/proof/engine/registration scope')
    # The batch resolver must reject every unrecognized exact input map. This
    # supports additional real historical checkpoints, not arbitrary drift.
    main_fp = g.main_fingerprint(meta['main_inputs'])
    if meta['main_input_sha256'] != main_fp or meta['staged_patch_sha256'] != g.PR['staged_patch_sha256']:
        raise ValueError('historical main/index identity differs')
    coq = work / 'Coq'
    paths = g.load('normal_delta_inventory', g.HERE.parent / 'elements-pegin-normal/review.py').source_paths
    if paths(coq) != paths(g.BASE) | set(g.NEW_SOURCES + g.GUARDS):
        raise ValueError('unexpected source/metadata inventory')
    for name, digest in g.baseline_inputs().items():
        if name.startswith('Coq/') and name[4:] not in g.METADATA + g.SCRIPTS:
            if s.sha((work / name).read_bytes()) != digest:
                raise ValueError('inherited source changed: ' + name)
    expected_meta = {n: s.sha((g.BASE / n).read_bytes()) for n in g.METADATA + g.SCRIPTS}
    if meta['baseline_metadata_sha256'] != expected_meta:
        raise ValueError('predecessor metadata binding differs')
    for m in g.MODULES:
        n = m.replace('.', '/') + '.v'
        if (coq / n).read_bytes() != (g.PROOF_TREE / 'Coq' / n).read_bytes():
            raise ValueError('normal source differs from kernel-checked proof')
    for n, rows in g.additions().items():
        if (coq / n).read_text() != (g.BASE / n).read_text() + '\n'.join(rows) + '\n':
            raise ValueError('public inventory is not exact append')
    if (coq / 'C/jet_coverage.tsv').read_text() != (g.BASE / 'C/jet_coverage.tsv').read_text() + g.COVERAGE:
        raise ValueError('coverage is not exactly the reviewed whole-C delta')
    for n in g.GUARDS:
        if (coq / n).read_bytes() != (g.HERE.parent / n).read_bytes():
            raise ValueError('deployed source guard differs')
    for n, text in g.script_changes().items():
        if (coq / n).read_text() != text:
            raise ValueError('unreviewed gate/printer/coverage script change')
    old_r, old_d = [normal.rows(g.BASE / 'C' / n) for n in ['jet_public_theorems.txt', 'jet_contract_definitions.txt']]
    new_r, new_d = [normal.rows(coq / 'C' / n) for n in ['jet_public_theorems.txt', 'jet_contract_definitions.txt']]
    if new_r[:len(old_r)] != old_r or new_d[:len(old_d)] != old_d:
        raise ValueError('inherited declaration order changed')
    old = normal.contract_records((g.BASE / 'C/jet_contracts.expected').read_text(), old_r, old_d)
    new = normal.contract_records((coq / 'C/jet_contracts.expected').read_text(), new_r, new_d)
    old_keys = {k for k, _ in old}
    if [(k, t) for k, t in new if k in old_keys] != old:
        raise ValueError('inherited contract bytes/order changed')
    added = [(k, t) for k, t in new if k not in old_keys]
    wanted = [('TYPE', m, n, 1) for m, n in new_r[len(old_r):]] + [('DEF', m, n, 1) for m, n in new_d[len(old_d):]]
    if [k for k, _ in added] != wanted or len(added) != g.NEW_RESULTS + g.NEW_DEFINITIONS:
        raise ValueError('wrong new-type/definition snapshot delta')
    text = (work / 'new_contracts.log').read_text()
    report = text[text.index('DELTA_DEEP_'):]
    marks = list(re.finditer(r'(?m)^DELTA_DEEP_(TYPE|DEF) (\S+)\n', report))
    if [(m[1], m[2]) for m in marks] != [(k, m + '.' + n) for k, m, n, _ in wanted]:
        raise ValueError('incomplete/reordered deep report')
    supplements = []
    for i, ((_, module, name, _), compact) in enumerate(added):
        deep = report[marks[i].end():marks[i+1].start() if i+1 < len(marks) else len(report)]
        if '...' in deep or re.search(r'\?[A-Za-z]', deep):
            raise ValueError('truncated/unquantified deep record')
        short, long = re.sub(r'\s+', '', compact), re.sub(r'\s+', '', deep)
        if short == long:
            continue
        pos, fragments = 0, short.split('...')
        for j, fragment in enumerate(fragments):
            at = len(long)-len(fragment) if j == len(fragments)-1 and long.endswith(fragment) else long.find(fragment, pos)
            if at < pos or j == 0 and at != 0:
                raise ValueError('compact/deep record disagrees')
            pos = at + len(fragment)
        if '...' not in short or pos != len(long):
            raise ValueError('unexplained compact/deep difference')
        supplements.append(module + '.' + name)
    old_deps = g.snapshot_deps((g.BASE / 'C/jet_assumptions.expected').read_text())
    new_deps = g.snapshot_deps((coq / 'C/jet_assumptions.expected').read_text())
    if {n: new_deps.get(n) for n in old_deps} != old_deps:
        raise ValueError('inherited dependency sets changed')
    fresh = normal.assumptions((work / 'new_assumptions.log').read_text())
    fresh_sorted = {n: sorted(ds) for n, ds in fresh.items()}
    if (set(fresh) != {m + '.' + n for m, n in new_r[len(old_r):]} or r['new_dependencies'] != fresh_sorted or
        {n: ds for n, ds in new_deps.items() if n not in old_deps} != fresh_sorted or
        any(not ds <= s.SIX or sorted(ds) != g.PR['dependencies'][n] for n, ds in fresh.items())):
        raise ValueError('normal assumptions differ from checked proof closure')
    if (any(fresh[n] for n in g.CLOSED_RESULTS) or any(fresh[n] != s.SIX for n in g.ENDPOINTS)):
        raise ValueError('closed bridges or C endpoint assumptions differ')
    if set(r['fresh_compiles']) != set(g.MODULES):
        raise ValueError('incomplete fresh module inventory')
    commands = [(r['build'], ['bash', 'build-jets.sh', '-j2'], 'build')]
    for name in ['contracts', 'assumptions']:
        commands.append((r[name], ['bash', 'build-jets.sh', '--coqc', '-q', str(work / ('new_' + name + '.v'))], 'new_' + name))
    sources, objects = {}, {}
    for m in g.MODULES:
        commands.append((r['fresh_compiles'][m], ['bash', 'build-jets.sh', '--coqc', '-q', m.replace('.', '/') + '.v'], 'fresh-' + m))
        path = coq / (m.replace('.', '/') + '.v')
        if path.is_symlink() or path.with_suffix('.vo').is_symlink():
            raise ValueError('shared mutable proof source/object')
        sources[m], objects[m] = s.sha(path.read_bytes()), s.sha(path.with_suffix('.vo').read_bytes())
    if meta['source_sha256'] != sources or r['new_objects_sha256'] != objects:
        raise ValueError('fresh source/object evidence changed')
    for row, command, stem in commands:
        if row['command'] != command or row['exit_code'] != 0 or row['log_sha256'] != s.sha((work / (stem + '.log')).read_bytes()):
            raise ValueError('wrong build/check command/flags/exit/log')
    g.load('normal_delta_source_guard', g.PROOF / 'check-source.py').check(work)
    return dict(candidate=str(work), coverage_added=g.COVERAGE_ADDED,
        new_results=g.NEW_RESULTS, new_definitions=g.NEW_DEFINITIONS,
        inherited_contracts_byte_identical=len(old), inherited_dependencies_unchanged=len(old_deps),
        untruncated_new_records=len(added), compact_deep_supplements=supplements,
        closed_shared_lemmas=len(g.CLOSED_RESULTS), inherited_proof_changes=0,
        main_index_preserved=True, predecessor_terminal_acceptance_required=True,
        full_acceptance=False, **g.SCOPE_FIELDS)
