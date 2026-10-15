"""Prepare two checked tap getters over the fingerprint-bound 399 predecessor.

The predecessor may still be auditing: copy its source text only. Compiler
objects come exclusively from the completed, separately checked tap proof tree.
Preparation generates review material; it does not accept or install proofs.
"""
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
REPO, MAIN = HERE.parents[1], HERE.parents[1] / 'Coq'


def load(name, path):
    sp = importlib.util.spec_from_file_location(name, path)
    m = importlib.util.module_from_spec(sp)
    sp.loader.exec_module(m)
    return m


parent = load('tap_normal_predecessor', HERE.parent / 'elements-thirteen-getters-admission/admission.py')
s, normal, snapshot_deps = parent.support, parent.normal, parent.snapshot_deps
PRED, PROOF = HERE.parent / 'elements-thirteen-getters-admission', HERE.parent / 'elements-tap-getters'
PR = json.loads((PROOF / 'PREPARATION.json').read_text())
PRED_META = json.loads((PRED / 'ASSEMBLY.json').read_text())
PRED_REVIEW = json.loads((PRED / 'REVIEW.json').read_text())
BASE_TREE, PROOF_TREE = Path(PRED_META['candidate']), Path(PR['candidate'])
BASE = BASE_TREE / 'Coq'
MODULES = ['C.jet_elements_hash_getter_local', 'C.jet_elements_hash_getter_writehash',
           'C.jet_elements_hash_field_jets', 'C.jet_elements_tappath_local',
           'C.jet_elements_tappath_nullable', 'C.jet_elements_tap_getters_literal']
NEW_SOURCES = ['C/jet_elements_tap_getters_literal.v']
MODIFIED_SOURCES = ['C/jet_elements_tappath_nullable.v']
GUARDS = ['elements-tap-getters/' + n for n in ['check-source.py', 'test-source.py']]
METADATA, SCRIPTS = parent.METADATA, parent.SCRIPTS
ENDPOINTS = [
    ('internal_key', 'jet_elements_hash_field_jets', 'elements_internal_key_local_spec', 'Ty.Unit', 'Word256'),
    ('tappath', 'jet_elements_tappath_nullable', 'elements_tappath_u8_local_spec', 'Word8', '(Ty.Sum Ty.Unit Word256)')]
COVERAGE = ''.join('simplicity_' + f + ' C.' + m + ' ' + n + '\n' for f, m, n, _, _ in ENDPOINTS)
write = parent.write


def baseline_inputs():
    result = dict(PRED_META['baseline_inputs'])
    result.update({'Coq/' + n: s.sha((BASE / n).read_bytes()) for n in
                   parent.METADATA + parent.SCRIPTS + parent.GUARDS + parent.NEW_SOURCES})
    return result


def boundaries():
    if s.inputs.fingerprint(BASE, BASE_TREE) != PRED_REVIEW['candidate_input_sha256']:
        raise ValueError('reviewed predecessor source changed')
    if s.inputs.fingerprint(PROOF_TREE / 'Coq', PROOF_TREE) != PR['candidate_input_sha256']:
        raise ValueError('completed proof tree changed')
    evidence = json.loads((PROOF / 'EVIDENCE-REVIEW.json').read_text())
    if (evidence['preparation_sha256'] != s.sha((PROOF / 'PREPARATION.json').read_bytes()) or
        evidence['review_sha256'] != s.sha((PROOF / 'REVIEW.json').read_bytes()) or
        evidence['normal_registration'] is not False or evidence['full_acceptance'] is not False):
        raise ValueError('completed proof review binding differs')
    for n, h in evidence['tools_sha256'].items():
        if s.sha((PROOF / n).read_bytes()) != h:
            raise ValueError('completed proof reviewer changed')
    for n, row in evidence['commands'].items():
        if row['exit_code'] != 0 or row['log_sha256'] != s.sha((PROOF / (n + '.log')).read_bytes()):
            raise ValueError('completed proof review command/log changed')
    for n, h in PR['tools_sha256'].items():
        if s.sha((PROOF / n).read_bytes()) != h:
            raise ValueError('completed proof checker changed')
    for n, h in PRED_REVIEW['tools_sha256'].items():
        if s.sha((PRED / n).read_bytes()) != h:
            raise ValueError('predecessor review tool changed')
    for m in MODULES:
        if s.sha((PROOF_TREE / 'Coq' / (m.replace('.', '/') + '.v')).read_bytes()) != PR['source_sha256'][m]:
            raise ValueError('checked proof source changed')
        if s.sha((PROOF_TREE / 'Coq' / (m.replace('.', '/') + '.vo')).read_bytes()) != PR['object_sha256'][m]:
            raise ValueError('completed compiler object changed')
    if s.input_map() not in [PR['main_inputs'], baseline_inputs()] or s.index_hash() != PR['staged_patch_sha256']:
        raise ValueError('main/index is not a preserved known predecessor checkpoint')


def additions():
    parser = load('tap_declarations', PROOF / 'check.py')
    results, definitions = [], []
    for m in MODULES:
        a, b = parser.declarations((PROOF_TREE / 'Coq' / (m.replace('.', '/') + '.v')).read_text(), m)
        results += [' '.join(n.rsplit('.', 1)) for n in a]
        definitions += [' '.join(n.rsplit('.', 1)) for n in b]
    if (len(results), len(definitions)) != (38, 19):
        raise ValueError('wrong six-module declaration inventory')
    old = {m for m, _ in normal.rows(BASE / 'C/jet_public_theorems.txt')}
    if old & set(MODULES):
        raise ValueError('new printer rules would affect inherited public records')
    return {'_CoqProject': [m.replace('.', '/') + '.v' for m in MODULES],
            '_CoqProject.jets': [m.replace('.', '/') + '.v' for m in MODULES],
            'C/jet_public_theorems.txt': results, 'C/jet_contract_definitions.txt': definitions}


def script_changes():
    once = parent.replace_once
    original = (BASE / 'jet-coverage.py').read_text()
    old = '            elif name == "simplicity_tx_is_final":'
    new = r'''            elif name == "simplicity_internal_key":
                contract = (rf"\bapplication_jet_local_spec_sep\s+f_{re.escape(name)}\s+"
                            r"elements_ge\s+Elements\.env\s+Ty\.Unit\s+Word256\b")
            elif name == "simplicity_tappath":
                contract = (rf"\bapplication_jet_local_spec_sep\s+f_{re.escape(name)}\s+"
                            r"elements_ge\s+Elements\.env\s+Word8\s+\(Ty\.Sum\s+Ty\.Unit\s+Word256\)")
            elif name == "simplicity_tx_is_final":'''
    changes = {'jet-coverage.py': once(original, old, new, 'two exact whole C contracts').replace(
        '# Only these thirty-eight selected correspondences have a reviewed',
        '# Only these forty selected correspondences have a reviewed')}
    original = (BASE / 'check-jets.sh').read_text()
    old = 'python3 elements-output-proof/test-source.py "${JET_C_REPO:-..}" . C/jet_elements_output_proof_literal.v\n'
    extra = ''.join('python3 elements-tap-getters/' + n + ' "${JET_C_REPO:-..}"\n'
                    for n in ['check-source.py', 'test-source.py'])
    changes['check-jets.sh'] = once(original, old, old + extra, 'mandatory tap source and negative guards')
    original = (BASE / 'audit-jet-contracts.sh').read_text()
    lines = re.findall(r'(?m)^    explicit = .*$', original)
    if len(lines) != 1:
        raise ValueError('ambiguous explicit printer')
    changes['audit-jet-contracts.sh'] = once(original, lines[0], lines[0] +
        ' || ($1 ~ /^(' + '|'.join(m.replace('.', '[.]') for m in MODULES) + ')$/)', 'new modules only')
    original = (BASE / 'test-jet-coverage.py').read_text()
    boundary = '    print("coverage tests passed: exact core/partial/application contracts; wrong function/global/logical environment and unknown/duplicate/helper/unaudited entries rejected")'
    fragment = original.split('        # Thirteen optional/outpoint/output contracts; never compile bad fixtures.\n', 1)
    if len(fragment) != 2:
        raise ValueError('missing statement-confined fixture template')
    fragment = fragment[1].split(boundary, 1)[0]
    fragment = once(fragment, fragment.splitlines()[0],
        '        for suffix, filename, theorem, domain, output in ' + repr(ENDPOINTS) + ':', 'fourteen coverage negatives')
    changes['test-jet-coverage.py'] = once(original, boundary,
        '        # Two raw-key/byte-index contracts; never compile bad fixtures.\n' + fragment + boundary, 'new fixtures only')
    return changes


def assemble():
    if (HERE / 'ASSEMBLY.json').exists():
        raise ValueError('candidate already assembled; continue its recorded private tree')
    # At first assembly the original completed review still sees its exact main
    # checkpoint. Later preparation/review allow only this checkpoint or 399.
    proof_review = load('tap_original_review', PROOF / 'review.py')
    proof_review.review()
    boundaries()
    before, index = s.input_map(), s.index_hash()
    work = Path(tempfile.mkdtemp(prefix='jet-tap-getters-admission.', dir='/private/tmp'))
    subprocess.run(['cp', '-cR', str(PROOF_TREE / 'Coq'), str(work / 'Coq')], check=True)
    for n in ['C', 'Haskell']:
        (work / n).symlink_to(REPO / n, target_is_directory=True)
    paths = load('tap_source_paths', HERE.parent / 'elements-pegin-normal/review.py').source_paths
    inherited = paths(BASE)
    if paths(work / 'Coq') - set(NEW_SOURCES) - inherited:
        raise ValueError('immutable completed seed contains unexpected source files')
    changes = {work / 'Coq' / n: (BASE / n).read_text() for n in inherited}
    extensions = additions()
    for n, rows in extensions.items():
        old = (BASE / n).read_text()
        if not old.endswith('\n') or any(row in old.splitlines() for row in rows):
            raise ValueError('nonfresh manifest/declaration append')
        changes[work / 'Coq' / n] = old + '\n'.join(rows) + '\n'
    if {x.split()[0] for x in COVERAGE.splitlines()} & {x.split()[0] for x in (BASE / 'C/jet_coverage.tsv').read_text().splitlines() if x.strip()}:
        raise ValueError('selected jet already registered')
    changes[work / 'Coq/C/jet_coverage.tsv'] = (BASE / 'C/jet_coverage.tsv').read_text() + COVERAGE
    for m in MODULES:
        name = m.replace('.', '/') + '.v'
        changes[work / 'Coq' / name] = (PROOF_TREE / 'Coq' / name).read_text()
    changes.update({work / 'Coq' / n: (HERE.parent / n).read_text() for n in GUARDS})
    changes.update({work / 'Coq' / n: text for n, text in script_changes().items()})
    s.changed(changes)
    boundaries()
    if s.input_map() != before or s.index_hash() != index:
        raise ValueError('main/index changed during assembly')
    meta = dict(candidate=str(work), predecessor_candidate=str(BASE_TREE),
        predecessor_input_sha256=PRED_REVIEW['candidate_input_sha256'],
        predecessor_review_sha256=s.sha((PRED / 'REVIEW.json').read_bytes()),
        proof_preparation_sha256=s.sha((PROOF / 'PREPARATION.json').read_bytes()),
        proof_review_sha256=s.sha((PROOF / 'EVIDENCE-REVIEW.json').read_bytes()),
        main_inputs=before, main_input_sha256=s.inputs.fingerprint(MAIN, REPO), baseline_inputs=baseline_inputs(),
        staged_patch_sha256=index, extensions=extensions, coverage_additions=COVERAGE,
        baseline_metadata_sha256={n: s.sha((BASE / n).read_bytes()) for n in METADATA + SCRIPTS},
        source_sha256={m: s.sha((PROOF_TREE / 'Coq' / (m.replace('.', '/') + '.v')).read_bytes()) for m in MODULES},
        reviewed_source_generalization={n: {'before': s.sha((BASE / n).read_bytes()),
            'after': s.sha((PROOF_TREE / 'Coq' / n).read_bytes())} for n in MODIFIED_SOURCES},
        new_sources=NEW_SOURCES, coverage_added=2, full_acceptance=False)
    write(work / 'ASSEMBLY.json', meta)
    write(HERE / 'ASSEMBLY.json', meta)
    print(json.dumps(dict(candidate=str(work), modules=6, results=38, definitions=19,
                         proposed_coverage='401/533', main_changed=False)), flush=True)


def prepare(work):
    if (work / 'PREPARATION.json').exists():
        raise ValueError('candidate preparation already completed; review its evidence')
    meta = json.loads((work / 'ASSEMBLY.json').read_text())
    boundaries()
    before = s.input_map()
    built = s.run(work, ['bash', 'build-jets.sh', '-j2'], 'build', 10800)
    fresh = {m: s.run(work, ['bash', 'build-jets.sh', '--coqc', '-q', m.replace('.', '/') + '.v'],
                      'fresh-' + m, 180) for m in MODULES}
    coq = work / 'Coq'
    results = [tuple(row.split()) for row in meta['extensions']['C/jet_public_theorems.txt']]
    definitions = [tuple(row.split()) for row in meta['extensions']['C/jet_contract_definitions.txt']]
    all_rows = normal.rows(coq / 'C/jet_public_theorems.txt') + normal.rows(coq / 'C/jet_contract_definitions.txt')
    header = ['Set Warnings "-notation-overridden".']
    for m in sorted({m for m, _ in all_rows}):
        keyword = ('Require' if m.startswith(('Simplicity.', 'C.jet_elements_')) or m in
            {'C.jet_secp_umul128_exec', 'C.jet_haskell_hash_word', 'C.jet_application_partial_transport'} else 'Require Import')
        header.append(keyword + ' ' + m + '.')
    assumptions = header[:]
    for m, n in results:
        assumptions += ['Goal True. idtac "JET_ASSUMPTIONS ' + m + '.' + n + '". exact I. Qed.', 'Print Assumptions ' + m + '.' + n + '.']
    wanted = [('TYPE', m + '.' + n) for m, n in results] + [('DEF', m + '.' + n) for m, n in definitions]
    driver = header + ['Import Simplicity.BitMachine Simplicity.Translate.', 'Set Printing All.', 'Set Printing Width 120.']
    for depth, marker in [(50, 'TAP_COMPACT_'), (1000000, 'TAP_DEEP_')]:
        driver += ['Set Printing Depth ' + str(depth) + '.']
        for kind, n in wanted:
            driver += ['Goal True. idtac "' + marker + kind + ' ' + n + '". exact I. Qed.', ('Check @' if kind == 'TYPE' else 'Print ') + n + '.']
    s.changed({work / 'new_contracts.v': '\n'.join(driver) + '\n', work / 'new_assumptions.v': '\n'.join(assumptions) + '\n'})
    contracts = s.run(work, ['bash', 'build-jets.sh', '--coqc', '-q', str(work / 'new_contracts.v')], 'new_contracts', 1800)
    audited = s.run(work, ['bash', 'build-jets.sh', '--coqc', '-q', str(work / 'new_assumptions.v')], 'new_assumptions', 1800)
    report = (work / 'new_contracts.log').read_text().split('TAP_DEEP_', 1)[0]
    marks = list(re.finditer(r'(?m)^TAP_COMPACT_(TYPE|DEF) (\S+)\n', report))
    if [(m[1], m[2]) for m in marks] != wanted or report[:marks[0].start()]:
        raise ValueError('incomplete compact report')
    bodies = {wanted[i]: ''.join(line.rstrip() + '\n' for line in report[m.end():marks[i+1].start() if i+1 < len(marks) else len(report)].splitlines()) for i, m in enumerate(marks)}
    inherited = normal.contract_records((BASE / 'C/jet_contracts.expected').read_text(),
        normal.rows(BASE / 'C/jet_public_theorems.txt'), normal.rows(BASE / 'C/jet_contract_definitions.txt'))
    snapshot = ''.join(t for (k, _, _, _), t in inherited if k == 'TYPE') + ''.join(bodies['TYPE', m + '.' + n] for m, n in results)
    snapshot += ''.join(t for (k, _, _, _), t in inherited if k == 'DEF') + ''.join(bodies['DEF', m + '.' + n] for m, n in definitions)
    deps = normal.assumptions((work / 'new_assumptions.log').read_text())
    if set(deps) != {m + '.' + n for m, n in results} or any(sorted(ds) != PR['dependencies'][n] for n, ds in deps.items()):
        raise ValueError('normal assumptions differ from checked proofs')
    old_deps = snapshot_deps((BASE / 'C/jet_assumptions.expected').read_text())
    if set(old_deps) & set(deps):
        raise ValueError('overlapping public assumption records')
    old_deps.update({n: sorted(ds) for n, ds in deps.items()})
    text = ''.join(n + ' : ' + (', '.join(ds) or 'closed') + '\n' for n, ds in sorted(old_deps.items()))
    s.changed({coq / 'C/jet_contracts.expected': snapshot, coq / 'C/jet_assumptions.expected': text})
    boundaries()
    if s.input_map() != before or s.index_hash() != meta['staged_patch_sha256']:
        raise ValueError('main/index changed during preparation')
    r = dict(candidate=str(work), build=built, fresh_compiles=fresh, contracts=contracts, assumptions=audited,
        new_dependencies={n: sorted(ds) for n, ds in deps.items()},
        new_objects_sha256={m: s.sha((coq / (m.replace('.', '/') + '.vo')).read_bytes()) for m in MODULES},
        coverage_added=2, full_acceptance=False)
    write(work / 'PREPARATION.json', r)
    write(HERE / 'PREPARATION.json', r)
    print('Two-jet normal preparation complete; review and full acceptance still required', flush=True)


if __name__ == '__main__':
    if sys.argv[1:] == ['assemble']:
        assemble()
    elif len(sys.argv) == 3 and sys.argv[1] == 'prepare':
        prepare(Path(sys.argv[2]).resolve())
    else:
        raise ValueError('usage: admission.py assemble|prepare PRIVATE_TREE')
