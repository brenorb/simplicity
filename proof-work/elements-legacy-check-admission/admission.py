"""Normal legacy assertion candidate over the reviewed 404 source predecessor."""
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile
from types import SimpleNamespace

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
REPO, MAIN = HERE.parents[1], HERE.parents[1] / 'Coq'


def load(name, path):
    sp = importlib.util.spec_from_file_location(name, path)
    m = importlib.util.module_from_spec(sp)
    sp.loader.exec_module(m)
    return m


parent = load('legacy_check_normal_predecessor', HERE.parent / 'elements-legacy-lock-admission/admission.py')
s, normal, snapshot_deps, write = parent.s, parent.normal, parent.snapshot_deps, parent.write
PRED, PROOF = HERE.parent / 'elements-legacy-lock-admission', HERE.parent / 'elements-legacy-check'
PRED_META = json.loads((PRED / 'ASSEMBLY.json').read_text())
PRED_REVIEW = json.loads((PRED / 'REVIEW.json').read_text())
PR = json.loads((PROOF / 'CHECKED.json').read_text())
BASE_TREE, PROOF_TREE = Path(PRED_META['candidate']), Path(PR['candidate'])
BASE = BASE_TREE / 'Coq'
MODULES = ['C.jet_elements_legacy_check']
NEW_SOURCES = [m.replace('.', '/') + '.v' for m in MODULES]
GUARDS = ['elements-legacy-check/' + n for n in ['check-source.py', 'test-source.py']]
METADATA, SCRIPTS = parent.METADATA, parent.SCRIPTS
COVERAGE_ADDED = 2
COVERAGE = ''.join('simplicity_broken_do_not_use_check_lock_' + n +
    ' C.jet_elements_legacy_check elements_broken_check_lock_' + n + '_local_spec\n' for n in ['distance', 'duration'])
PREPARE_ENGINE = HERE.parent / 'normal-delta-prepare.py'


def baseline_inputs():
    result = dict(PRED_META['baseline_inputs'])
    result.update({'Coq/' + n: s.sha((BASE / n).read_bytes()) for n in
                  parent.METADATA + parent.SCRIPTS + parent.GUARDS + parent.NEW_SOURCES})
    return result


def boundaries():
    if (s.inputs.fingerprint(BASE, BASE_TREE) != PRED_REVIEW['candidate_input_sha256'] or
        s.inputs.fingerprint(PROOF_TREE / 'Coq', PROOF_TREE) != PR['candidate_input_sha256']):
        raise ValueError('reviewed predecessor/completed proof source changed')
    evidence = json.loads((PROOF / 'EVIDENCE-REVIEW.json').read_text())
    if (evidence['checked_sha256'] != s.sha((PROOF / 'CHECKED.json').read_bytes()) or
        evidence['launch_sha256'] != s.sha((PROOF / 'RUN.json').read_bytes()) or
        evidence['candidate_input_sha256'] != PR['candidate_input_sha256'] or
        evidence['canonical_source_gate_complete'] is not True or evidence['normal_registration'] is not False or
        evidence['full_acceptance'] is not False or PR['recursive_kernel_check'] is not True):
        raise ValueError('completed proof/source review scope or identity differs')
    for n, h in evidence['tools_sha256'].items():
        if s.sha((PROOF / n).read_bytes()) != h:
            raise ValueError('completed proof reviewer changed')
    for n, row in evidence['commands'].items():
        if row['exit_code'] != 0 or row['log_sha256'] != s.sha((PROOF / (n + '.log')).read_bytes()):
            raise ValueError('source/evidence review log changed')
    for n, h in PR['tools_sha256'].items():
        if s.sha((PROOF / n).read_bytes()) != h:
            raise ValueError('completed proof checker changed')
    for n, row in PR['commands'].items():
        if row['exit_code'] != 0 or row['log_sha256'] != s.sha((PROOF_TREE / (n + '.log')).read_bytes()):
            raise ValueError('completed compiler/kernel/AST/report evidence changed')
    for m in MODULES:
        for suffix, table in [('.v', 'source_sha256'), ('.vo', 'object_sha256')]:
            if s.sha((PROOF_TREE / 'Coq' / (m.replace('.', '/') + suffix)).read_bytes()) != PR[table][m]:
                raise ValueError('completed proof source/object changed')
    for n, h in PRED_REVIEW['tools_sha256'].items():
        if s.sha((PRED / n).read_bytes()) != h:
            raise ValueError('predecessor review tool changed')
    if PRED_REVIEW['preparation_engine_sha256'] != s.sha(PREPARE_ENGINE.read_bytes()):
        raise ValueError('reviewed shared preparation engine changed')
    if s.input_map() not in [PRED_META['main_inputs'], PRED_META['baseline_inputs'], baseline_inputs(), parent.parent.baseline_inputs()] or s.index_hash() != PR['staged_patch_sha256']:
        raise ValueError('main/index is not an exact preserved 399/401/402/404 checkpoint')


def additions():
    results, definitions = [], []
    parser = load('legacy_declarations', PROOF / 'check.py').shared
    for m in MODULES:
        a, b = parser.declarations((PROOF_TREE / 'Coq' / (m.replace('.', '/') + '.v')).read_text(), m)
        results += [' '.join(n.rsplit('.', 1)) for n in a]
        definitions += [' '.join(n.rsplit('.', 1)) for n in b]
    if (len(results), len(definitions)) != (8, 5):
        raise ValueError('wrong one-module declaration inventory')
    if {m for m, _ in normal.rows(BASE / 'C/jet_public_theorems.txt')} & set(MODULES):
        raise ValueError('new printer rules affect inherited declarations')
    return {'_CoqProject': NEW_SOURCES, '_CoqProject.jets': NEW_SOURCES,
            'C/jet_public_theorems.txt': results, 'C/jet_contract_definitions.txt': definitions}


def script_changes():
    once = load('legacy_exact_replace', HERE.parent / 'elements-thirteen-getters-admission/admission.py').replace_once
    original = (BASE / 'jet-coverage.py').read_text()
    old = '            elif name == "simplicity_tx_is_final":'
    new = r'''            elif name in {"simplicity_broken_do_not_use_check_lock_distance", "simplicity_broken_do_not_use_check_lock_duration"}:
                contract = (rf"\bapplication_jet_partial_spec\s+f_{re.escape(name)}\s+"
                            r"elements_ge\s+Elements\.env\s+Word16\s+Ty\.Unit\b")
            elif name == "simplicity_tx_is_final":'''
    changes = {'jet-coverage.py': once(original, old, new, 'exact two historical whole-C contracts').replace(
        '# Only these forty-three selected correspondences have a reviewed', '# Only these forty-five selected correspondences have a reviewed')}
    original = (BASE / 'check-jets.sh').read_text()
    old = 'python3 elements-legacy-lock/test-source.py "${JET_C_REPO:-..}"\n'
    extra = ''.join('python3 elements-legacy-check/' + n + ' "${JET_C_REPO:-..}"\n' for n in ['check-source.py', 'test-source.py'])
    changes['check-jets.sh'] = once(original, old, old + extra, 'mandatory legacy canonical/source negative gates')
    original = (BASE / 'audit-jet-contracts.sh').read_text()
    lines = re.findall(r'(?m)^    explicit = .*$', original)
    if len(lines) != 1:
        raise ValueError('ambiguous explicit printer')
    changes['audit-jet-contracts.sh'] = once(original, lines[0], lines[0] +
        ' || ($1 ~ /^(' + '|'.join(m.replace('.', '[.]') for m in MODULES) + ')$/)', 'new modules only')
    original = (BASE / 'test-jet-coverage.py').read_text()
    boundary = '    print("coverage tests passed: exact core/partial/application contracts; wrong function/global/logical environment and unknown/duplicate/helper/unaudited entries rejected")'
    fragment = original.split('        # Historical relative-lock whole-C contracts; never compile bad fixtures.\n', 1)
    if len(fragment) != 2:
        raise ValueError('missing statement-confined fixture template')
    fragment = fragment[1].split(boundary, 1)[0]
    rows = [('broken_do_not_use_check_lock_' + n, 'jet_elements_legacy_check',
             'elements_broken_check_lock_' + n + '_local_spec', 'Word16', 'Ty.Unit') for n in ['distance', 'duration']]
    fragment = once(fragment, fragment.splitlines()[0],
        '        for suffix, filename, theorem, domain, output in ' + repr(rows) + ':', 'fourteen new whole-contract fixtures')
    fragment = once(fragment,
        "('application_jet_local_spec_sep f_simplicity_' + suffix, 'application_jet_local_spec f_simplicity_' + suffix),",
        "('application_jet_partial_spec f_simplicity_' + suffix, 'application_jet_local_spec_sep f_simplicity_' + suffix),",
        'reject replacing the assertion/failure contract with a total getter contract')
    changes['test-jet-coverage.py'] = once(original, boundary,
        '        # Historical relative-lock assertions; never compile bad fixtures.\n' + fragment + boundary, 'new fixtures only')
    return changes


def assemble():
    if (HERE / 'ASSEMBLY.json').exists():
        raise ValueError('already assembled; continue the recorded private candidate')
    boundaries()
    load('legacy_proof_canonical_guard', PROOF / 'check-source.py').check(PROOF_TREE)
    before, index = s.input_map(), s.index_hash()
    work = Path(tempfile.mkdtemp(prefix='jet-legacy-check-admission.', dir='/private/tmp'))
    # Only completed proof objects are copied. The predecessor supplies source.
    subprocess.run(['cp', '-cR', str(PROOF_TREE / 'Coq'), str(work / 'Coq')], check=True)
    for n in ['C', 'Haskell']:
        (work / n).symlink_to(REPO / n, target_is_directory=True)
    paths = load('legacy_source_inventory', HERE.parent / 'elements-pegin-normal/review.py').source_paths
    if paths(work / 'Coq') - set(NEW_SOURCES) - paths(BASE):
        raise ValueError('completed seed contains unexpected source')
    changes = {work / 'Coq' / n: (BASE / n).read_text() for n in paths(BASE)}
    extensions = additions()
    for n, rows in extensions.items():
        text = (BASE / n).read_text()
        if not text.endswith('\n') or any(row in text.splitlines() for row in rows):
            raise ValueError('nonfresh public inventory append')
        changes[work / 'Coq' / n] = text + '\n'.join(rows) + '\n'
    if any(row.split()[0] in (BASE / 'C/jet_coverage.tsv').read_text() for row in COVERAGE.splitlines()):
        raise ValueError('legacy getter already registered')
    changes[work / 'Coq/C/jet_coverage.tsv'] = (BASE / 'C/jet_coverage.tsv').read_text() + COVERAGE
    changes.update({work / 'Coq' / n: (PROOF_TREE / 'Coq' / n).read_text() for n in NEW_SOURCES})
    changes.update({work / 'Coq' / n: (HERE.parent / n).read_text() for n in GUARDS})
    changes.update({work / 'Coq' / n: text for n, text in script_changes().items()})
    s.changed(changes)
    boundaries()
    if s.input_map() != before or s.index_hash() != index:
        raise ValueError('main/index drift during assembly')
    meta = dict(candidate=str(work), predecessor_candidate=str(BASE_TREE),
        predecessor_input_sha256=PRED_REVIEW['candidate_input_sha256'],
        predecessor_review_sha256=s.sha((PRED / 'REVIEW.json').read_bytes()),
        proof_checked_sha256=s.sha((PROOF / 'CHECKED.json').read_bytes()),
        proof_review_sha256=s.sha((PROOF / 'EVIDENCE-REVIEW.json').read_bytes()),
        preparation_engine_sha256=s.sha(PREPARE_ENGINE.read_bytes()),
        main_inputs=before, main_input_sha256=s.inputs.fingerprint(MAIN, REPO), baseline_inputs=baseline_inputs(),
        staged_patch_sha256=index, extensions=extensions, coverage_additions=COVERAGE,
        baseline_metadata_sha256={n: s.sha((BASE / n).read_bytes()) for n in METADATA + SCRIPTS},
        source_sha256={m: PR['source_sha256'][m] for m in MODULES},
        new_sources=NEW_SOURCES, coverage_added=2, full_acceptance=False)
    write(work / 'ASSEMBLY.json', meta)
    write(HERE / 'ASSEMBLY.json', meta)
    print(json.dumps(dict(candidate=str(work), modules=1, results=8, definitions=5,
                         proposed_coverage='406/533', main_changed=False)), flush=True)


if __name__ == '__main__':
    if sys.argv[1:] == ['assemble']:
        assemble()
    elif len(sys.argv) == 3 and sys.argv[1] == 'prepare':
        engine = load('legacy_normal_delta_engine', PREPARE_ENGINE)
        engine.prepare(SimpleNamespace(**globals()), Path(sys.argv[2]).resolve())
    else:
        raise ValueError('usage: admission.py assemble|prepare PRIVATE_TREE')
