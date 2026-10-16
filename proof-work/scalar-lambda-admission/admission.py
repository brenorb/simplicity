"""Normal initialized-lambda delta over reviewed419; no main installation.

Seed objects come only from the completed418-based refresh. The live419
predecessor contributes sources/metadata, never its mutable object cache.
"""
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


parent = load('lambda_normal_419_parent', HERE.parent / 'elements-null-data-admission/admission.py')
s, normal, snapshot_deps, write = parent.s, parent.normal, parent.snapshot_deps, parent.write
PRED = HERE.parent / 'elements-null-data-admission'
PRED_META = json.loads((PRED / 'ASSEMBLY.json').read_text())
PRED_REVIEW = json.loads((PRED / 'REVIEW.json').read_text())
BASE_TREE = Path(PRED_META['candidate'])
BASE = BASE_TREE / 'Coq'
PROOF = HERE.parent / 'scalar-lambda-refresh'
PR = json.loads((PROOF / 'CHECKED.json').read_text())
PROOF_TREE = Path(PR['candidate'])
ASSEMBLED_PROOF = json.loads((PROOF / 'ASSEMBLY.json').read_text())
MODULES = PR['modules']
NEW_SOURCES = ASSEMBLED_PROOF['new_sources']
REUSED_SOURCES = ASSEMBLED_PROOF['reused_sources']
MANIFEST_SOURCES = [m.replace('.', '/') + '.v' for m in MODULES]
GUARDS = ['scalar-lambda-integration/' + n for n in ['check-lambda-public.py', 'test-lambda-public.py']]
METADATA, SCRIPTS = parent.METADATA, parent.SCRIPTS
COVERAGE_ADDED = 1
COVERAGE = ('simplicity_scalar_multiply_lambda C.jet_secp_scalar_lambda_local '
            'scalar_lambda_initialized_local_spec\n')
PREPARE_ENGINE = HERE.parent / 'normal-delta-prepare-v2.py'
ALLOWED_DEPENDENCIES = s.SIX | {'Events.external_functions_properties', 'Events.inline_assembly_properties'}
ENDPOINTS = ['C.jet_secp_scalar_lambda_local.scalar_lambda_initialized_local_spec',
             'C.jet_secp_scalar_lambda_fresh.scalar_lambda_runs_from_actual_init']
ENDPOINT_DEPENDENCIES = {n: ALLOWED_DEPENDENCIES for n in ENDPOINTS}
REQUIRE_ONLY_MODULES = set(parent.MODULES) | {
    'C.jet_forWhile_fold', 'C.jet_u32_local_init', 'C.jet_local_alloc_effect'}


def proof_evidence_hashes():
    paths = [PROOF / n for n in ['ASSEMBLY.json', 'RUN.json', 'CHECKED.json', 'EVIDENCE-REVIEW.json']]
    return {str(p.relative_to(HERE.parent)): s.sha(p.read_bytes()) for p in paths}


def baseline_inputs():
    result = dict(PRED_META['baseline_inputs'])
    for n in parent.METADATA + parent.SCRIPTS + parent.NEW_SOURCES + parent.GUARDS:
        result['Coq/' + n] = s.sha((BASE / n).read_bytes())
    return result


def main_fingerprint(inputs):
    if inputs != PRED_META['main_inputs']:
        raise ValueError('unknown main checkpoint; expected exact accepted418')
    return PRED_META['main_input_sha256']


def source_check(work):
    return load('lambda_selected_public_source', HERE.parent / GUARDS[0]).check(REPO, work / 'Coq')


def boundaries():
    # Full acceptance of419 is required at the later combined-audit launch,
    # not invented here as a prerequisite to isolated normal preparation.
    predecessor = load('lambda_reviewed_419', PRED / 'accept.py').reviewed(BASE_TREE)
    if predecessor != PRED_REVIEW or predecessor['candidate_input_sha256'] != s.inputs.fingerprint(BASE, BASE_TREE):
        raise ValueError('reviewed419 source/evidence changed')
    v = load('lambda_completed_refresh', PROOF / 'review.py')
    actual = v.review(PROOF_TREE)
    e = json.loads((PROOF / 'EVIDENCE-REVIEW.json').read_text())
    if (e['review'] != actual or e['checked_sha256'] != s.sha((PROOF / 'CHECKED.json').read_bytes()) or
        e['assembly_sha256'] != s.sha((PROOF / 'ASSEMBLY.json').read_bytes()) or
        e['launch_sha256'] != s.sha((PROOF / 'RUN.json').read_bytes()) or
        e['candidate_input_sha256'] != PR['candidate_input_sha256'] or
        e['normal_registration'] is not False or e['full_acceptance'] is not False):
        raise ValueError('completed refresh review differs')
    for n, h in e['tools_sha256'].items():
        if s.sha((PROOF / n).read_bytes()) != h:
            raise ValueError('refresh checker/reviewer changed')
    for n, h in e['inherited_tools_sha256'].items():
        if s.sha((REPO / n).read_bytes()) != h:
            raise ValueError('inherited canonical source reviewer changed')
    row = e['commands']['evidence-tests']
    if (set(e['commands']) != {'evidence-tests'} or row['exit_code'] != 0 or
        row['log_sha256'] != s.sha((PROOF_TREE / 'evidence-tests.log').read_bytes()) or
        (PROOF / 'evidence-tests.log').read_bytes() != (PROOF_TREE / 'evidence-tests.log').read_bytes()):
        raise ValueError('refresh evidence-test exit/log differs')
    for n in REUSED_SOURCES:
        if (BASE / n).read_bytes() != (PROOF_TREE / 'Coq' / n).read_bytes():
            raise ValueError('shared existing proof differs')
    if (s.input_map() != PRED_META['main_inputs'] or s.index_hash() != PR['staged_patch_sha256'] or
        (len(MODULES), len(NEW_SOURCES), len(REUSED_SOURCES)) != (28, 26, 2)):
        raise ValueError('main/index or complete refresh scope differs')


def additions():
    old_r = set(normal.rows(BASE / 'C/jet_public_theorems.txt'))
    old_d = set(normal.rows(BASE / 'C/jet_contract_definitions.txt'))
    results = [tuple(n.rsplit('.', 1)) for n in PR['results']]
    definitions = [tuple(n.rsplit('.', 1)) for n in PR['definitions']]
    if (len(results), len(definitions)) != (116, 32) or old_r & set(results) or old_d & set(definitions):
        raise ValueError('wrong/nonfresh complete public inventory')
    if {m for m, _ in old_r} & set(MODULES):
        raise ValueError('new printer rules affect inherited theorem modules')
    return {'_CoqProject': MANIFEST_SOURCES, '_CoqProject.jets': MANIFEST_SOURCES,
            'C/jet_public_theorems.txt': [' '.join(row) for row in results],
            'C/jet_contract_definitions.txt': [' '.join(row) for row in definitions]}


def script_changes():
    once = load('lambda_admission_exact_replace', HERE.parent / 'elements-direct-getters-admission/admission.py').replace_once
    original = (BASE / 'jet-coverage.py').read_text()
    old = '                contract = rf"\\bsecp_jet_local_spec\\s+f_{re.escape(name)}\\b"\n'
    extra = r'''            elif name == "simplicity_scalar_multiply_lambda":
                # Named initialized-global contract; never arbitrary Ready.
                contract = (r"\bsecp_jet_initialized_local_spec\s+scalar_lambda_initialized\s+"
                            r"f_simplicity_scalar_multiply_lambda\s+\(Word\s+8\)\s+\(Word\s+8\)\s+"
                            r"\(@canonical_scalar_multiply_lambda\s+Alg\.CoreFunSem\)\s*\.$")
'''
    changes = {'jet-coverage.py': once(original, old, old + extra, 'exact initialized lambda whole contract')}
    original = (BASE / 'check-jets.sh').read_text()
    old = 'python3 scalar-square-review/test-square-public.py "${JET_C_REPO:-..}" .\n'
    extra = ('python3 scalar-lambda-integration/check-lambda-public.py --repo "${JET_C_REPO:-..}" --coq .\n'
             'python3 scalar-lambda-integration/test-lambda-public.py "${JET_C_REPO:-..}" .\n')
    changes['check-jets.sh'] = once(original, old, old + extra, 'mandatory initialized lambda source/mutation gates')
    original = (BASE / 'audit-jet-contracts.sh').read_text()
    names = '|'.join(m.replace('.', '[.]') for m in MODULES)
    anchor = '         /^C\\.jet_secp_umul128_exec$/ {print "Require " $0 "."; next}\n'
    original = once(original, anchor, anchor + '         /^(' + names + ')$/ {print "Require " $0 "."; next}\n', 'new modules Require-only')
    lines = re.findall(r'(?m)^    explicit = .*$', original)
    if len(lines) != 1:
        raise ValueError('ambiguous explicit-printer rule')
    changes['audit-jet-contracts.sh'] = once(original, lines[0], lines[0] +
        ' || ($1 ~ /^(' + names + ')$/)', 'explicit types only for new public modules')
    original = (BASE / 'test-jet-coverage.py').read_text()
    marker = '    print("coverage tests passed: exact core/partial/application contracts; wrong function/global/logical environment and unknown/duplicate/helper/unaudited entries rejected")'
    changes['test-jet-coverage.py'] = once(original, marker, (HERE / 'coverage-fixtures.py').read_text() + marker, 'initialized lambda full-boundary fixtures')
    return changes


def assemble():
    if (HERE / 'ASSEMBLY.json').exists():
        raise ValueError('already assembled; continue recorded candidate')
    boundaries()
    before, index = s.input_map(), s.index_hash()
    work = Path(tempfile.mkdtemp(prefix='jet-scalar-lambda-admission.', dir='/private/tmp'))
    subprocess.run(['cp', '-cR', str(PROOF_TREE / 'Coq'), str(work / 'Coq')], check=True)
    for n in ['C', 'Haskell']:
        (work / n).symlink_to(REPO / n, target_is_directory=True)
    paths = load('lambda_normal_source_inventory', HERE.parent / 'elements-pegin-normal/review.py').source_paths
    if (paths(work / 'Coq') - paths(BASE) != set(NEW_SOURCES) or
        paths(BASE) - paths(work / 'Coq') != set(parent.NEW_SOURCES + parent.GUARDS)):
        raise ValueError('unexpected completed seed/source predecessor inventory')
    changes = {work / 'Coq' / n: (BASE / n).read_text() for n in paths(BASE)}
    extensions = additions()
    for n, rows in extensions.items():
        text = (BASE / n).read_text()
        if not text.endswith('\n') or any(row in text.splitlines() for row in rows):
            raise ValueError('nonfresh normal inventory append')
        changes[work / 'Coq' / n] = text + '\n'.join(rows) + '\n'
    if 'simplicity_scalar_multiply_lambda ' in (BASE / 'C/jet_coverage.tsv').read_text():
        raise ValueError('lambda already registered')
    changes[work / 'Coq/C/jet_coverage.tsv'] = (BASE / 'C/jet_coverage.tsv').read_text() + COVERAGE
    for n in GUARDS:
        if (BASE / n).exists():
            raise ValueError('new guard path already exists')
        changes[work / 'Coq' / n] = (HERE.parent / n).read_text()
    changes.update({work / 'Coq' / n: text for n, text in script_changes().items()})
    s.changed(changes)
    source_check(work)
    boundaries()
    if s.input_map() != before or s.index_hash() != index:
        raise ValueError('main/index drift during assembly')
    meta = dict(candidate=str(work), predecessor_candidate=str(BASE_TREE),
        predecessor_input_sha256=PRED_REVIEW['candidate_input_sha256'],
        predecessor_review_sha256=s.sha((PRED / 'REVIEW.json').read_bytes()), proof_evidence_sha256=proof_evidence_hashes(),
        preparation_engine_sha256=s.sha(PREPARE_ENGINE.read_bytes()), main_inputs=before,
        main_input_sha256=main_fingerprint(before), baseline_inputs=baseline_inputs(), staged_patch_sha256=index,
        extensions=extensions, coverage_additions=COVERAGE, new_sources=NEW_SOURCES,
        baseline_metadata_sha256={n: s.sha((BASE / n).read_bytes()) for n in METADATA + SCRIPTS},
        source_sha256={m: PR['source_sha256'][m] for m in MODULES}, coverage_added=1, full_acceptance=False)
    write(work / 'ASSEMBLY.json', meta)
    write(HERE / 'ASSEMBLY.json', meta)
    print(json.dumps(dict(candidate=str(work), modules=28, added_sources=26, reused_sources=2,
                         results=116, definitions=32, proposed_coverage='420/533', main_changed=False)), flush=True)


if __name__ == '__main__':
    if sys.argv[1:] == ['assemble']:
        assemble()
    elif len(sys.argv) == 3 and sys.argv[1] == 'prepare':
        load('lambda_normal_prepare_v2', PREPARE_ENGINE).prepare(SimpleNamespace(**globals()), Path(sys.argv[2]).resolve())
    else:
        raise ValueError('usage: admission.py assemble|prepare PRIVATE_TREE')
