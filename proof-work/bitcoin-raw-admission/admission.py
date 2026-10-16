"""Isolated normal admission of sixteen checked raw Bitcoin hash programs.

Use only a completed420 object cache; the running actual-main audit is never
copied, restarted or modified. This prepares a candidate, not acceptance.
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


parent = load('raw_admission_completed420', HERE.parent / 'scalar-lambda-admission/integration.py')
s, normal = parent.s, parent.g.normal
snapshot_deps, write = parent.g.snapshot_deps, parent.g.write
PRED = HERE.parent / 'scalar-lambda-admission'
PRED_REVIEW = json.loads((PRED / 'REVIEW.json').read_text())
PRED_ACCEPTED = json.loads((PRED / 'ACCEPTANCE.json').read_text())
BASE_TREE = Path(PRED_ACCEPTED['candidate'])
BASE = BASE_TREE / 'Coq'
PROOF = HERE.parent / 'bitcoin-raw-program'
RAW = json.loads((PROOF / 'CHECKED.json').read_text())
PROOF_TREE = Path(RAW['candidate'])
TAPLEAF = HERE.parent / 'bitcoin-tapleaf-literal'
TAP = json.loads((TAPLEAF / 'CHECKED.json').read_text())
MODULES = ['C.jet_bitcoin_tapleaf_literal', 'C.jet_bitcoin_raw_program', 'C.jet_bitcoin_hash_raw_program']
MANIFEST_SOURCES = [m.replace('.', '/') + '.v' for m in MODULES]
NEW_SOURCES = MANIFEST_SOURCES
GUARDS = ['bitcoin-tapleaf-literal/' + n for n in ['check-source.py', 'test-source.py', 'source-model.txt']]
GUARDS += ['bitcoin-raw-program-source/' + n for n in ['check-source.py', 'test-source.py', 'source-model.py']]
METADATA, SCRIPTS = parent.g.METADATA, parent.g.SCRIPTS
COVERAGE_ADDED = 16
ENDPOINTS = RAW['endpoints']
COVERAGE = ''.join('simplicity_bitcoin_' + n.removeprefix('C.jet_bitcoin_hash_raw_program.bitcoin_').removesuffix('_raw_program_local_spec') +
                   ' C.jet_bitcoin_hash_raw_program ' + n.rsplit('.', 1)[1] + '\n' for n in ENDPOINTS)
PR = dict(results=TAP['results'] + RAW['results'], definitions=TAP['definitions'] + RAW['definitions'],
          closed_results=TAP['closed_results'] + RAW['closed_results'],
          dependencies=dict(TAP['dependencies'], **RAW['dependencies']),
          staged_patch_sha256=RAW['staged_patch_sha256'])
PREPARE_ENGINE = HERE.parent / 'normal-delta-prepare-v2.py'
ALLOWED_DEPENDENCIES = s.SIX
ENDPOINT_DEPENDENCIES = {n: s.SIX for n in ENDPOINTS}
REQUIRE_ONLY_MODULES = {'C.jet_forWhile_fold', 'C.jet_u32_local_init', 'C.jet_local_alloc_effect'}


def guard_sources():
    deployed = load('raw_admission_tapleaf_deployment', TAPLEAF / 'deploy-guards.py').sources()
    deployed.update({n: (HERE.parent / n).read_text() for n in GUARDS if n.startswith('bitcoin-raw-program-source/')})
    if set(deployed) != set(GUARDS):
        raise ValueError('incomplete raw hash-program guard deployment')
    return deployed


def proof_evidence_hashes():
    paths = [folder / name for folder in [TAPLEAF, PROOF]
             for name in ['RUN.json', 'CHECKED.json', 'EVIDENCE-REVIEW.json']]
    paths += [PROOF / 'KERNEL-RUN.json', TAPLEAF / 'GUARD-DEPLOYMENT.json']
    return {str(p.relative_to(HERE.parent)): s.sha(p.read_bytes()) for p in paths}


def baseline_inputs():
    return parent.planner.input_map(BASE_TREE)


def main_fingerprint(inputs):
    if inputs != baseline_inputs():
        raise ValueError('unknown raw-admission main checkpoint; expected checked420')
    return PRED_ACCEPTED['audit_input_sha256']


def source_check(work):
    return load('raw_admission_canonical_source', work / 'Coq/bitcoin-raw-program-source/check-source.py').check(work)


def boundaries():
    p, accepted, _, after = parent.candidate_acceptance(BASE_TREE)
    if (accepted != PRED_ACCEPTED or p['candidate_input_sha256'] != PRED_ACCEPTED['audit_input_sha256'] or
        after != baseline_inputs() or s.input_map() != after or s.index_hash() != PR['staged_patch_sha256']):
        raise ValueError('checked420 source/index boundary changed')
    for folder in [TAPLEAF, PROOF]:
        v = load('raw_admission_checked_' + folder.name, folder / 'review.py')
        evidence = json.loads((folder / 'EVIDENCE-REVIEW.json').read_text())
        work = Path(evidence['review']['candidate'])
        if (evidence['review'] != v.review(work) or
            evidence['checked_sha256'] != s.sha((folder / 'CHECKED.json').read_bytes()) or
            evidence['candidate_input_sha256'] != s.inputs.fingerprint(work / 'Coq', work) or
            evidence['normal_registration'] is not False or evidence['full_acceptance'] is not False):
            raise ValueError('raw/TapLeaf completed proof review differs')
        for n, digest in evidence['tools_sha256'].items():
            root = HERE.parent if folder == PROOF else folder
            if s.sha((root / n).read_bytes()) != digest:
                raise ValueError('reviewed proof/source checker changed')
        for stem, row in evidence['commands'].items():
            if (row['exit_code'] != 0 or row['log_sha256'] != s.sha((work / (stem + '.log')).read_bytes()) or
                (folder / (stem + '.log')).read_bytes() != (work / (stem + '.log')).read_bytes()):
                raise ValueError('reviewed proof/source command log changed')
    if (len(ENDPOINTS), len(PR['results']), len(PR['definitions']), len(PR['closed_results'])) != (16, 27, 10, 5):
        raise ValueError('wrong complete three-module proof inventory')
    for name in NEW_SOURCES:
        if (MAIN / name).exists() or (BASE / name).exists():
            raise ValueError('new proof would overwrite inherited/untracked source')


def additions():
    old_r = set(normal.rows(BASE / 'C/jet_public_theorems.txt'))
    old_d = set(normal.rows(BASE / 'C/jet_contract_definitions.txt'))
    results = [tuple(n.rsplit('.', 1)) for n in PR['results']]
    definitions = [tuple(n.rsplit('.', 1)) for n in PR['definitions']]
    if old_r & set(results) or old_d & set(definitions) or {m for m, _ in old_r} & set(MODULES):
        raise ValueError('nonfresh raw-program public inventory/printer rules')
    return {'_CoqProject': MANIFEST_SOURCES, '_CoqProject.jets': MANIFEST_SOURCES,
            'C/jet_public_theorems.txt': [' '.join(row) for row in results],
            'C/jet_contract_definitions.txt': [' '.join(row) for row in definitions]}


def once(text, old, new, label):
    if text.count(old) != 1:
        raise ValueError('unexpected raw admission boundary: ' + label)
    return text.replace(old, new, 1)


def script_changes():
    changes = {}
    original = (BASE / 'jet-coverage.py').read_text()
    names = ['simplicity_bitcoin_' + n.removeprefix('C.jet_bitcoin_hash_raw_program.bitcoin_').removesuffix('_raw_program_local_spec') for n in ENDPOINTS]
    extra = 'RAW_BITCOIN_HASH_JETS = ' + repr(set(names)) + '\n\n\n' + (HERE / 'coverage-boundary.py').read_text() + '\n\n'
    # Keep generated source deterministic rather than relying on set iteration.
    extra = extra.replace(repr(set(names)), '{' + ', '.join(repr(n) for n in sorted(names)) + '}')
    original = once(original, 'def inventory():\n', extra + 'def inventory():\n', 'exact selected raw targets')
    anchor = '        body = statement[1].strip() if statement else ""\n'
    check = ('        if family == "bitcoin" and name in RAW_BITCOIN_HASH_JETS:\n'
             '            if re.sub(r"\\s+", "", body) != raw_bitcoin_hash_contracts()[name]:\n'
             '                raise ValueError(f"coverage entry is not a direct canonical jet theorem: {module}.{theorem}")\n')
    changes['jet-coverage.py'] = once(original, anchor, anchor + check, 'complete raw endpoint type')
    original = (BASE / 'check-jets.sh').read_text()
    anchor = 'python3 scalar-lambda-integration/test-lambda-public.py "${JET_C_REPO:-..}" .\n'
    extra = ''.join('python3 ' + folder + '/' + script + ' "${JET_C_REPO:-..}"\n'
                    for folder in ['bitcoin-tapleaf-literal', 'bitcoin-raw-program-source']
                    for script in ['check-source.py', 'test-source.py'])
    changes['check-jets.sh'] = once(original, anchor, anchor + extra, 'mandatory raw/TapLeaf source gates')
    original = (BASE / 'audit-jet-contracts.sh').read_text()
    names = '|'.join(m.replace('.', '[.]') for m in MODULES)
    anchor = '         /^C\\.jet_secp_umul128_exec$/ {print "Require " $0 "."; next}\n'
    original = once(original, anchor, anchor + '         /^(' + names + ')$/ {print "Require " $0 "."; next}\n', 'Require-only new modules')
    lines = re.findall(r'(?m)^    explicit = .*$', original)
    if len(lines) != 1:
        raise ValueError('ambiguous explicit-printer rule')
    changes['audit-jet-contracts.sh'] = once(original, lines[0], lines[0] + ' || ($1 ~ /^(' + names + ')$/)', 'new types only')
    original = (BASE / 'test-jet-coverage.py').read_text()
    anchor = '        shutil.copy2(SOURCE / "scan-jet-proofs.py", project / "scan-jet-proofs.py")\n'
    extra = ('        (project / "bitcoin-raw-program-source").mkdir()\n'
             '        shutil.copy2(SOURCE / "bitcoin-raw-program-source/source-model.py", project / "bitcoin-raw-program-source/source-model.py")\n')
    original = once(original, anchor, anchor + extra, 'selected model in read-only coverage fixtures')
    marker = '    print("coverage tests passed: exact core/partial/application contracts; wrong function/global/logical environment and unknown/duplicate/helper/unaudited entries rejected")'
    changes['test-jet-coverage.py'] = once(original, marker, (HERE / 'coverage-fixtures.py').read_text() + marker, 'sixteen complete target fixtures')
    return changes


def assemble():
    if (HERE / 'ASSEMBLY.json').exists():
        raise ValueError('already assembled; continue recorded candidate')
    boundaries()
    before, index = s.input_map(), s.index_hash()
    work = Path(tempfile.mkdtemp(prefix='jet-bitcoin-raw-admission.', dir='/private/tmp'))
    subprocess.run(['cp', '-cR', str(BASE), str(work / 'Coq')], check=True)
    for name in ['C', 'Haskell']:
        (work / name).symlink_to(REPO / name, target_is_directory=True)
    extensions = additions()
    changes = {work / 'Coq' / n: (PROOF_TREE / 'Coq' / n).read_text() for n in NEW_SOURCES}
    for name, rows in extensions.items():
        text = (BASE / name).read_text()
        if not text.endswith('\n') or any(row in text.splitlines() for row in rows):
            raise ValueError('nonfresh normal inventory append')
        changes[work / 'Coq' / name] = text + '\n'.join(rows) + '\n'
    existing = {row[0] for row in normal.rows(BASE / 'C/jet_coverage.tsv')}
    if existing & {row.split()[0] for row in COVERAGE.splitlines()}:
        raise ValueError('raw hash jet already registered')
    changes[work / 'Coq/C/jet_coverage.tsv'] = (BASE / 'C/jet_coverage.tsv').read_text() + COVERAGE
    for name, text in guard_sources().items():
        if (BASE / name).exists():
            raise ValueError('new guard would overwrite inherited input')
        changes[work / 'Coq' / name] = text
    changes.update({work / 'Coq' / n: text for n, text in script_changes().items()})
    s.changed(changes)
    source_check(work)
    boundaries()
    if s.input_map() != before or s.index_hash() != index:
        raise ValueError('assembly changed main/index')
    meta = dict(candidate=str(work), predecessor_candidate=str(BASE_TREE),
        predecessor_input_sha256=PRED_REVIEW['candidate_input_sha256'],
        predecessor_review_sha256=s.sha((PRED / 'REVIEW.json').read_bytes()),
        proof_evidence_sha256=proof_evidence_hashes(), preparation_engine_sha256=s.sha(PREPARE_ENGINE.read_bytes()),
        main_inputs=before, main_input_sha256=main_fingerprint(before), baseline_inputs=baseline_inputs(),
        staged_patch_sha256=index, extensions=extensions, coverage_additions=COVERAGE, new_sources=NEW_SOURCES,
        baseline_metadata_sha256={n: s.sha((BASE / n).read_bytes()) for n in METADATA + SCRIPTS},
        source_sha256={m: s.sha((PROOF_TREE / 'Coq' / n).read_bytes()) for m, n in zip(MODULES, NEW_SOURCES)},
        coverage_added=16, full_acceptance=False)
    write(work / 'ASSEMBLY.json', meta)
    write(HERE / 'ASSEMBLY.json', meta)
    print(json.dumps(dict(candidate=str(work), modules=3, results=27, definitions=10,
                         proposed_coverage='436/533', main_changed=False)), flush=True)


if __name__ == '__main__':
    if sys.argv[1:] == ['assemble']:
        assemble()
    elif len(sys.argv) == 3 and sys.argv[1] == 'prepare':
        load('raw_normal_prepare_v2', PREPARE_ENGINE).prepare(SimpleNamespace(**globals()), Path(sys.argv[2]).resolve())
    else:
        raise ValueError('usage: admission.py assemble|prepare PRIVATE_TREE')
