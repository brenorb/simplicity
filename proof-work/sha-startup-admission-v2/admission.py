"""Register the complete checked SHA startup closure over reviewed normal449.

The object seed is the completed449 preparation, not the running447 audit.
Nine inherited sources remain byte-identical; one adapter source is added.
Ten modules and their entire public inventories are freshly registered.
Second candidate: derive the preparation header from the actual audit printer.
Assembly/preparation are not full acceptance or a main installation.
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
    module = importlib.util.module_from_spec(sp)
    sp.loader.exec_module(module)
    return module


prior = load('sha_admission_completed449', HERE.parent / 'elements-composite-admission/accept.py')
parent = prior.g
s, normal, snapshot_deps, write = parent.s, parent.normal, parent.snapshot_deps, parent.write
PRED = HERE.parent / 'elements-composite-admission'
PRED_REVIEW = json.loads((PRED / 'REVIEW.json').read_text())
PRED_META = json.loads((PRED / 'ASSEMBLY.json').read_text())
BASE_TREE = Path(PRED_META['candidate'])
BASE = BASE_TREE / 'Coq'
PROOF = HERE.parent / 'sha-canonical-startup'
COMPILED = json.loads((PROOF / 'RUN.json').read_text())
SUPPORT = json.loads((PROOF / 'SUPPORT-REPORT.json').read_text())
PROOF_TREE = Path(COMPILED['candidate'])
MODULES = SUPPORT['modules'] + COMPILED['modules']
# This shared-engine field means newly REGISTERED module sources. Nine are
# already inherited files and are separately required to stay byte-identical.
NEW_SOURCES = [m.replace('.', '/') + '.v' for m in MODULES]
MANIFEST_SOURCES = NEW_SOURCES
INHERITED_SOURCES, ADAPTER_SOURCE = NEW_SOURCES[:-1], NEW_SOURCES[-1]
SOURCE_FOLDERS = ['sha-canonical-startup-source']
GUARDS = [SOURCE_FOLDERS[0] + '/' + n for n in ['check-source.py', 'test-source.py', 'source-model.py']]
METADATA, SCRIPTS = parent.METADATA, parent.SCRIPTS
ENDPOINTS = COMPILED['endpoints']
PR = dict(results=SUPPORT['results'] + COMPILED['results'], definitions=SUPPORT['definitions'],
    closed_results=SUPPORT['closed_results'],
    dependencies=dict(SUPPORT['dependencies'], **COMPILED['dependencies']),
    staged_patch_sha256=COMPILED['staged_patch_sha256'])
COVERAGE_ADDED = 18
COVERAGE = ''.join('simplicity_' + e.rsplit('.', 1)[1].removesuffix('_canonical_startup_spec') +
    ' ' + e.rsplit('.', 1)[0] + ' ' + e.rsplit('.', 1)[1] + '\n' for e in ENDPOINTS)
PREPARE_ENGINE = HERE.parent / 'normal-delta-prepare-v3.py'
proof_review = load('sha_admission_actual_proof_review', PROOF / 'review.py')
ALLOWED_DEPENDENCIES = proof_review.INHERITED
ENDPOINT_DEPENDENCIES = {e: ALLOWED_DEPENDENCIES for e in ENDPOINTS}
REQUIRE_ONLY_MODULES = set(parent.MODULES) | parent.REQUIRE_ONLY_MODULES
once = parent.once


def guard_sources():
    return {n: (HERE.parent / n).read_text() for n in GUARDS}


def proof_source(module):
    if module not in MODULES:
        raise ValueError('unknown registered SHA module')
    return PROOF_TREE / 'Coq' / (module.replace('.', '/') + '.v')


def proof_sources():
    return {n: proof_source(m) for m, n in zip(MODULES, NEW_SOURCES)}


def proof_evidence_hashes():
    paths = [PROOF / n for n in ['RUN.json', 'KERNEL-RUN.json', 'CHECKED.json', 'SUPPORT-REPORT.json', 'EVIDENCE-REVIEW.json']]
    paths += [HERE.parent / SOURCE_FOLDERS[0] / 'SOURCE-REVIEW.json']
    return {str(p.relative_to(HERE.parent)): s.sha(p.read_bytes()) for p in paths}


def baseline_inputs():
    result = dict(parent.baseline_inputs())
    for n in parent.METADATA + parent.SCRIPTS + parent.NEW_SOURCES + parent.GUARDS:
        result['Coq/' + n] = s.sha((BASE / n).read_bytes())
    return result


def main_fingerprint(inputs):
    return parent.main_fingerprint(inputs)


def source_check(work):
    return {SOURCE_FOLDERS[0]: load('sha_admission_deployed_canonical_source',
        work / 'Coq' / SOURCE_FOLDERS[0] / 'check-source.py').check(work)}


def boundaries():
    if (BASE_TREE / 'AUDIT-RUN.json').exists() and not (BASE_TREE / 'TERMINAL.json').exists():
        raise ValueError('449 object seed has a live audit; do not copy its objects')
    if prior.reviewed(BASE_TREE) != PRED_REVIEW:
        raise ValueError('reviewed449 source/evidence changed')
    evidence = json.loads((PROOF / 'EVIDENCE-REVIEW.json').read_text())
    if (evidence['review'] != proof_review.review(PROOF_TREE) or
        evidence['checked_sha256'] != s.sha((PROOF / 'CHECKED.json').read_bytes()) or
        evidence['compile_sha256'] != s.sha((PROOF / 'RUN.json').read_bytes()) or
        evidence['kernel_launch_sha256'] != s.sha((PROOF / 'KERNEL-RUN.json').read_bytes()) or
        evidence['support_report_sha256'] != s.sha((PROOF / 'SUPPORT-REPORT.json').read_bytes()) or
        evidence['source_review_sha256'] != s.sha((HERE.parent / SOURCE_FOLDERS[0] / 'SOURCE-REVIEW.json').read_bytes()) or
        evidence['independent_evidence_review_complete'] is not True or
        evidence['normal_registration'] is not False or evidence['full_acceptance'] is not False or
        evidence['candidate_input_sha256'] != COMPILED['candidate_input_sha256']):
        raise ValueError('completed SHA execution/startup/kernel/source evidence differs')
    for name, digest in evidence['tools_sha256'].items():
        if s.sha((PROOF / name).read_bytes()) != digest:
            raise ValueError('reviewed SHA proof tool changed: ' + name)
    if set(evidence['checks']) != {'evidence-tests'}:
        raise ValueError('incomplete SHA evidence-test inventory')
    row, log = evidence['checks']['evidence-tests'], PROOF_TREE / 'evidence-tests.log'
    if (row != dict(command=[sys.executable, '-B', str(PROOF / 'test-review.py'), str(PROOF_TREE)],
                    exit_code=0, log_sha256=s.sha(log.read_bytes())) or
        (PROOF / log.name).read_bytes() != log.read_bytes()):
        raise ValueError('actual SHA evidence-test command/exit/log differs')
    if ((len(MODULES), len(set(MODULES)), len(PR['results']), len(PR['definitions']), len(PR['closed_results'])) != (10, 10, 123, 15, 12) or
        len(ENDPOINTS) != 18 or s.input_map() != PRED_META['main_inputs'] or s.index_hash() != PR['staged_patch_sha256']):
        raise ValueError('SHA registration scope or original main/index differs')
    main_fingerprint(s.input_map())
    for n in INHERITED_SOURCES:
        if (BASE / n).is_symlink() or (BASE / n).read_bytes() != proof_source(n[:-2].replace('/', '.')).read_bytes():
            raise ValueError('inherited startup support source would change: ' + n)
    if (MAIN / ADAPTER_SOURCE).exists() or (BASE / ADAPTER_SOURCE).exists():
        raise ValueError('new adapter source would overwrite inherited/untracked work')
    for m in MODULES:
        if proof_source(m).is_symlink():
            raise ValueError('shared mutable SHA proof source')


def additions():
    old_r = set(normal.rows(BASE / 'C/jet_public_theorems.txt'))
    old_d = set(normal.rows(BASE / 'C/jet_contract_definitions.txt'))
    results = [tuple(n.rsplit('.', 1)) for n in PR['results']]
    definitions = [tuple(n.rsplit('.', 1)) for n in PR['definitions']]
    if old_r & set(results) or old_d & set(definitions) or {m for m, _ in old_r} & set(MODULES):
        raise ValueError('nonfresh complete SHA public inventory')
    return {'_CoqProject': MANIFEST_SOURCES, '_CoqProject.jets': MANIFEST_SOURCES,
        'C/jet_public_theorems.txt': [' '.join(r) for r in results],
        'C/jet_contract_definitions.txt': [' '.join(r) for r in definitions]}


def script_changes():
    changes = {}
    names = sorted(row.split()[0] for row in COVERAGE.splitlines())
    text = (BASE / 'jet-coverage.py').read_text()
    extra = 'SHA_STARTUP_JETS = {' + ', '.join(repr(n) for n in names) + '}\n\n\n'
    extra += (HERE / 'coverage-boundary.py').read_text() + '\n\n'
    text = once(text, 'def inventory():\n', extra + 'def inventory():\n', 'eighteen exact SHA contracts')
    anchor = '        if family == "core":\n'
    extra = ('        if name in SHA_STARTUP_JETS:\n'
             '            contract = (rf"\\b(?:memcpy_model\\s*->\\s*)?sha_startup_(?:total|partial)_spec\\s+"\n'
             '                        rf"f_{re.escape(name)}\\b")\n')
    text = once(text, anchor, extra + anchor.replace('if family', 'elif family', 1), 'selected SHA contract family')
    anchor = '        body = statement[1].strip() if statement else ""\n'
    extra = ('        if name in SHA_STARTUP_JETS:\n'
             '            if re.sub(r"\\s+", "", body) != sha_startup_contracts()[name]:\n'
             '                raise ValueError(f"coverage entry is not a direct canonical jet theorem: {module}.{theorem}")\n')
    text = once(text, anchor, anchor + extra, 'whole named SHA theorem equality')
    changes['jet-coverage.py'] = once(text,
        'expected_arrows = 1 if family == "core" and conditional else 0',
        'expected_arrows = 1 if conditional and (family == "core" or name in SHA_STARTUP_JETS) else 0',
        'exactly the four named conditional Bitcoin helpers')
    text = (BASE / 'check-jets.sh').read_text()
    anchor = 'python3 elements-issuance-proofs-source/test-source.py "${JET_C_REPO:-..}"\n'
    extra = ''.join('python3 ' + SOURCE_FOLDERS[0] + '/' + n + ' "${JET_C_REPO:-..}"\n' for n in ['check-source.py', 'test-source.py'])
    changes['check-jets.sh'] = once(text, anchor, anchor + extra, 'mandatory canonical SHA source gates')
    text = (BASE / 'audit-jet-contracts.sh').read_text()
    pattern = '|'.join(m.replace('.', '[.]') for m in MODULES)
    anchor = '         /^C\\.jet_secp_umul128_exec$/ {print "Require " $0 "."; next}\n'
    text = once(text, anchor, anchor + '         /^(' + pattern + ')$/ {print "Require " $0 "."; next}\n', 'Require-only startup closure')
    lines = re.findall(r'(?m)^    explicit = .*$', text)
    if len(lines) != 1:
        raise ValueError('ambiguous full-contract printer rule')
    changes['audit-jet-contracts.sh'] = once(text, lines[0], lines[0] + ' || ($1 ~ /^(' + pattern + ')$/)', 'new SHA record printer only')
    text = (BASE / 'test-jet-coverage.py').read_text()
    anchor = '    assert sum(row["condition"] == "memcpy_model" for row in rows) == 104\n'
    extra = ('    assert sum(row["condition"] == "memcpy_model" for row in rows) == 121\n'
             '    assert sum(row["condition"] == "memcpy_model" for row in rows\n'
             '               if row["function"] not in coverage.SHA_STARTUP_JETS) == 104\n'
             '    assert {row["function"] for row in rows if row["function"] in coverage.SHA_STARTUP_JETS\n'
             '            and row["condition"] == "memcpy_model"} == coverage.SHA_STARTUP_JETS - {"simplicity_sha_256_block"}\n')
    text = once(text, anchor, extra, '104 inherited plus exactly seventeen new memcpy conditions')
    anchor = '        shutil.copy2(SOURCE / "scan-jet-proofs.py", project / "scan-jet-proofs.py")\n'
    folder = SOURCE_FOLDERS[0]
    extra = ('        (project / "' + folder + '").mkdir()\n'
             '        shutil.copy2(SOURCE / "' + folder + '/source-model.py", project / "' + folder + '/source-model.py")\n')
    text = once(text, anchor, anchor + extra, 'fixed SHA model in coverage fixtures')
    marker = '    print("coverage tests passed: exact core/partial/application contracts; wrong function/global/logical environment and unknown/duplicate/helper/unaudited entries rejected")'
    changes['test-jet-coverage.py'] = once(text, marker, (HERE / 'coverage-fixtures.py').read_text() + marker, 'entire SHA contract mutations')
    return changes


def assemble():
    if (HERE / 'ASSEMBLY.json').exists():
        raise ValueError('normal467 already assembled; continue its recorded tree')
    boundaries()
    before, index = s.input_map(), s.index_hash()
    work = Path(tempfile.mkdtemp(prefix='jet-sha-startup-admission-v2.', dir='/private/tmp'))
    subprocess.run(['cp', '-cR', str(BASE), str(work / 'Coq')], check=True)
    for n in ['C', 'Haskell']:
        (work / n).symlink_to(REPO / n, target_is_directory=True)
    paths = load('sha_startup_source_inventory', HERE.parent / 'elements-pegin-normal/review.py').source_paths
    if paths(work / 'Coq') != paths(BASE):
        raise ValueError('completed449 source inventory copy differs')
    changes = {work / 'Coq' / ADAPTER_SOURCE: proof_source(COMPILED['modules'][0]).read_text()}
    extensions = additions()
    for n, rows in extensions.items():
        text = (BASE / n).read_text()
        if not text.endswith('\n') or any(r in text.splitlines() for r in rows):
            raise ValueError('nonfresh complete startup manifest/public registration')
        changes[work / 'Coq' / n] = text + '\n'.join(rows) + '\n'
    if {r[0] for r in normal.rows(BASE / 'C/jet_coverage.tsv')} & {r.split()[0] for r in COVERAGE.splitlines()}:
        raise ValueError('SHA endpoint already counted')
    changes[work / 'Coq/C/jet_coverage.tsv'] = (BASE / 'C/jet_coverage.tsv').read_text() + COVERAGE
    for n, text in guard_sources().items():
        if (BASE / n).exists():
            raise ValueError('new canonical SHA gate would overwrite inherited work')
        changes[work / 'Coq' / n] = text
    changes.update({work / 'Coq' / n: text for n, text in script_changes().items()})
    s.changed(changes)
    source_check(work)
    boundaries()
    if s.input_map() != before or s.index_hash() != index:
        raise ValueError('SHA assembly changed main/index')
    meta = dict(candidate=str(work), predecessor_candidate=str(BASE_TREE),
        predecessor_input_sha256=PRED_REVIEW['candidate_input_sha256'],
        predecessor_review_sha256=s.sha((PRED / 'REVIEW.json').read_bytes()),
        proof_evidence_sha256=proof_evidence_hashes(), preparation_engine_sha256=s.sha(PREPARE_ENGINE.read_bytes()),
        main_inputs=before, main_input_sha256=main_fingerprint(before), baseline_inputs=baseline_inputs(),
        staged_patch_sha256=index, extensions=extensions, coverage_additions=COVERAGE, new_sources=NEW_SOURCES,
        baseline_metadata_sha256={n: s.sha((BASE / n).read_bytes()) for n in METADATA + SCRIPTS},
        source_sha256={m: s.sha(proof_source(m).read_bytes()) for m in MODULES}, coverage_added=18, full_acceptance=False)
    write(work / 'ASSEMBLY.json', meta)
    write(HERE / 'ASSEMBLY.json', meta)
    print(json.dumps(dict(candidate=str(work), modules=10, results=123, definitions=15,
        inherited_support_files_changed=0, new_v_files=1, proposed_coverage='467/533', main_changed=False)), flush=True)


if __name__ == '__main__':
    if sys.argv[1:] == ['assemble']:
        assemble()
    elif len(sys.argv) == 3 and sys.argv[1] == 'prepare':
        load('normal467_prepare_v3', PREPARE_ENGINE).prepare(SimpleNamespace(**globals()), Path(sys.argv[2]).resolve())
    else:
        raise ValueError('usage: admission.py assemble|prepare PRIVATE_TREE')
