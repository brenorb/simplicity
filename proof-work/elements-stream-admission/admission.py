"""Normal443 source delta over reviewed436, seeded from completed proof objects.

The live436 audit contributes only frozen sources/metadata, never its mutable
object cache. Real436 full acceptance is required before a later combined443
full audit or installation; isolated preparation does not invent that result.
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


prior = load('elements_stream_reviewed436', HERE.parent / 'bitcoin-raw-admission/accept.py')
parent = prior.g
s, normal, snapshot_deps, write = parent.s, parent.normal, parent.snapshot_deps, parent.write
PRED = HERE.parent / 'bitcoin-raw-admission'
PRED_REVIEW = json.loads((PRED / 'REVIEW.json').read_text())
PRED_META = json.loads((PRED / 'ASSEMBLY.json').read_text())
BASE_TREE = Path(PRED_META['candidate'])
BASE = BASE_TREE / 'Coq'
PROOF = HERE.parent / 'elements-stream'
PR = json.loads((PROOF / 'CHECKED.json').read_text())
PROOF_TREE = Path(PR['candidate'])
SOURCE = HERE.parent / 'elements-stream-source'
MODULES, NEW_SOURCES = PR['modules'], PR['new_sources']
MANIFEST_SOURCES = [m.replace('.', '/') + '.v' for m in MODULES]
GUARDS = ['elements-stream-source/' + n for n in ['check-source.py', 'test-source.py', 'source-model.py']]
METADATA, SCRIPTS = parent.METADATA, parent.SCRIPTS
COVERAGE_ADDED = 7
ENDPOINTS = PR['endpoints']
COVERAGE = ''.join('simplicity_' + n.removeprefix('C.jet_elements_words_hash_program.elements_').removesuffix('_program_local_spec') +
                   ' C.jet_elements_words_hash_program ' + n.rsplit('.', 1)[1] + '\n' for n in ENDPOINTS)
PREPARE_ENGINE = HERE.parent / 'normal-delta-prepare-v2.py'
ALLOWED_DEPENDENCIES = s.SIX
ENDPOINT_DEPENDENCIES = {n: s.SIX for n in ENDPOINTS}
REQUIRE_ONLY_MODULES = set(parent.MODULES) | parent.REQUIRE_ONLY_MODULES


def guard_sources():
    return {n: (HERE.parent / n).read_text() for n in GUARDS}


def proof_evidence_hashes():
    paths = [PROOF / n for n in ['READER-CHECKED.json', 'RUN.json', 'KERNEL-RUN.json', 'CHECKED.json', 'EVIDENCE-REVIEW.json']]
    paths += [SOURCE / 'SOURCE-REVIEW.json']
    return {str(p.relative_to(HERE.parent)): s.sha(p.read_bytes()) for p in paths}


def baseline_inputs():
    result = dict(parent.baseline_inputs())
    for name in parent.METADATA + parent.SCRIPTS + parent.NEW_SOURCES + parent.GUARDS:
        result['Coq/' + name] = s.sha((BASE / name).read_bytes())
    return result


def main_fingerprint(inputs):
    # Historical actual-main420 is distinct from the reviewed private436
    # metadata/source predecessor. Neither map is accepted by approximation.
    return parent.main_fingerprint(inputs)


def source_check(work):
    return load('normal443_elements_source', work / 'Coq/elements-stream-source/check-source.py').check(work)


def boundaries():
    if prior.reviewed(BASE_TREE) != PRED_REVIEW:
        raise ValueError('reviewed436 predecessor source/evidence changed')
    v = load('normal443_completed_elements_proof', PROOF / 'review.py')
    evidence = json.loads((PROOF / 'EVIDENCE-REVIEW.json').read_text())
    if (evidence['review'] != v.review(PROOF_TREE) or
        evidence['checked_sha256'] != s.sha((PROOF / 'CHECKED.json').read_bytes()) or
        evidence['compile_sha256'] != s.sha((PROOF / 'RUN.json').read_bytes()) or
        evidence['reader_checkpoint_sha256'] != s.sha((PROOF / 'READER-CHECKED.json').read_bytes()) or
        evidence['kernel_launch_sha256'] != s.sha((PROOF / 'KERNEL-RUN.json').read_bytes()) or
        evidence['source_review_sha256'] != s.sha((SOURCE / 'SOURCE-REVIEW.json').read_bytes()) or
        evidence['candidate_input_sha256'] != PR['candidate_input_sha256'] or
        evidence['normal_registration'] is not False or evidence['full_acceptance'] is not False):
        raise ValueError('completed Elements proof/source/kernel review differs')
    for name, digest in evidence['tools_sha256'].items():
        if s.sha((PROOF / name).read_bytes()) != digest:
            raise ValueError('reviewed Elements proof tool changed')
    expected = [sys.executable, '-B', str(PROOF / 'test-review.py'), str(PROOF_TREE)]
    row = evidence['checks']['evidence-tests']
    if (set(evidence['checks']) != {'evidence-tests'} or row['command'] != expected or row['exit_code'] != 0 or
        row['log_sha256'] != s.sha((PROOF_TREE / 'evidence-tests.log').read_bytes()) or
        (PROOF / 'evidence-tests.log').read_bytes() != (PROOF_TREE / 'evidence-tests.log').read_bytes()):
        raise ValueError('completed Elements evidence-test command/exit/log differs')
    if ((len(MODULES), len(NEW_SOURCES), len(PR['results']), len(PR['definitions'])) != (2, 2, 36, 10) or
        s.input_map() != parent.baseline_inputs() or s.index_hash() != PR['staged_patch_sha256']):
        raise ValueError('main/index or complete Elements proof scope differs')
    for name in NEW_SOURCES:
        if (MAIN / name).exists() or (BASE / name).exists():
            raise ValueError('new Elements proof would overwrite inherited/untracked source')


def additions():
    old_r = set(normal.rows(BASE / 'C/jet_public_theorems.txt'))
    old_d = set(normal.rows(BASE / 'C/jet_contract_definitions.txt'))
    results = [tuple(n.rsplit('.', 1)) for n in PR['results']]
    definitions = [tuple(n.rsplit('.', 1)) for n in PR['definitions']]
    if old_r & set(results) or old_d & set(definitions) or {m for m, _ in old_r} & set(MODULES):
        raise ValueError('nonfresh Elements stream public inventory/printer rules')
    return {'_CoqProject': MANIFEST_SOURCES, '_CoqProject.jets': MANIFEST_SOURCES,
            'C/jet_public_theorems.txt': [' '.join(row) for row in results],
            'C/jet_contract_definitions.txt': [' '.join(row) for row in definitions]}


def script_changes():
    once = parent.once
    changes = {}
    original = (BASE / 'jet-coverage.py').read_text()
    names = sorted(row.split()[0] for row in COVERAGE.splitlines())
    extra = 'ELEMENTS_STREAM_JETS = {' + ', '.join(repr(n) for n in names) + '}\n\n\n'
    extra += (HERE / 'coverage-boundary.py').read_text() + '\n\n'
    original = once(original, 'def inventory():\n', extra + 'def inventory():\n', 'seven exact stream targets')
    anchor = '            if name in {"simplicity_input_script_hash", "simplicity_input_script_sig_hash", "simplicity_issuance_asset_proof", "simplicity_issuance_token_proof"}:\n'
    extra = ('            if name in ELEMENTS_STREAM_JETS:\n'
             '                contract = (rf"\\bapplication_jet_local_spec_sep\\s+f_{re.escape(name)}\\s+"\n'
             '                            r"elements_ge\\s+Elements\\.env\\s+Ty\\.Unit\\s+Word256\\b")\n')
    original = once(original, anchor, extra + anchor.replace('if name', 'elif name', 1), 'selected Elements contract family')
    anchor = '        body = statement[1].strip() if statement else ""\n'
    extra = ('        if family == "elements" and name in ELEMENTS_STREAM_JETS:\n'
             '            if re.sub(r"\\s+", "", body) != elements_stream_contracts()[name]:\n'
             '                raise ValueError(f"coverage entry is not a direct canonical jet theorem: {module}.{theorem}")\n')
    changes['jet-coverage.py'] = once(original, anchor, anchor + extra, 'entire Elements stream theorem')
    original = (BASE / 'check-jets.sh').read_text()
    anchor = 'python3 bitcoin-raw-program-source/test-source.py "${JET_C_REPO:-..}"\n'
    extra = ''.join('python3 elements-stream-source/' + n + ' "${JET_C_REPO:-..}"\n' for n in ['check-source.py', 'test-source.py'])
    changes['check-jets.sh'] = once(original, anchor, anchor + extra, 'mandatory Elements stream source gates')
    original = (BASE / 'audit-jet-contracts.sh').read_text()
    names = '|'.join(m.replace('.', '[.]') for m in MODULES)
    anchor = '         /^C\\.jet_secp_umul128_exec$/ {print "Require " $0 "."; next}\n'
    original = once(original, anchor, anchor + '         /^(' + names + ')$/ {print "Require " $0 "."; next}\n', 'Require-only new stream modules')
    lines = re.findall(r'(?m)^    explicit = .*$', original)
    if len(lines) != 1:
        raise ValueError('ambiguous inherited explicit-printer rule')
    changes['audit-jet-contracts.sh'] = once(original, lines[0], lines[0] + ' || ($1 ~ /^(' + names + ')$/)', 'new types only')
    original = (BASE / 'test-jet-coverage.py').read_text()
    anchor = '        shutil.copy2(SOURCE / "scan-jet-proofs.py", project / "scan-jet-proofs.py")\n'
    extra = ('        (project / "elements-stream-source").mkdir()\n'
             '        shutil.copy2(SOURCE / "elements-stream-source/source-model.py", project / "elements-stream-source/source-model.py")\n')
    original = once(original, anchor, anchor + extra, 'Elements model in coverage fixtures')
    marker = '    print("coverage tests passed: exact core/partial/application contracts; wrong function/global/logical environment and unknown/duplicate/helper/unaudited entries rejected")'
    changes['test-jet-coverage.py'] = once(original, marker, (HERE / 'coverage-fixtures.py').read_text() + marker, 'seven complete stream contract fixtures')
    return changes


def assemble():
    if (HERE / 'ASSEMBLY.json').exists():
        raise ValueError('normal443 already assembled; continue recorded candidate')
    boundaries()
    before, index = s.input_map(), s.index_hash()
    work = Path(tempfile.mkdtemp(prefix='jet-elements-stream-admission.', dir='/private/tmp'))
    # Only the completed Elements proof tree contributes objects.
    subprocess.run(['cp', '-cR', str(PROOF_TREE / 'Coq'), str(work / 'Coq')], check=True)
    for name in ['C', 'Haskell']:
        (work / name).symlink_to(REPO / name, target_is_directory=True)
    paths = load('normal443_source_inventory', HERE.parent / 'elements-pegin-normal/review.py').source_paths
    if (paths(work / 'Coq') - paths(BASE) != set(NEW_SOURCES) or
        paths(BASE) - paths(work / 'Coq') != set(parent.NEW_SOURCES + parent.GUARDS)):
        raise ValueError('unexpected completed seed/live436 source-only inventory')
    # Overlay source text only, never live436 .vo/.glob/object outputs.
    changes = {work / 'Coq' / name: (BASE / name).read_text() for name in paths(BASE)}
    extensions = additions()
    for name, rows in extensions.items():
        text = (BASE / name).read_text()
        if not text.endswith('\n') or any(row in text.splitlines() for row in rows):
            raise ValueError('nonfresh normal443 public inventory append')
        changes[work / 'Coq' / name] = text + '\n'.join(rows) + '\n'
    existing = {row[0] for row in normal.rows(BASE / 'C/jet_coverage.tsv')}
    if existing & {row.split()[0] for row in COVERAGE.splitlines()}:
        raise ValueError('Elements stream jet already registered')
    changes[work / 'Coq/C/jet_coverage.tsv'] = (BASE / 'C/jet_coverage.tsv').read_text() + COVERAGE
    for name, text in guard_sources().items():
        if (BASE / name).exists():
            raise ValueError('new stream guard would overwrite inherited source')
        changes[work / 'Coq' / name] = text
    changes.update({work / 'Coq' / n: text for n, text in script_changes().items()})
    s.changed(changes)
    source_check(work)
    boundaries()
    if s.input_map() != before or s.index_hash() != index:
        raise ValueError('normal443 assembly changed main/index')
    meta = dict(candidate=str(work), predecessor_candidate=str(BASE_TREE),
        predecessor_input_sha256=PRED_REVIEW['candidate_input_sha256'],
        predecessor_review_sha256=s.sha((PRED / 'REVIEW.json').read_bytes()),
        proof_evidence_sha256=proof_evidence_hashes(), preparation_engine_sha256=s.sha(PREPARE_ENGINE.read_bytes()),
        main_inputs=before, main_input_sha256=main_fingerprint(before), baseline_inputs=baseline_inputs(),
        staged_patch_sha256=index, extensions=extensions, coverage_additions=COVERAGE, new_sources=NEW_SOURCES,
        baseline_metadata_sha256={n: s.sha((BASE / n).read_bytes()) for n in METADATA + SCRIPTS},
        source_sha256={m: PR['source_sha256'][m] for m in MODULES}, coverage_added=7, full_acceptance=False)
    write(work / 'ASSEMBLY.json', meta)
    write(HERE / 'ASSEMBLY.json', meta)
    print(json.dumps(dict(candidate=str(work), modules=2, results=36, definitions=10,
                         proposed_coverage='443/533', live_predecessor_objects_copied=0, main_changed=False)), flush=True)


if __name__ == '__main__':
    if sys.argv[1:] == ['assemble']:
        assemble()
    elif len(sys.argv) == 3 and sys.argv[1] == 'prepare':
        load('normal443_prepare_v2', PREPARE_ENGINE).prepare(SimpleNamespace(**globals()), Path(sys.argv[2]).resolve())
    else:
        raise ValueError('usage: admission.py assemble|prepare PRIVATE_TREE')
