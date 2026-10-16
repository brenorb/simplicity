"""Prepare four Elements program endpoints over the reviewed443 source state.

Clone only the completed tapenv proof tree. Overlay the live443 predecessor's
frozen sources, never its objects. Preparation is not full acceptance; real443
full success is required before a later combined audit/installation.
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


prior = load('context_reviewed443', HERE.parent / 'elements-stream-admission/accept.py')
parent = prior.g
s, normal, snapshot_deps, write = parent.s, parent.normal, parent.snapshot_deps, parent.write
PRED = HERE.parent / 'elements-stream-admission'
PRED_REVIEW = json.loads((PRED / 'REVIEW.json').read_text())
PRED_META = json.loads((PRED / 'ASSEMBLY.json').read_text())
BASE_TREE = Path(PRED_META['candidate'])
BASE = BASE_TREE / 'Coq'
PARTS = ['elements-annexes', 'elements-tapleaf', 'elements-tapenv', 'elements-outpoints']
RECORDS = {n: json.loads((HERE.parent / n / 'RUN.json').read_text()) for n in PARTS}
SEED = Path(RECORDS['elements-tapenv']['candidate'])
MODULES = [m for n in PARTS for m in RECORDS[n]['modules']]
NEW_SOURCES = [m.replace('.', '/') + '.v' for m in MODULES]
MANIFEST_SOURCES = NEW_SOURCES
SOURCE_FOLDERS = [n + '-source' for n in PARTS]
GUARDS = [n + '/' + f for n in SOURCE_FOLDERS for f in ['check-source.py', 'test-source.py', 'source-model.py']]
METADATA, SCRIPTS = parent.METADATA, parent.SCRIPTS
ENDPOINTS = [e for n in PARTS for e in RECORDS[n]['endpoints']]
PR = dict(results=[e for n in PARTS for e in RECORDS[n]['results']],
    definitions=[e for n in PARTS for e in RECORDS[n]['definitions']],
    closed_results=[e for n in PARTS for e in RECORDS[n]['closed_results']],
    dependencies={e: d for n in PARTS for e, d in RECORDS[n]['dependencies'].items()},
    staged_patch_sha256=PRED_META['staged_patch_sha256'])
COVERAGE_ADDED = 4
COVERAGE = ''.join('simplicity_' + e.rsplit('.', 1)[1].removeprefix('elements_').removesuffix('_program_local_spec') +
    ' ' + e.rsplit('.', 1)[0] + ' ' + e.rsplit('.', 1)[1] + '\n' for e in ENDPOINTS)
PREPARE_ENGINE = HERE.parent / 'normal-delta-prepare-v2.py'
ALLOWED_DEPENDENCIES = s.SIX
ENDPOINT_DEPENDENCIES = {e: s.SIX for e in ENDPOINTS}
REQUIRE_ONLY_MODULES = set(parent.MODULES) | parent.REQUIRE_ONLY_MODULES


def guard_sources():
    return {n: (HERE.parent / n).read_text() for n in GUARDS}


def proof_evidence_hashes():
    paths = [HERE.parent / n / f for n in PARTS for f in
             ['RUN.json', 'KERNEL-RUN.json', 'CHECKED.json', 'EVIDENCE-REVIEW.json']]
    paths += [HERE.parent / n / 'SOURCE-REVIEW.json' for n in SOURCE_FOLDERS]
    return {str(p.relative_to(HERE.parent)): s.sha(p.read_bytes()) for p in paths}


def baseline_inputs():
    result = dict(parent.baseline_inputs())
    for n in parent.METADATA + parent.SCRIPTS + parent.NEW_SOURCES + parent.GUARDS:
        result['Coq/' + n] = s.sha((BASE / n).read_bytes())
    return result


def main_fingerprint(inputs):
    return parent.main_fingerprint(inputs)


def proof_source(module):
    records = [r for r in RECORDS.values() if module in r['modules']]
    if len(records) != 1:
        raise ValueError('ambiguous new Elements source owner')
    return Path(records[0]['candidate']) / 'Coq' / (module.replace('.', '/') + '.v')


def proof_sources():
    return {n: proof_source(m) for m, n in zip(MODULES, NEW_SOURCES)}


def source_check(work):
    return {n: load('context_source_' + n.replace('-', '_'), work / 'Coq' / n / 'check-source.py').check(work)
            for n in SOURCE_FOLDERS}


def boundaries():
    for n in PARTS:
        for f in ['CHECKED.json', 'EVIDENCE-REVIEW.json']:
            if not (HERE.parent / n / f).is_file():
                raise ValueError('complete ' + n + ' kernel/evidence review required; poll the existing process')
    if prior.reviewed(BASE_TREE) != PRED_REVIEW:
        raise ValueError('reviewed443 source/evidence changed')
    for n in PARTS:
        folder = HERE.parent / n
        compiled = RECORDS[n]
        work = Path(compiled['candidate'])
        v = load('context_complete_' + n.replace('-', '_'), folder / 'review.py')
        checked = json.loads((folder / 'CHECKED.json').read_text())
        evidence = json.loads((folder / 'EVIDENCE-REVIEW.json').read_text())
        if (evidence['review'] != v.review(work) or checked['recursive_kernel_check'] is not True or
            evidence['checked_sha256'] != s.sha((folder / 'CHECKED.json').read_bytes()) or
            evidence['compile_sha256'] != s.sha((folder / 'RUN.json').read_bytes()) or
            evidence['kernel_launch_sha256'] != s.sha((folder / 'KERNEL-RUN.json').read_bytes()) or
            evidence['source_review_sha256'] != s.sha((HERE.parent / (n + '-source') / 'SOURCE-REVIEW.json').read_bytes()) or
            evidence['candidate_input_sha256'] != compiled['candidate_input_sha256'] or
            evidence['normal_registration'] is not False or evidence['full_acceptance'] is not False):
            raise ValueError('complete Elements proof/source/kernel review differs: ' + n)
        for name, digest in evidence['tools_sha256'].items():
            if s.sha((folder / name).read_bytes()) != digest:
                raise ValueError('reviewed Elements tool changed: ' + n + '/' + name)
        row = evidence['checks']['evidence-tests']
        if (set(evidence['checks']) != {'evidence-tests'} or
            row['command'] != [sys.executable, '-B', str(folder / 'test-review.py'), str(work)] or row['exit_code'] != 0 or
            row['log_sha256'] != s.sha((work / 'evidence-tests.log').read_bytes()) or
            (folder / 'evidence-tests.log').read_bytes() != (work / 'evidence-tests.log').read_bytes()):
            raise ValueError('complete Elements evidence-test command/exit/log differs')
    if ((len(MODULES), len(set(MODULES)), len(PR['results']), len(PR['definitions']), len(PR['closed_results'])) != (5, 5, 31, 22, 15) or
        len(ENDPOINTS) != 4 or s.input_map() != PRED_META['main_inputs'] or s.index_hash() != PR['staged_patch_sha256']):
        raise ValueError('four-jet proof scope or original main/index differs')
    main_fingerprint(s.input_map())
    for module, name in zip(MODULES, NEW_SOURCES):
        if (MAIN / name).exists() or (BASE / name).exists() or proof_source(module).is_symlink():
            raise ValueError('new source would overwrite inherited/untracked proof')


def additions():
    old_r = set(normal.rows(BASE / 'C/jet_public_theorems.txt'))
    old_d = set(normal.rows(BASE / 'C/jet_contract_definitions.txt'))
    results = [tuple(n.rsplit('.', 1)) for n in PR['results']]
    definitions = [tuple(n.rsplit('.', 1)) for n in PR['definitions']]
    if old_r & set(results) or old_d & set(definitions) or {m for m, _ in old_r} & set(MODULES):
        raise ValueError('nonfresh Elements context public inventory/printer rules')
    return {'_CoqProject': MANIFEST_SOURCES, '_CoqProject.jets': MANIFEST_SOURCES,
        'C/jet_public_theorems.txt': [' '.join(r) for r in results],
        'C/jet_contract_definitions.txt': [' '.join(r) for r in definitions]}


def script_changes():
    once, changes = parent.parent.once, {}
    names = sorted(row.split()[0] for row in COVERAGE.splitlines())
    text = (BASE / 'jet-coverage.py').read_text()
    extra = 'ELEMENTS_CONTEXT_JETS = {' + ', '.join(repr(n) for n in names) + '}\n\n\n'
    extra += (HERE / 'coverage-boundary.py').read_text() + '\n\n'
    text = once(text, 'def inventory():\n', extra + 'def inventory():\n', 'four exact context targets')
    anchor = '            if name in ELEMENTS_STREAM_JETS:\n'
    extra = ('            if name in ELEMENTS_CONTEXT_JETS:\n'
             '                contract = (rf"\\bapplication_jet_local_spec_sep\\s+f_{re.escape(name)}\\s+"\n'
             '                            r"elements_ge\\s+Elements\\.env\\s+Ty\\.Unit\\s+Word256\\b")\n')
    text = once(text, anchor, extra + anchor.replace('if name', 'elif name', 1), 'selected context family')
    anchor = '        body = statement[1].strip() if statement else ""\n'
    extra = ('        if family == "elements" and name in ELEMENTS_CONTEXT_JETS:\n'
             '            if re.sub(r"\\s+", "", body) != elements_context_contracts()[name]:\n'
             '                raise ValueError(f"coverage entry is not a direct canonical jet theorem: {module}.{theorem}")\n')
    changes['jet-coverage.py'] = once(text, anchor, anchor + extra, 'entire context theorem')
    text = (BASE / 'check-jets.sh').read_text()
    anchor = 'python3 elements-stream-source/test-source.py "${JET_C_REPO:-..}"\n'
    extra = ''.join('python3 ' + n + '/' + f + ' "${JET_C_REPO:-..}"\n'
                    for n in SOURCE_FOLDERS for f in ['check-source.py', 'test-source.py'])
    changes['check-jets.sh'] = once(text, anchor, anchor + extra, 'mandatory context source gates')
    text = (BASE / 'audit-jet-contracts.sh').read_text()
    pattern = '|'.join(m.replace('.', '[.]') for m in MODULES)
    anchor = '         /^C\\.jet_secp_umul128_exec$/ {print "Require " $0 "."; next}\n'
    text = once(text, anchor, anchor + '         /^(' + pattern + ')$/ {print "Require " $0 "."; next}\n', 'Require-only context modules')
    lines = re.findall(r'(?m)^    explicit = .*$', text)
    if len(lines) != 1:
        raise ValueError('ambiguous explicit-printer rule')
    changes['audit-jet-contracts.sh'] = once(text, lines[0], lines[0] + ' || ($1 ~ /^(' + pattern + ')$/)', 'new types only')
    text = (BASE / 'test-jet-coverage.py').read_text()
    anchor = '        shutil.copy2(SOURCE / "scan-jet-proofs.py", project / "scan-jet-proofs.py")\n'
    extra = ''.join('        (project / "' + n + '").mkdir()\n'
                    '        shutil.copy2(SOURCE / "' + n + '/source-model.py", project / "' + n + '/source-model.py")\n'
                    for n in SOURCE_FOLDERS)
    text = once(text, anchor, anchor + extra, 'fixed context models in coverage fixtures')
    marker = '    print("coverage tests passed: exact core/partial/application contracts; wrong function/global/logical environment and unknown/duplicate/helper/unaudited entries rejected")'
    changes['test-jet-coverage.py'] = once(text, marker, (HERE / 'coverage-fixtures.py').read_text() + marker, 'four complete context fixtures')
    return changes


def assemble():
    if (HERE / 'ASSEMBLY.json').exists():
        raise ValueError('normal447 already assembled; continue the recorded candidate')
    boundaries()
    before, index = s.input_map(), s.index_hash()
    work = Path(tempfile.mkdtemp(prefix='jet-elements-context-admission.', dir='/private/tmp'))
    subprocess.run(['cp', '-cR', str(SEED / 'Coq'), str(work / 'Coq')], check=True)
    for n in ['C', 'Haskell']:
        (work / n).symlink_to(REPO / n, target_is_directory=True)
    paths = load('context_source_inventory', HERE.parent / 'elements-pegin-normal/review.py').source_paths
    expected_seed_extra = {'C/jet_elements_tapleaf_hash_program.v', 'C/jet_elements_tap_env_hash_program.v'}
    if (paths(work / 'Coq') - paths(BASE) != expected_seed_extra or
        paths(BASE) - paths(work / 'Coq') != set(parent.parent.NEW_SOURCES + parent.parent.GUARDS + parent.GUARDS)):
        raise ValueError('unexpected completed-seed/live443 source-only inventory')
    changes = {work / 'Coq' / n: (BASE / n).read_text() for n in paths(BASE)}
    changes.update({work / 'Coq' / n: proof_source(m).read_text() for m, n in zip(MODULES, NEW_SOURCES)})
    extensions = additions()
    for n, rows in extensions.items():
        text = (BASE / n).read_text()
        if not text.endswith('\n') or any(r in text.splitlines() for r in rows):
            raise ValueError('nonfresh normal447 inventory append')
        changes[work / 'Coq' / n] = text + '\n'.join(rows) + '\n'
    if {r[0] for r in normal.rows(BASE / 'C/jet_coverage.tsv')} & {r.split()[0] for r in COVERAGE.splitlines()}:
        raise ValueError('context jet already registered')
    changes[work / 'Coq/C/jet_coverage.tsv'] = (BASE / 'C/jet_coverage.tsv').read_text() + COVERAGE
    for n, text in guard_sources().items():
        if (BASE / n).exists():
            raise ValueError('new context guard would overwrite inherited source')
        changes[work / 'Coq' / n] = text
    changes.update({work / 'Coq' / n: t for n, t in script_changes().items()})
    s.changed(changes)
    source_check(work)
    boundaries()
    if s.input_map() != before or s.index_hash() != index:
        raise ValueError('normal447 assembly changed main/index')
    meta = dict(candidate=str(work), predecessor_candidate=str(BASE_TREE),
        predecessor_input_sha256=PRED_REVIEW['candidate_input_sha256'],
        predecessor_review_sha256=s.sha((PRED / 'REVIEW.json').read_bytes()),
        proof_evidence_sha256=proof_evidence_hashes(), preparation_engine_sha256=s.sha(PREPARE_ENGINE.read_bytes()),
        main_inputs=before, main_input_sha256=main_fingerprint(before), baseline_inputs=baseline_inputs(),
        staged_patch_sha256=index, extensions=extensions, coverage_additions=COVERAGE, new_sources=NEW_SOURCES,
        baseline_metadata_sha256={n: s.sha((BASE / n).read_bytes()) for n in METADATA + SCRIPTS},
        source_sha256={m: s.sha(proof_source(m).read_bytes()) for m in MODULES}, coverage_added=4, full_acceptance=False)
    write(work / 'ASSEMBLY.json', meta)
    write(HERE / 'ASSEMBLY.json', meta)
    print(json.dumps(dict(candidate=str(work), modules=5, results=31, definitions=22,
        proposed_coverage='447/533', live_predecessor_objects_copied=0, main_changed=False)), flush=True)


if __name__ == '__main__':
    if sys.argv[1:] == ['assemble']:
        assemble()
    elif len(sys.argv) == 3 and sys.argv[1] == 'prepare':
        load('normal447_prepare_v2', PREPARE_ENGINE).prepare(SimpleNamespace(**globals()), Path(sys.argv[2]).resolve())
    else:
        raise ValueError('usage: admission.py assemble|prepare PRIVATE_TREE')
