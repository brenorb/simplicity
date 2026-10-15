"""Normal lbtc_asset candidate over the source-frozen reviewed 401 predecessor."""
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


parent = load('lbtc_normal_predecessor', HERE.parent / 'elements-tap-getters-admission/admission.py')
s, normal, snapshot_deps = parent.s, parent.normal, parent.snapshot_deps
PRED, PROOF = HERE.parent / 'elements-tap-getters-admission', HERE.parent / 'elements-lbtc-asset'
PRED_META = json.loads((PRED / 'ASSEMBLY.json').read_text())
PRED_REVIEW = json.loads((PRED / 'REVIEW.json').read_text())
PR = json.loads((PROOF / 'PREPARATION.json').read_text())
BASE_TREE, PROOF_TREE = Path(PRED_META['candidate']), Path(PR['candidate'])
BASE = BASE_TREE / 'Coq'
MODULES = ['C.jet_u32_local_init', 'C.jet_elements_lbtc_asset_exec', 'C.jet_elements_lbtc_asset_local']
NEW_SOURCES = [m.replace('.', '/') + '.v' for m in MODULES]
GUARDS = ['elements-lbtc-asset/' + n for n in ['check-source.py', 'test-source.py']]
METADATA, SCRIPTS = parent.METADATA, parent.SCRIPTS
COVERAGE_ADDED = 1
COVERAGE = 'simplicity_lbtc_asset C.jet_elements_lbtc_asset_local elements_lbtc_asset_local_spec\n'
write = parent.write
PREPARE_ENGINE = HERE.parent / 'normal-delta-prepare.py'


def baseline_inputs():
    result = dict(PRED_META['baseline_inputs'])
    result.update({'Coq/' + n: s.sha((BASE / n).read_bytes()) for n in
                   parent.METADATA + parent.SCRIPTS + parent.GUARDS + parent.NEW_SOURCES + parent.MODIFIED_SOURCES})
    return result


def boundaries():
    if (s.inputs.fingerprint(BASE, BASE_TREE) != PRED_REVIEW['candidate_input_sha256'] or
        s.inputs.fingerprint(PROOF_TREE / 'Coq', PROOF_TREE) != PR['candidate_input_sha256']):
        raise ValueError('reviewed predecessor/completed proof source changed')
    evidence = json.loads((PROOF / 'EVIDENCE-REVIEW.json').read_text())
    if (evidence['preparation_sha256'] != s.sha((PROOF / 'PREPARATION.json').read_bytes()) or
        evidence['review_sha256'] != s.sha((PROOF / 'REVIEW.json').read_bytes()) or
        evidence['normal_registration'] is not False or evidence['full_acceptance'] is not False):
        raise ValueError('completed proof evidence binding differs')
    for n, h in evidence['tools_sha256'].items():
        if s.sha((PROOF / n).read_bytes()) != h:
            raise ValueError('completed reviewer changed')
    for n, row in evidence['commands'].items():
        if row['exit_code'] != 0 or row['log_sha256'] != s.sha((PROOF / (n + '.log')).read_bytes()):
            raise ValueError('completed review/negative log changed')
    for n, h in PR['tools_sha256'].items():
        if s.sha((PROOF / n).read_bytes()) != h:
            raise ValueError('completed checker changed')
    for n, row in PR['commands'].items():
        if row['exit_code'] != 0 or row['log_sha256'] != s.sha((PROOF_TREE / (n + '.log')).read_bytes()):
            raise ValueError('completed compiler/kernel/AST/source evidence changed')
    for m in MODULES:
        for suffix, table in [('.v', 'source_sha256'), ('.vo', 'object_sha256')]:
            if s.sha((PROOF_TREE / 'Coq' / (m.replace('.', '/') + suffix)).read_bytes()) != PR[table][m]:
                raise ValueError('completed source/object changed')
    for n, h in PRED_REVIEW['tools_sha256'].items():
        if s.sha((PRED / n).read_bytes()) != h:
            raise ValueError('predecessor review tool changed')
    if s.input_map() not in [PRED_META['baseline_inputs'], baseline_inputs()] or s.index_hash() != PR['staged_patch_sha256']:
        raise ValueError('main/index is not a preserved exact 399 or 401 checkpoint')


def additions():
    results, definitions = [], []
    parser = load('lbtc_declarations', PROOF / 'check.py').shared
    for m in MODULES:
        a, b = parser.declarations((PROOF_TREE / 'Coq' / (m.replace('.', '/') + '.v')).read_text(), m)
        results += [' '.join(n.rsplit('.', 1)) for n in a]
        definitions += [' '.join(n.rsplit('.', 1)) for n in b]
    if (len(results), len(definitions)) != (13, 12):
        raise ValueError('wrong three-module declaration inventory')
    if {m for m, _ in normal.rows(BASE / 'C/jet_public_theorems.txt')} & set(MODULES):
        raise ValueError('new printer rules affect old declarations')
    return {'_CoqProject': NEW_SOURCES, '_CoqProject.jets': NEW_SOURCES,
            'C/jet_public_theorems.txt': results, 'C/jet_contract_definitions.txt': definitions}


def script_changes():
    once = parent.parent.replace_once
    original = (BASE / 'jet-coverage.py').read_text()
    old = '            elif name == "simplicity_tx_is_final":'
    new = r'''            elif name == "simplicity_lbtc_asset":
                contract = (rf"\bapplication_jet_local_spec_sep\s+f_{re.escape(name)}\s+"
                            r"elements_ge\s+Elements\.env\s+Ty\.Unit\s+Word256\b")
            elif name == "simplicity_tx_is_final":'''
    changes = {'jet-coverage.py': once(original, old, new, 'exact whole lbtc C contract').replace(
        '# Only these forty selected correspondences have a reviewed', '# Only these forty-one selected correspondences have a reviewed')}
    original = (BASE / 'check-jets.sh').read_text()
    old = 'python3 elements-tap-getters/test-source.py "${JET_C_REPO:-..}"\n'
    extra = ''.join('python3 elements-lbtc-asset/' + n + ' "${JET_C_REPO:-..}"\n' for n in ['check-source.py', 'test-source.py'])
    changes['check-jets.sh'] = once(original, old, old + extra, 'mandatory lbtc source and negative gates')
    original = (BASE / 'audit-jet-contracts.sh').read_text()
    rule = '         /^C\\.jet_haskell_hash_word$/ {print "Require " $0 "."; next}'
    original = once(original, rule, '         /^C\\.jet_u32_local_init$/ {print "Require " $0 "."; next}\n' + rule,
                    'load generic local initializer without opening it')
    lines = re.findall(r'(?m)^    explicit = .*$', original)
    if len(lines) != 1:
        raise ValueError('ambiguous explicit printer')
    changes['audit-jet-contracts.sh'] = once(original, lines[0], lines[0] +
        ' || ($1 ~ /^(' + '|'.join(m.replace('.', '[.]') for m in MODULES) + ')$/)', 'new modules only')
    original = (BASE / 'test-jet-coverage.py').read_text()
    boundary = '    print("coverage tests passed: exact core/partial/application contracts; wrong function/global/logical environment and unknown/duplicate/helper/unaudited entries rejected")'
    fragment = original.split('        # Two raw-key/byte-index contracts; never compile bad fixtures.\n', 1)
    if len(fragment) != 2:
        raise ValueError('missing statement-confined fixture template')
    fragment = fragment[1].split(boundary, 1)[0]
    fragment = once(fragment, fragment.splitlines()[0],
        "        for suffix, filename, theorem, domain, output in [('lbtc_asset', 'jet_elements_lbtc_asset_local', 'elements_lbtc_asset_local_spec', 'Ty.Unit', 'Word256')]:", 'seven new whole-contract fixtures')
    changes['test-jet-coverage.py'] = once(original, boundary,
        '        # Exact original C lbtc asset contract; never compile bad fixtures.\n' + fragment + boundary, 'new fixtures only')
    return changes


def assemble():
    if (HERE / 'ASSEMBLY.json').exists():
        raise ValueError('candidate already assembled; continue its recorded private tree')
    boundaries()
    source = load('lbtc_original_source_guard', PROOF / 'check-source.py')
    source.check(PROOF_TREE)
    before, index = s.input_map(), s.index_hash()
    work = Path(tempfile.mkdtemp(prefix='jet-lbtc-asset-admission.', dir='/private/tmp'))
    subprocess.run(['cp', '-cR', str(PROOF_TREE / 'Coq'), str(work / 'Coq')], check=True)
    for n in ['C', 'Haskell']:
        (work / n).symlink_to(REPO / n, target_is_directory=True)
    paths = load('lbtc_source_inventory', HERE.parent / 'elements-pegin-normal/review.py').source_paths
    if paths(work / 'Coq') - set(NEW_SOURCES) - paths(BASE):
        raise ValueError('completed seed contains unexpected sources')
    changes = {work / 'Coq' / n: (BASE / n).read_text() for n in paths(BASE)}
    extensions = additions()
    for n, rows in extensions.items():
        text = (BASE / n).read_text()
        if not text.endswith('\n') or any(row in text.splitlines() for row in rows):
            raise ValueError('nonfresh public inventory append')
        changes[work / 'Coq' / n] = text + '\n'.join(rows) + '\n'
    if 'simplicity_lbtc_asset ' in (BASE / 'C/jet_coverage.tsv').read_text():
        raise ValueError('lbtc jet already registered')
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
        proof_preparation_sha256=s.sha((PROOF / 'PREPARATION.json').read_bytes()),
        proof_review_sha256=s.sha((PROOF / 'EVIDENCE-REVIEW.json').read_bytes()),
        preparation_engine_sha256=s.sha(PREPARE_ENGINE.read_bytes()),
        main_inputs=before, main_input_sha256=s.inputs.fingerprint(MAIN, REPO), baseline_inputs=baseline_inputs(),
        staged_patch_sha256=index, extensions=extensions, coverage_additions=COVERAGE,
        baseline_metadata_sha256={n: s.sha((BASE / n).read_bytes()) for n in METADATA + SCRIPTS},
        source_sha256={m: PR['source_sha256'][m] for m in MODULES},
        new_sources=NEW_SOURCES, coverage_added=1, full_acceptance=False)
    write(work / 'ASSEMBLY.json', meta)
    write(HERE / 'ASSEMBLY.json', meta)
    print(json.dumps(dict(candidate=str(work), modules=3, results=13, definitions=12,
                         proposed_coverage='402/533', main_changed=False)), flush=True)


if __name__ == '__main__':
    if sys.argv[1:] == ['assemble']:
        assemble()
    elif len(sys.argv) == 3 and sys.argv[1] == 'prepare':
        engine = load('normal_delta_engine', PREPARE_ENGINE)
        # Pass explicit configuration, not a mutated predecessor's globals.
        from types import SimpleNamespace
        config = SimpleNamespace(**globals())
        engine.prepare(config, Path(sys.argv[2]).resolve())
    else:
        raise ValueError('usage: admission.py assemble|prepare PRIVATE_TREE')
