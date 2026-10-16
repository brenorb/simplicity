"""Isolated 419 candidate: complete null-data jet on represented BM frames.

The 17 additive proof batches retain their individual checked receipts. A
separate subsequent source review does not rewrite any formal receipt.
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


parent = load('null_data_normal_parent', HERE.parent / 'elements-txid-admission/admission.py')
s, normal, snapshot_deps, write = parent.s, parent.normal, parent.snapshot_deps, parent.write
PRED = HERE.parent / 'elements-txid-admission'
PRED_REVIEW = json.loads((PRED / 'REVIEW.json').read_text())
BASE_TREE = Path(json.loads((PRED / 'ASSEMBLY.json').read_text())['candidate'])
BASE = BASE_TREE / 'Coq'
PROOF = HERE.parent / 'elements-null-data-literal'
PROOF_TREE = Path(json.loads((PROOF / 'CHECKED.json').read_text())['candidate'])
SOURCE = HERE.parent / 'elements-null-data-source'
BATCHES = [
    'elements-null-data-output', 'elements-null-data-loads', 'elements-null-data-reserved',
    'elements-null-data-payload', 'elements-null-data-nonpush', 'elements-null-data-opcode',
    'elements-null-data-index', 'elements-null-data-output-guard', 'elements-current-reader',
    'elements-null-data-read-index', 'elements-null-data-guard-compose', 'elements-null-data-rest',
    'elements-null-data-layout', 'elements-null-data-bitmachine', 'elements-null-data-environment',
    'elements-null-data-context-contract', 'elements-null-data-literal']
RECEIPTS = [json.loads((HERE.parent / n / 'CHECKED.json').read_text()) for n in BATCHES]
MODULES = [m for r in RECEIPTS for m in r['modules']]
NEW_SOURCES = [m.replace('.', '/') + '.v' for m in MODULES]
PR = dict(dependencies={n: ds for r in RECEIPTS for n, ds in r['dependencies'].items()},
          staged_patch_sha256=RECEIPTS[-1]['staged_patch_sha256'])
METADATA, SCRIPTS = parent.METADATA, parent.SCRIPTS
GUARDS = ['elements-null-data-source/' + n for n in ['check-source.py', 'test-source.py', 'source-model.py']]
SEED_MISSING_GUARDS = {folder + '/' + n for folder in [
    'elements-amount-literal', 'elements-asset-literal', 'elements-issuance-amount-literal',
    'elements-legacy-check', 'elements-legacy-lock', 'elements-output-nonce',
    'elements-token-amount-complete', 'elements-txid-literal']
    for n in ['check-source.py', 'test-source.py']}
COVERAGE_ADDED = 1
COVERAGE = ('simplicity_output_null_datum C.jet_elements_null_data_literal '
            'elements_output_null_datum_literal_bitmachine_spec\n')
PREPARE_ENGINE = HERE.parent / 'normal-delta-prepare.py'


def proof_evidence_hashes():
    paths = [HERE.parent / n / f for n in BATCHES for f in ['CHECKED.json', 'EVIDENCE-REVIEW.json']]
    paths.append(SOURCE / 'SOURCE-REVIEW.json')
    return {str(p.relative_to(HERE.parent)): s.sha(p.read_bytes()) for p in paths}


def baseline_inputs():
    return json.loads((SOURCE / 'SOURCE-REVIEW.json').read_text())['main_inputs']


def main_fingerprint(inputs):
    if inputs != baseline_inputs():
        raise ValueError('unknown main checkpoint; require actual accepted418')
    return PRED_REVIEW['candidate_input_sha256']


def source_check(work):
    return load('null_data_selected_source', SOURCE / 'check-source.py').check(work)


def declarations(source, module):
    code = s.safe_source(source, module)
    results = [module + '.' + n for n in re.findall(r"^(?:Lemma|Theorem|Corollary)\s+([A-Za-z_][\w']*)", code, re.M)]
    definitions = [module + '.' + n for n in re.findall(r"^(?:Definition|Fixpoint|Record|Inductive)\s+([A-Za-z_][\w']*)", code, re.M)]
    return results, definitions


def boundaries():
    current = load('null_data_actual418', PRED / 'integration.py').check()
    if current['actual_main_acceptance'] is not True or current['coverage'] != '418/533':
        raise ValueError('actual main418 acceptance required')
    load('null_data_completed_source_review', SOURCE / 'review.py').verify(PROOF_TREE)
    if (len(MODULES), len(set(MODULES)), len(PR['dependencies'])) != (24, 24, 144):
        raise ValueError('wrong complete proof-closure inventory')
    for folder, r in zip(BATCHES, RECEIPTS):
        here, work = HERE.parent / folder, Path(r['candidate'])
        if json.loads((here / 'CHECKED.json').read_text()) != r:
            raise ValueError('proof receipt changed after loading')
        e = json.loads((here / 'EVIDENCE-REVIEW.json').read_text())
        if (e['checked_sha256'] != s.sha((here / 'CHECKED.json').read_bytes()) or
            e['launch_sha256'] != s.sha((here / 'RUN.json').read_bytes()) or
            e['candidate_input_sha256'] != r['candidate_input_sha256'] or
            s.inputs.fingerprint(work / 'Coq', work) != r['candidate_input_sha256'] or
            r['recursive_kernel_check'] is not True or e['review']['recursive_kernel_check'] is not True or
            e['review']['inherited_source_changes'] != 0 or
            any(e[n] is not False for n in ['normal_registration', 'full_acceptance'])):
            raise ValueError('incomplete/changed proof evidence: ' + folder)
        for receipt in [r, e]:
            for n, h in receipt['tools_sha256'].items():
                if s.sha((here / n).read_bytes()) != h:
                    raise ValueError('proof checker/reviewer changed')
            for n, row in receipt['commands'].items():
                log = work / (n + '.log')
                if row['exit_code'] != 0 or row['log_sha256'] != s.sha(log.read_bytes()) or (here / log.name).read_bytes() != log.read_bytes():
                    raise ValueError('compiler/kernel/report/evidence command log changed')
        rs, ds = [], []
        for m in r['modules']:
            n = m.replace('.', '/') + '.v'
            a, b = declarations((PROOF_TREE / 'Coq' / n).read_text(), m)
            rs += a
            ds += b
            if (work / 'Coq' / n).read_bytes() != (PROOF_TREE / 'Coq' / n).read_bytes():
                raise ValueError('proof closure source changed')
            for suffix, table in [('.v', 'source_sha256'), ('.vo', 'object_sha256')]:
                if s.sha((work / 'Coq' / (m.replace('.', '/') + suffix)).read_bytes()) != r[table][m]:
                    raise ValueError('checked source/object changed')
        if rs != r['results'] or ds != r['definitions']:
            raise ValueError('proof declaration inventory differs')
    if s.input_map() != baseline_inputs() or s.index_hash() != PR['staged_patch_sha256']:
        raise ValueError('main/index differs from accepted418/source review')


def additions():
    results, definitions = [], []
    for m in MODULES:
        a, b = declarations((PROOF_TREE / 'Coq' / (m.replace('.', '/') + '.v')).read_text(), m)
        results += [' '.join(n.rsplit('.', 1)) for n in a]
        definitions += [' '.join(n.rsplit('.', 1)) for n in b]
    if (len(results), len(definitions)) != (144, 103):
        raise ValueError('wrong full declaration/inductive inventory')
    if {m for m, _ in normal.rows(BASE / 'C/jet_public_theorems.txt')} & set(MODULES):
        raise ValueError('new printer rules affect inherited modules')
    return {'_CoqProject': NEW_SOURCES, '_CoqProject.jets': NEW_SOURCES,
            'C/jet_public_theorems.txt': results, 'C/jet_contract_definitions.txt': definitions}


def script_changes():
    once = load('null_data_exact_replace', HERE.parent / 'elements-direct-getters-admission/admission.py').replace_once
    original = (BASE / 'jet-coverage.py').read_text()
    old = '            elif name == "simplicity_transaction_id":'
    new = r'''            elif name == "simplicity_output_null_datum":
                # Explicit contextual family: separated represented BM frames,
                # not the unrestricted application_jet_local_spec_sep API.
                contract = (rf"\bapplication_jet_bitmachine_spec\s+f_{re.escape(name)}\s+"
                            r"elements_ge\s+Elements\.env\s+\(Ty\.Prod\s+Word32\s+Word32\)\s+"
                            r"ResultTy\s+elements_null_data_environment_rep\s+"
                            r"elements_output_null_datum_literal_spec\s*\.$")
            elif name == "simplicity_transaction_id":'''
    changes = {'jet-coverage.py': once(original, old, new, 'exact contextual null-data contract').replace(
        '# Only these fifty-seven selected correspondences have a reviewed', '# Only these fifty-eight selected correspondences have a reviewed')}
    original = (BASE / 'check-jets.sh').read_text()
    old = 'python3 elements-txid-literal/test-source.py "${JET_C_REPO:-..}"\n'
    extra = ''.join('python3 elements-null-data-source/' + n + ' "${JET_C_REPO:-..}"\n' for n in ['check-source.py', 'test-source.py'])
    changes['check-jets.sh'] = once(original, old, old + extra, 'mandatory null-data source guards')
    original = (BASE / 'audit-jet-contracts.sh').read_text()
    selected = '|'.join(m.replace('.', '[.]') for m in MODULES)
    rule = '         /^C\\.jet_elements_/ {print "Require " $0 "."; next}'
    original = once(original, rule, '         /^(' + selected + ')$/ {print "Require " $0 "."; next}\n' + rule, 'load new modules without opening')
    lines = re.findall(r'(?m)^    explicit = .*$', original)
    if len(lines) != 1:
        raise ValueError('ambiguous explicit-printer rule')
    changes['audit-jet-contracts.sh'] = once(original, lines[0], lines[0] +
        ' || ($1 ~ /^(' + selected + ')$/)', 'new modules only explicit types')
    original = (BASE / 'test-jet-coverage.py').read_text()
    boundary = '    print("coverage tests passed: exact core/partial/application contracts; wrong function/global/logical environment and unknown/duplicate/helper/unaudited entries rejected")'
    changes['test-jet-coverage.py'] = once(original, boundary, (HERE / 'coverage-fixtures.py').read_text() + boundary, 'contextual null-data fixtures')
    return changes


def assemble(work=None):
    if (HERE / 'ASSEMBLY.json').exists():
        raise ValueError('already assembled; continue recorded candidate')
    boundaries()
    before, index = s.input_map(), s.index_hash()
    if work is None:
        work = Path(tempfile.mkdtemp(prefix='jet-null-data-admission.', dir='/private/tmp'))
        subprocess.run(['cp', '-cR', str(PROOF_TREE / 'Coq'), str(work / 'Coq')], check=True)
        for n in ['C', 'Haskell']:
            (work / n).symlink_to(REPO / n, target_is_directory=True)
    elif work.parent != Path('/private/tmp') or not work.name.startswith('jet-null-data-admission.'):
        raise ValueError('resume only a private unrecorded seed copy')
    paths = load('null_data_source_inventory', HERE.parent / 'elements-pegin-normal/review.py').source_paths
    if (paths(work / 'Coq') - paths(BASE) != set(NEW_SOURCES) or
        paths(BASE) - paths(work / 'Coq') != SEED_MISSING_GUARDS):
        raise ValueError('unexpected completed proof closure')
    for n in paths(work / 'Coq'):
        if (work / 'Coq' / n).read_bytes() != (PROOF_TREE / 'Coq' / n).read_bytes():
            raise ValueError('resumed seed differs from completed proof')
    changes = {work / 'Coq' / n: (BASE / n).read_text() for n in paths(BASE)}
    extensions = additions()
    for n, rows in extensions.items():
        text = (BASE / n).read_text()
        if not text.endswith('\n') or any(row in text.splitlines() for row in rows):
            raise ValueError('nonfresh inventory append')
        changes[work / 'Coq' / n] = text + '\n'.join(rows) + '\n'
    if 'simplicity_output_null_datum ' in (BASE / 'C/jet_coverage.tsv').read_text():
        raise ValueError('null-data already registered')
    changes[work / 'Coq/C/jet_coverage.tsv'] = (BASE / 'C/jet_coverage.tsv').read_text() + COVERAGE
    changes.update({work / 'Coq' / n: (HERE.parent / n).read_text() for n in GUARDS})
    changes.update({work / 'Coq' / n: text for n, text in script_changes().items()})
    s.changed(changes)
    source_check(work)
    boundaries()
    if s.input_map() != before or s.index_hash() != index:
        raise ValueError('main/index drift during assembly')
    meta = dict(candidate=str(work), predecessor_candidate=str(BASE_TREE),
        predecessor_input_sha256=PRED_REVIEW['candidate_input_sha256'],
        predecessor_review_sha256=s.sha((PRED / 'REVIEW.json').read_bytes()),
        proof_evidence_sha256=proof_evidence_hashes(), preparation_engine_sha256=s.sha(PREPARE_ENGINE.read_bytes()),
        main_inputs=before, main_input_sha256=main_fingerprint(before), baseline_inputs=baseline_inputs(),
        staged_patch_sha256=index, extensions=extensions, coverage_additions=COVERAGE,
        baseline_metadata_sha256={n: s.sha((BASE / n).read_bytes()) for n in METADATA + SCRIPTS},
        source_sha256={m: s.sha((PROOF_TREE / 'Coq' / (m.replace('.', '/') + '.v')).read_bytes()) for m in MODULES},
        new_sources=NEW_SOURCES, coverage_added=1, full_acceptance=False)
    write(work / 'ASSEMBLY.json', meta)
    write(HERE / 'ASSEMBLY.json', meta)
    print(json.dumps(dict(candidate=str(work), modules=24, results=144, definitions=103,
                         proposed_coverage='419/533', main_changed=False)), flush=True)


if __name__ == '__main__':
    if sys.argv[1:] == ['assemble']:
        assemble()
    elif len(sys.argv) == 3 and sys.argv[1] == 'assemble':
        assemble(Path(sys.argv[2]).resolve())
    elif len(sys.argv) == 3 and sys.argv[1] == 'prepare':
        load('null_data_normal_prepare', PREPARE_ENGINE).prepare(SimpleNamespace(**globals()), Path(sys.argv[2]).resolve())
    else:
        raise ValueError('usage: admission.py assemble|prepare PRIVATE_TREE')
