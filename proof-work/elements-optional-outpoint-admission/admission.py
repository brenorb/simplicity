"""Prepare eleven checked getters over the reviewed 386-jet source predecessor.

Only immutable completed trees supply compiler objects. The live predecessor
supplies fingerprint-bound source text, never objects. No acceptance is claimed.
"""
import argparse
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
spec = importlib.util.spec_from_file_location('optional_outpoint_predecessor', HERE.parent / 'elements-digest-getters-admission/admission.py')
predecessor = importlib.util.module_from_spec(spec)
spec.loader.exec_module(predecessor)
support, normal, snapshot_deps = predecessor.support, predecessor.normal, predecessor.snapshot_deps
replace_once, write = predecessor.replace_once, predecessor.write
PRED = HERE.parent / 'elements-digest-getters-admission'
PRED_META = json.loads((PRED / 'ASSEMBLY.json').read_text())
PRED_REVIEW = json.loads((PRED / 'REVIEW.json').read_text())
BASE_TREE = Path(PRED_META['candidate'])
BASE = BASE_TREE / 'Coq'
PRIOR_PATHS = [HERE.parent / p for p in ['elements-annex-hash/PREPARATION.json',
               'elements-issuance-digest/PREPARATION.json', 'elements-outpoint-output/CHECKED.json',
               'elements-outpoint-output/PREPARATION.json']]
PRIORS = [json.loads(p.read_text()) for p in PRIOR_PATHS]
MODULES = ['jet_elements_annex_local', 'jet_elements_optional_digest_literal',
           'jet_elements_issuance_digest_literal', 'jet_elements_indexed_literal']
ORIGINS = {m: Path(r['candidate']) / 'Coq/C' / (m + '.v') for m, r in zip(MODULES, [PRIORS[0], PRIORS[0], PRIORS[1], PRIORS[2]])}
NEW_SOURCES = ['C/' + m + '.v' for m in MODULES[1:]]
METADATA, SCRIPTS = predecessor.METADATA, predecessor.SCRIPTS
GUARD_MODULES = [('elements-annex-hash', MODULES[1]), ('elements-issuance-digest', MODULES[2]),
                 ('elements-outpoint-output', MODULES[3])]
GUARDS = [d + '/' + n for d, _ in GUARD_MODULES for n in ['check-source.py', 'test-source.py']]
ENDPOINTS = [
    ('input_annex_hash', 'jet_elements_annex_local', 'elements_input_annex_hash_local_spec', 'Word32', '(Ty.Sum Ty.Unit (Ty.Sum Ty.Unit Word256))'),
    ('current_annex_hash', 'jet_elements_current_gen_jets', 'elements_current_annex_hash_local_spec', 'Ty.Unit', '(Ty.Sum Ty.Unit Word256)'),
    *[(('current_' if current else '') + name,
       'jet_elements_current_input_jets' if current else 'jet_elements_issuance_jets',
       'elements_' + ('current_' if current else '') + name + '_local_spec',
       'Ty.Unit' if current else 'Word32', '(Ty.Sum Ty.Unit Word256)' if current else '(Ty.Sum Ty.Unit (Ty.Sum Ty.Unit Word256))')
      for name in ['reissuance_blinding', 'new_issuance_contract', 'reissuance_entropy'] for current in [False, True]],
    ('input_prev_outpoint', 'jet_elements_indexed_ptr_jets', 'elements_input_prev_outpoint_local_spec', 'Word32', '(Ty.Sum Ty.Unit (Ty.Prod Word256 Word32))'),
    ('current_prev_outpoint', 'jet_elements_current_input_jets', 'elements_current_prev_outpoint_local_spec', 'Ty.Unit', '(Ty.Prod Word256 Word32)'),
    ('output_script_hash', 'jet_elements_indexed_ptr_jets', 'elements_output_script_hash_local_spec', 'Word32', '(Ty.Sum Ty.Unit Word256)'),
]
COVERAGE = ''.join('simplicity_' + f + ' C.' + m + ' ' + n + '\n' for f, m, n, _, _ in ENDPOINTS)


def script_changes():
    original = (BASE / 'jet-coverage.py').read_text()
    old = '            elif name == "simplicity_tx_is_final":'
    new = r'''            elif name in {"simplicity_input_annex_hash", "simplicity_reissuance_blinding", "simplicity_new_issuance_contract", "simplicity_reissuance_entropy"}:
                contract = (rf"\bapplication_jet_local_spec_sep\s+f_{re.escape(name)}\s+"
                            r"elements_ge\s+Elements\.env\s+Word32\s+\(Ty\.Sum\s+Ty\.Unit\s+\(Ty\.Sum\s+Ty\.Unit\s+Word256\)\)")
            elif name in {"simplicity_current_annex_hash", "simplicity_current_reissuance_blinding", "simplicity_current_new_issuance_contract", "simplicity_current_reissuance_entropy"}:
                contract = (rf"\bapplication_jet_local_spec_sep\s+f_{re.escape(name)}\s+"
                            r"elements_ge\s+Elements\.env\s+Ty\.Unit\s+\(Ty\.Sum\s+Ty\.Unit\s+Word256\)")
            elif name == "simplicity_input_prev_outpoint":
                contract = (rf"\bapplication_jet_local_spec_sep\s+f_{re.escape(name)}\s+"
                            r"elements_ge\s+Elements\.env\s+Word32\s+\(Ty\.Sum\s+Ty\.Unit\s+\(Ty\.Prod\s+Word256\s+Word32\)\)")
            elif name == "simplicity_current_prev_outpoint":
                contract = (rf"\bapplication_jet_local_spec_sep\s+f_{re.escape(name)}\s+"
                            r"elements_ge\s+Elements\.env\s+Ty\.Unit\s+\(Ty\.Prod\s+Word256\s+Word32\)")
            elif name == "simplicity_output_script_hash":
                contract = (rf"\bapplication_jet_local_spec_sep\s+f_{re.escape(name)}\s+"
                            r"elements_ge\s+Elements\.env\s+Word32\s+\(Ty\.Sum\s+Ty\.Unit\s+Word256\)")
            elif name == "simplicity_tx_is_final":'''
    changes = {'jet-coverage.py': replace_once(original, old, new, 'eleven exact whole getter contracts').replace(
        '# Only these twenty-five selected correspondences have a reviewed', '# Only these thirty-six selected correspondences have a reviewed')}
    original = (BASE / 'check-jets.sh').read_text()
    old = 'python3 elements-issuance-proof/test-source.py "${JET_C_REPO:-..}" . C/jet_elements_issuance_proof_literal.v\n'
    extra = ''.join('python3 ' + d + '/check-source.py --repo "${JET_C_REPO:-..}" --coq . --literal C/' + m + '.v\n' +
                    'python3 ' + d + '/test-source.py "${JET_C_REPO:-..}" . C/' + m + '.v\n' for d, m in GUARD_MODULES)
    changes['check-jets.sh'] = replace_once(original, old, old + extra, 'three mandatory source/negative gates')
    original = (BASE / 'audit-jet-contracts.sh').read_text()
    lines = re.findall(r'(?m)^    explicit = .*$', original)
    if len(lines) != 1:
        raise ValueError('ambiguous explicit contract printer')
    changes['audit-jet-contracts.sh'] = replace_once(original, lines[0], lines[0] +
        ' || ($1 ~ /^(' + '|'.join('C[.]' + m for m in MODULES) + ')$/)', 'four new modules only')
    # Reuse the reviewed, statement-confined fixture generator, with this batch's
    # endpoints. It changes no existing fixture or existing coverage allowance.
    template = predecessor.script_changes()['test-jet-coverage.py']
    boundary = '    print("coverage tests passed: exact core/partial/application contracts; wrong function/global/logical environment and unknown/duplicate/helper/unaudited entries rejected")'
    added = template.split('        # Eight exact indexed/current digest contracts; never compile bad fixtures.\n', 1)
    if len(added) != 2:
        raise ValueError('missing reviewed statement-confined coverage fixture generator')
    fixture = added[1].split(boundary, 1)[0]
    first = fixture.splitlines()[0]
    fixture = replace_once(fixture, first, '        for suffix, filename, theorem, domain, output in ' + repr(ENDPOINTS) + ':', '77 selected coverage negatives')
    changes['test-jet-coverage.py'] = replace_once((BASE / 'test-jet-coverage.py').read_text(), boundary,
        '        # Eleven optional/outpoint/output contracts; never compile bad fixtures.\n' + fixture + boundary, 'new fixtures only')
    return changes


def additions():
    results, definitions = [], []
    for m in MODULES:
        code = support.safe_source(ORIGINS[m].read_text(), m)
        results += ['C.' + m + ' ' + n for n in re.findall(r"^(?:Lemma|Theorem|Corollary)\s+([A-Za-z_][\w']*)", code, re.M)]
        definitions += ['C.' + m + ' ' + n for n in re.findall(r"^(?:Definition|Fixpoint|Record)\s+([A-Za-z_][\w']*)", code, re.M)]
    if (len(results), len(definitions)) != (34, 30):
        raise ValueError('wrong four-module declaration inventory')
    if {m for m, _ in normal.rows(BASE / 'C/jet_public_theorems.txt')} & {'C.' + m for m in MODULES}:
        raise ValueError('new printer rule affects inherited records')
    return {'_CoqProject': ['C/' + m + '.v' for m in MODULES], '_CoqProject.jets': ['C/' + m + '.v' for m in MODULES],
            'C/jet_public_theorems.txt': results, 'C/jet_contract_definitions.txt': definitions}


def predecessor_source():
    if support.inputs.fingerprint(BASE, BASE_TREE) != PRED_REVIEW['candidate_input_sha256']:
        raise ValueError('reviewed 386 predecessor source changed')
    for n, h in PRED_REVIEW['tools_sha256'].items():
        if support.sha((PRED / n).read_bytes()) != h:
            raise ValueError('predecessor review tool changed')


def assemble():
    for directory, reviewer in [('elements-annex-hash', 'review.py'), ('elements-issuance-digest', 'review.py'),
                                 ('elements-outpoint-output', 'review-source.py')]:
        subprocess.run([sys.executable, '-B', str(HERE.parent / directory / reviewer)], check=True)
    predecessor_source()
    before, index = support.input_map(), support.index_hash()
    paths = support.load('optional_admission_source_paths', HERE.parent / 'elements-pegin-normal/review.py').source_paths
    seed = predecessor.predecessor.PRIOR_TREE
    if not paths(seed / 'Coq') <= paths(BASE):
        raise ValueError('immutable seed contains unexpected source files')
    work = Path(tempfile.mkdtemp(prefix='jet-optional-outpoint-admission.', dir='/private/tmp'))
    subprocess.run(['cp', '-cR', str(seed / 'Coq'), str(work / 'Coq')], check=True)
    for n in ['C', 'Haskell']:
        (work / n).symlink_to(REPO / n, target_is_directory=True)
    support.changed({work / 'Coq' / n: (BASE / n).read_text() for n in paths(BASE)
                     if not (work / 'Coq' / n).exists() or (work / 'Coq' / n).read_bytes() != (BASE / n).read_bytes()})
    if support.inputs.fingerprint(work / 'Coq', work) != PRED_REVIEW['candidate_input_sha256']:
        raise ValueError('reconstructed 386 source differs; no live compiler outputs may be copied')
    baseline = {n: h for n, h in before.items() if not n.startswith('Coq/')}
    baseline.update({'Coq/' + n: support.sha((BASE / n).read_bytes()) for n in paths(BASE)})
    if before not in [PRED_META['baseline_inputs'], baseline]:
        raise ValueError('main is not an exact known 378/386 checkpoint')
    extensions, changes = additions(), {}
    for n, rows in extensions.items():
        old = (BASE / n).read_text()
        if not old.endswith('\n') or any(row in old.splitlines() for row in rows):
            raise ValueError('nonfresh declaration/manifest append')
        changes[work / 'Coq' / n] = old + '\n'.join(rows) + '\n'
    old = (BASE / 'C/jet_coverage.tsv').read_text()
    if {r.split()[0] for r in COVERAGE.splitlines()} & {r.split()[0] for r in old.splitlines() if r.strip()}:
        raise ValueError('selected getter already registered')
    changes[work / 'Coq/C/jet_coverage.tsv'] = old + COVERAGE
    changes.update({work / 'Coq/C' / (m + '.v'): ORIGINS[m].read_text() for m in MODULES})
    changes.update({work / 'Coq' / n: (HERE.parent / n).read_text() for n in GUARDS})
    changes.update({work / 'Coq' / n: text for n, text in script_changes().items()})
    support.changed(changes)
    predecessor_source()
    if support.input_map() != before or support.index_hash() != index:
        raise ValueError('main/index drift during assembly')
    meta = {'candidate': str(work), 'predecessor_candidate': str(BASE_TREE),
            'predecessor_input_sha256': PRED_REVIEW['candidate_input_sha256'],
            'predecessor_review_sha256': support.sha((PRED / 'REVIEW.json').read_bytes()),
            'main_inputs': before, 'main_input_sha256': support.inputs.fingerprint(MAIN, REPO),
            'baseline_inputs': baseline, 'staged_patch_sha256': index, 'extensions': extensions, 'coverage_additions': COVERAGE,
            'baseline_metadata_sha256': {n: support.sha((BASE / n).read_bytes()) for n in METADATA + SCRIPTS},
            'source_sha256': {'Coq/C/' + m + '.v': support.sha(ORIGINS[m].read_bytes()) for m in MODULES},
            'prior_preparations_sha256': {str(p.relative_to(HERE.parent)): support.sha(p.read_bytes()) for p in PRIOR_PATHS},
            'new_sources': NEW_SOURCES, 'coverage_added': 11, 'full_acceptance': False}
    write(work / 'ASSEMBLY.json', meta)
    write(HERE / 'ASSEMBLY.json', meta)
    print(json.dumps({'candidate': str(work), 'modules': 4, 'results': 34, 'definitions': 30,
                      'proposed_coverage': '397/533', 'main_changed': False}), flush=True)


def command(work, args, stem, timeout=10800):
    return support.run(work, args, stem, timeout)


def prepare(work):
    meta = json.loads((work / 'ASSEMBLY.json').read_text())
    before = support.input_map()
    predecessor_source()
    built = command(work, ['bash', 'build-jets.sh', '-j2'], 'build')
    fresh = {m: command(work, ['bash', 'build-jets.sh', '--coqc', '-q', 'C/' + m + '.v'], 'fresh-' + m, 180) for m in MODULES}
    coq = work / 'Coq'
    results = [tuple(row.split()) for row in meta['extensions']['C/jet_public_theorems.txt']]
    definitions = [tuple(row.split()) for row in meta['extensions']['C/jet_contract_definitions.txt']]
    all_rows = normal.rows(coq / 'C/jet_public_theorems.txt') + normal.rows(coq / 'C/jet_contract_definitions.txt')
    driver = ['Set Warnings "-notation-overridden".']
    for m in sorted({m for m, _ in all_rows}):
        keyword = ('Require' if m.startswith(('Simplicity.', 'C.jet_elements_')) or m in
                   {'C.jet_secp_umul128_exec', 'C.jet_haskell_hash_word', 'C.jet_application_partial_transport'} else 'Require Import')
        driver.append(keyword + ' ' + m + '.')
    assumptions = driver[:]
    for m, n in results:
        assumptions += ['Goal True. idtac "JET_ASSUMPTIONS ' + m + '.' + n + '". exact I. Qed.', 'Print Assumptions ' + m + '.' + n + '.']
    wanted = [('TYPE', m + '.' + n) for m, n in results] + [('DEF', m + '.' + n) for m, n in definitions]
    driver += ['Import Simplicity.BitMachine Simplicity.Translate.', 'Set Printing All.', 'Set Printing Width 120.']
    for depth, marker in [(50, 'DIGEST_COMPACT_'), (1000000, 'DIGEST_DEEP_')]:
        driver += ['Set Printing Depth ' + str(depth) + '.']
        for kind, n in wanted:
            driver += ['Goal True. idtac "' + marker + kind + ' ' + n + '". exact I. Qed.', ('Check @' if kind == 'TYPE' else 'Print ') + n + '.']
    support.changed({work / 'new_contracts.v': '\n'.join(driver) + '\n', work / 'new_assumptions.v': '\n'.join(assumptions) + '\n'})
    contracts = command(work, ['bash', 'build-jets.sh', '--coqc', '-q', str(work / 'new_contracts.v')], 'new_contracts')
    audited = command(work, ['bash', 'build-jets.sh', '--coqc', '-q', str(work / 'new_assumptions.v')], 'new_assumptions')
    report = (work / 'new_contracts.log').read_text().split('DIGEST_DEEP_', 1)[0]
    marks = list(re.finditer(r'(?m)^DIGEST_COMPACT_(TYPE|DEF) (\S+)\n', report))
    if [(m[1], m[2]) for m in marks] != wanted or report[:marks[0].start()]:
        raise ValueError('incomplete compact digest report')
    bodies = {wanted[i]: ''.join(line.rstrip() + '\n' for line in report[m.end():marks[i+1].start() if i+1 < len(marks) else len(report)].splitlines()) for i, m in enumerate(marks)}
    inherited = normal.contract_records((BASE / 'C/jet_contracts.expected').read_text(), normal.rows(BASE / 'C/jet_public_theorems.txt'), normal.rows(BASE / 'C/jet_contract_definitions.txt'))
    snapshot = ''.join(t for (k, _, _, _), t in inherited if k == 'TYPE') + ''.join(bodies[('TYPE', m + '.' + n)] for m, n in results)
    snapshot += ''.join(t for (k, _, _, _), t in inherited if k == 'DEF') + ''.join(bodies[('DEF', m + '.' + n)] for m, n in definitions)
    deps = normal.assumptions((work / 'new_assumptions.log').read_text())
    expected = {n: ds for r in PRIORS[:3] for n, ds in r['dependencies'].items()}
    if set(deps) != {m + '.' + n for m, n in results} or any(sorted(ds) != expected[n] for n, ds in deps.items()):
        raise ValueError('new digest assumption sets changed')
    old_deps = snapshot_deps((BASE / 'C/jet_assumptions.expected').read_text())
    if set(old_deps) & set(deps):
        raise ValueError('overlapping assumptions')
    old_deps.update({n: sorted(ds) for n, ds in deps.items()})
    text = ''.join(n + ' : ' + (', '.join(ds) or 'closed') + '\n' for n, ds in sorted(old_deps.items()))
    support.changed({coq / 'C/jet_contracts.expected': snapshot, coq / 'C/jet_assumptions.expected': text})
    if support.input_map() != before or support.index_hash() != meta['staged_patch_sha256']:
        raise ValueError('main/index changed during preparation')
    r = {'candidate': str(work), 'build': built, 'fresh_compiles': fresh, 'contracts': contracts, 'assumptions': audited,
         'new_dependencies': {n: sorted(ds) for n, ds in deps.items()},
         'new_objects_sha256': {'Coq/C/' + m + '.vo': support.sha((coq / 'C' / (m + '.vo')).read_bytes()) for m in MODULES},
         'coverage_added': 11, 'full_acceptance': False}
    write(work / 'PREPARATION.json', r)
    write(HERE / 'PREPARATION.json', r)
    print('Eleven-jet normal preparation complete; review, predecessor acceptance and own full acceptance still required', flush=True)



if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('action', choices=['assemble', 'prepare'])
    p.add_argument('work', nargs='?')
    args = p.parse_args()
    assemble() if args.action == 'assemble' else prepare(Path(args.work).resolve())
