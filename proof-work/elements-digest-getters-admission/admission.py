"""Prepare eight digest getters over the reviewed, not-yet-installed predecessor.

Copy objects only from an immutable completed proof tree. The running
predecessor supplies fingerprint-bound source text, never compiler outputs.
Preparation is not authorization to accept or install an unfinished predecessor.
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
REPO = HERE.parents[1]
MAIN = REPO / 'Coq'
spec = importlib.util.spec_from_file_location('digest_admission_predecessor', HERE.parent / 'elements-timelock-pegin-admission/admission.py')
predecessor = importlib.util.module_from_spec(spec)
spec.loader.exec_module(predecessor)
support, normal, snapshot_deps = predecessor.support, predecessor.normal, predecessor.snapshot_deps
replace_once, write = predecessor.replace_once, predecessor.write
PRED = HERE.parent / 'elements-timelock-pegin-admission'
PRED_META = json.loads((PRED / 'ASSEMBLY.json').read_text())
PRED_REVIEW = json.loads((PRED / 'REVIEW.json').read_text())
BASE_TREE = Path(PRED_META['candidate'])
BASE = BASE_TREE / 'Coq'
PRIOR_PATHS = [HERE.parent / 'elements-script-hash/PREPARATION.json', HERE.parent / 'elements-issuance-proof/CHECKED.json',
               HERE.parent / 'elements-issuance-proof/PREPARATION.json']
PRIORS = [json.loads(p.read_text()) for p in PRIOR_PATHS]
PRIOR_TREE = Path(PRIORS[1]['candidate'])
MODULES = ['jet_elements_script_hash_literal', 'jet_elements_issuance_proof_literal']
NEW_SOURCES = ['C/' + m + '.v' for m in MODULES]
METADATA, SCRIPTS = predecessor.METADATA, predecessor.SCRIPTS
GUARDS = [d + '/' + n for d in ['elements-script-hash', 'elements-issuance-proof'] for n in ['check-source.py', 'test-source.py']]
ENDPOINTS = [(prefix + suffix, 'jet_elements_current_input_jets' if prefix == 'current_' else 'jet_elements_input_hash_jets',
              'elements_' + prefix + suffix + '_local_spec', 'Ty.Unit' if prefix == 'current_' else 'Word32',
              'Word256' if prefix == 'current_' else '(Ty.Sum Ty.Unit Word256)')
             for prefix, suffix in [('input_', 'script_hash'), ('input_', 'script_sig_hash'),
                                    ('current_', 'script_hash'), ('current_', 'script_sig_hash'),
                                    ('', 'issuance_asset_proof'), ('', 'issuance_token_proof'),
                                    ('current_', 'issuance_asset_proof'), ('current_', 'issuance_token_proof')]]
COVERAGE = ''.join('simplicity_' + f + ' C.' + m + ' ' + n + '\n' for f, m, n, _, _ in ENDPOINTS)


def script_changes():
    changes = {}
    original = (BASE / 'jet-coverage.py').read_text()
    old = '            if name == "simplicity_tx_is_final":'
    new = r'''            if name in {"simplicity_input_script_hash", "simplicity_input_script_sig_hash", "simplicity_issuance_asset_proof", "simplicity_issuance_token_proof"}:
                contract = (rf"\bapplication_jet_local_spec_sep\s+f_{re.escape(name)}\s+"
                            r"elements_ge\s+Elements\.env\s+Word32\s+\(Ty\.Sum\s+Ty\.Unit\s+Word256\)")
            elif name in {"simplicity_current_script_hash", "simplicity_current_script_sig_hash", "simplicity_current_issuance_asset_proof", "simplicity_current_issuance_token_proof"}:
                contract = (rf"\bapplication_jet_local_spec_sep\s+f_{re.escape(name)}\s+"
                            r"elements_ge\s+Elements\.env\s+Ty\.Unit\s+Word256\b")
            elif name == "simplicity_tx_is_final":'''
    changes['jet-coverage.py'] = replace_once(original, old, new, 'eight exact digest contracts').replace(
        '# Only these seventeen selected correspondences have a reviewed', '# Only these twenty-five selected correspondences have a reviewed')
    original = (BASE / 'check-jets.sh').read_text()
    old = 'python3 elements-pegin/test-source.py "${JET_C_REPO:-..}" . C/jet_elements_pegin_literal.v\n'
    extra = ''.join('python3 ' + directory + '/check-source.py --repo "${JET_C_REPO:-..}" --coq . --literal C/' + module + '.v\n' +
                    'python3 ' + directory + '/test-source.py "${JET_C_REPO:-..}" . C/' + module + '.v\n'
                    for directory, module in zip(['elements-script-hash', 'elements-issuance-proof'], MODULES))
    changes['check-jets.sh'] = replace_once(original, old, old + extra, 'mandatory digest source gates')
    original = (BASE / 'audit-jet-contracts.sh').read_text()
    lines = re.findall(r'(?m)^    explicit = .*$', original)
    if len(lines) != 1:
        raise ValueError('ambiguous printer rule')
    selected = '|'.join('C[.]' + m for m in MODULES)
    changes['audit-jet-contracts.sh'] = replace_once(original, lines[0], lines[0] + ' || ($1 ~ /^(' + selected + ')$/)', 'two-module-only explicit printing')
    original = (BASE / 'test-jet-coverage.py').read_text()
    boundary = '    print("coverage tests passed: exact core/partial/application contracts; wrong function/global/logical environment and unknown/duplicate/helper/unaudited entries rejected")'
    extra = '        # Eight exact indexed/current digest contracts; never compile bad fixtures.\n'
    extra += '        for suffix, filename, theorem, domain, output in ' + repr(ENDPOINTS) + ':\n'
    extra += '''            module = 'C.' + filename
            file = project / (module.replace('.', '/') + '.v')
            shutil.copy2(SOURCE / (module.replace('.', '/') + '.v'), file)
            text = file.read_text()
            if not any(r['function'] == 'simplicity_' + suffix and r['proof'] for r in coverage.inventory()):
                manifest.write_text(manifest.read_text() + 'simplicity_' + suffix + ' ' + module + ' ' + theorem + '\\n')
            if [module, theorem] not in coverage.records(audited, 2):
                audited.write_text(audited.read_text() + module + ' ' + theorem + '\\n')
            declaration = 'Theorem ' + theorem + ' :'
            for old, new in [
                ('f_simplicity_' + suffix + ' elements_ge', 'f_simplicity_version elements_ge'),
                ('elements_ge Elements.env', 'ge0 Elements.env'),
                ('elements_ge Elements.env', 'elements_ge Bitcoin.env'),
                (domain + ' ' + output, 'Word64 ' + output),
                (domain + ' ' + output, domain + ' Word16'),
                (declaration, declaration + ' False ->'),
                ('application_jet_local_spec_sep f_simplicity_' + suffix, 'application_jet_local_spec f_simplicity_' + suffix),
            ]:
                start = text.index(declaration)
                stop = text.index('Proof.', start)
                tail = text[start:stop]
                if old not in tail:
                    import re
                    match = re.search(r'\\s+'.join(map(re.escape, old.split())), tail)
                    assert match, (suffix, old)
                    old = match[0]
                file.write_text(text[:start] + tail.replace(old, new, 1) + text[stop:])
                rejects(coverage.inventory, 'not a direct canonical jet theorem')
            file.write_text(text)
            assert coverage.inventory()
'''
    changes['test-jet-coverage.py'] = replace_once(original, boundary, extra + boundary, '56 digest coverage rejections')
    return changes


def additions():
    results, definitions = [], []
    for m in MODULES:
        code = support.safe_source((PRIOR_TREE / 'Coq/C' / (m + '.v')).read_text(), m)
        results += ['C.' + m + ' ' + n for n in re.findall(r"^(?:Lemma|Theorem|Corollary)\s+([A-Za-z_][\w']*)", code, re.M)]
        definitions += ['C.' + m + ' ' + n for n in re.findall(r"^(?:Definition|Fixpoint|Record)\s+([A-Za-z_][\w']*)", code, re.M)]
    if (len(results), len(definitions)) != (19, 11):
        raise ValueError('wrong digest public inventory')
    if {m for m, _ in normal.rows(BASE / 'C/jet_public_theorems.txt')} & {'C.' + m for m in MODULES}:
        raise ValueError('printer rule affects inherited records')
    return {'_CoqProject': NEW_SOURCES, '_CoqProject.jets': NEW_SOURCES,
            'C/jet_public_theorems.txt': results, 'C/jet_contract_definitions.txt': definitions}


def predecessor_source():
    if (support.inputs.fingerprint(BASE, BASE_TREE) != PRED_REVIEW['candidate_input_sha256'] or
            PRED_REVIEW['review']['coverage_added'] != 7 or PRED_REVIEW['full_acceptance'] is not False):
        raise ValueError('reviewed predecessor source/scope drift')
    for n, h in PRED_REVIEW['tools_sha256'].items():
        if support.sha((PRED / n).read_bytes()) != h:
            raise ValueError('predecessor review tool drift')


def assemble():
    for directory in ['elements-script-hash', 'elements-issuance-proof']:
        subprocess.run([sys.executable, '-B', str(HERE.parent / directory / 'review.py')], check=True)
    predecessor_source()
    before, index = support.input_map(), support.index_hash()
    # The completed immutable seed supplies objects. Only source-text deltas
    # are read from the running predecessor, under its reviewed fingerprint.
    seed = predecessor.PRIOR_TREE
    work = Path(tempfile.mkdtemp(prefix='jet-digest-getters-admission.', dir='/tmp')).resolve()
    subprocess.run(['cp', '-cR', str(seed / 'Coq'), str(work / 'Coq')], check=True)
    for n in ['C', 'Haskell']:
        (work / n).symlink_to(REPO / n, target_is_directory=True)
    baseline_paths = predecessor.METADATA + predecessor.SCRIPTS + predecessor.GUARDS + predecessor.NEW_SOURCES
    support.changed({work / 'Coq' / n: (BASE / n).read_text() for n in baseline_paths})
    if support.inputs.fingerprint(work / 'Coq', work) != PRED_REVIEW['candidate_input_sha256']:
        raise ValueError('reconstructed predecessor source differs')
    baseline = dict(PRED_META['main_inputs'])
    baseline.update({'Coq/' + n: support.sha((BASE / n).read_bytes()) for n in baseline_paths})
    if before not in [PRED_META['main_inputs'], baseline]:
        raise ValueError('main is not an exact known predecessor checkpoint')
    extensions, changes = additions(), {}
    for n, rows in extensions.items():
        old = (BASE / n).read_text()
        if not old.endswith('\n') or any(row in old.splitlines() for row in rows):
            raise ValueError('nonfresh digest append')
        changes[work / 'Coq' / n] = old + '\n'.join(rows) + '\n'
    old = (BASE / 'C/jet_coverage.tsv').read_text()
    if {r.split()[0] for r in COVERAGE.splitlines()} & {r.split()[0] for r in old.splitlines() if r.strip()}:
        raise ValueError('digest jet already registered')
    changes[work / 'Coq/C/jet_coverage.tsv'] = old + COVERAGE
    changes.update({work / 'Coq' / n: (PRIOR_TREE / 'Coq' / n).read_text() for n in NEW_SOURCES})
    changes.update({work / 'Coq' / n: (HERE.parent / n).read_text() for n in GUARDS})
    changes.update({work / 'Coq' / n: text for n, text in script_changes().items()})
    support.changed(changes)
    meta = {'candidate': str(work), 'predecessor_candidate': str(BASE_TREE),
            'predecessor_input_sha256': PRED_REVIEW['candidate_input_sha256'],
            'predecessor_review_sha256': support.sha((PRED / 'REVIEW.json').read_bytes()),
            'main_inputs': before, 'main_input_sha256': support.inputs.fingerprint(MAIN, REPO),
            'baseline_inputs': baseline, 'staged_patch_sha256': index, 'extensions': extensions, 'coverage_additions': COVERAGE,
            'baseline_metadata_sha256': {n: support.sha((BASE / n).read_bytes()) for n in METADATA + SCRIPTS},
            'source_sha256': {'Coq/C/' + m + '.v': support.sha((work / 'Coq/C' / (m + '.v')).read_bytes()) for m in MODULES},
            'prior_preparations_sha256': {str(p.relative_to(HERE.parent)): support.sha(p.read_bytes()) for p in PRIOR_PATHS},
            'new_sources': NEW_SOURCES, 'coverage_added': 8, 'full_acceptance': False}
    write(work / 'ASSEMBLY.json', meta)
    write(HERE / 'ASSEMBLY.json', meta)
    print(json.dumps({'candidate': str(work), 'modules': 2, 'results': 19, 'definitions': 11, 'proposed_coverage': '386/533'}), flush=True)


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
    expected = {n: ds for r in PRIORS[:2] for n, ds in r['dependencies'].items()}
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
         'coverage_added': 8, 'full_acceptance': False}
    write(work / 'PREPARATION.json', r)
    write(HERE / 'PREPARATION.json', r)
    print('Eight-jet normal preparation complete; review, predecessor acceptance and own full acceptance still required', flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('action', choices=['assemble', 'prepare'])
    p.add_argument('work', nargs='?')
    args = p.parse_args()
    assemble() if args.action == 'assemble' else prepare(Path(args.work).resolve())
