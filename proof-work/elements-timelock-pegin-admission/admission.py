"""Normal admission preparation for seven checked Elements C contracts."""
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
spec = importlib.util.spec_from_file_location('seven_admission_base', HERE.parent / 'elements-direct-getters-admission/admission.py')
base = importlib.util.module_from_spec(spec)
spec.loader.exec_module(base)
support, normal, snapshot_deps = base.support, base.normal, base.snapshot_deps
replace_once, write = base.replace_once, base.write
PRIOR_PATHS = [HERE.parent / n / 'PREPARATION.json' for n in ['elements-check-lock-normal', 'elements-pegin-normal']]
PRIORS = [json.loads(p.read_text()) for p in PRIOR_PATHS]
PRIOR_TREE = Path(PRIORS[1]['candidate'])
MODULES = [m.removeprefix('C.') for r in PRIORS for m in r['missing_dependency_modules']]
NEW_SOURCES = ['C/' + m + '.v' for m in ['jet_elements_lock_literal', 'jet_application_partial_transport',
               'jet_elements_check_lock_literal', 'jet_elements_pegin_literal']]
METADATA, SCRIPTS = base.METADATA, base.SCRIPTS
GUARDS = [d + '/' + f for d in ['elements-finality', 'elements-lock', 'elements-check-lock', 'elements-pegin']
          for f in ['check-source.py', 'test-source.py']]
# Coverage points at the original actual-C contracts; mandatory source gates
# check their complete canonical targets and their checked literal transports.
ENDPOINTS = [
    ('tx_is_final', 'jet_elements_is_final_local', 'elements_tx_is_final_local_spec'),
    ('tx_lock_height', 'jet_elements_lock_local', 'elements_tx_lock_height_local_spec'),
    ('tx_lock_time', 'jet_elements_lock_local', 'elements_tx_lock_time_local_spec'),
    ('check_lock_height', 'jet_elements_check_lock', 'elements_check_lock_height_local_spec'),
    ('check_lock_time', 'jet_elements_check_lock', 'elements_check_lock_time_local_spec'),
    ('input_pegin', 'jet_elements_pegin_local', 'elements_input_pegin_hash_local_spec'),
    ('current_pegin', 'jet_elements_current_gen_jets', 'elements_current_pegin_local_spec'),
]
COVERAGE = ''.join('simplicity_' + f + ' C.' + m + ' ' + n + '\n' for f, m, n in ENDPOINTS)


def script_changes():
    changes = {}
    original = (MAIN / 'jet-coverage.py').read_text()
    old = '            if name in {"simplicity_tapleaf_version", "simplicity_script_cmr", "simplicity_genesis_block_hash"}:'
    new = r'''            if name == "simplicity_tx_is_final":
                contract = (rf"\bapplication_jet_local_spec_sep\s+f_{re.escape(name)}\s+"
                            r"elements_ge\s+Elements\.env\s+Ty\.Unit\s+Bit\b")
            elif name in {"simplicity_tx_lock_height", "simplicity_tx_lock_time"}:
                contract = (rf"\bapplication_jet_local_spec_sep\s+f_{re.escape(name)}\s+"
                            r"elements_ge\s+Elements\.env\s+Ty\.Unit\s+Word32\b")
            elif name in {"simplicity_check_lock_height", "simplicity_check_lock_time"}:
                contract = (rf"\bapplication_jet_partial_spec\s+f_{re.escape(name)}\s+"
                            r"elements_ge\s+Elements\.env\s+\(Word\s+5\)\s+Ty\.Unit\b")
            elif name == "simplicity_input_pegin":
                contract = (rf"\bapplication_jet_local_spec_sep\s+f_{re.escape(name)}\s+"
                            r"elements_ge\s+Elements\.env\s+Word32\s+"
                            r"\(Ty\.Sum\s+Ty\.Unit\s+\(Ty\.Sum\s+Ty\.Unit\s+Word256\)\)")
            elif name == "simplicity_current_pegin":
                contract = (rf"\bapplication_jet_local_spec_sep\s+f_{re.escape(name)}\s+"
                            r"elements_ge\s+Elements\.env\s+Ty\.Unit\s+\(Ty\.Sum\s+Ty\.Unit\s+Word256\)")
            elif name in {"simplicity_tapleaf_version", "simplicity_script_cmr", "simplicity_genesis_block_hash"}:'''
    changes['jet-coverage.py'] = replace_once(original, old, new, 'seven exact whole contract shapes').replace(
        '# Only these ten selected correspondences have a reviewed', '# Only these seventeen selected correspondences have a reviewed')
    original = (MAIN / 'check-jets.sh').read_text()
    old = 'python3 elements-hash-literal/test-source.py "${JET_C_REPO:-..}" . C/jet_haskell_hash_word.v C/jet_elements_hash_literal.v\n'
    extra = '''python3 elements-finality/check-source.py --repo "${JET_C_REPO:-..}" --coq .
python3 elements-finality/test-source.py "${JET_C_REPO:-..}" .
python3 elements-lock/check-source.py --repo "${JET_C_REPO:-..}" --coq . --literal C/jet_elements_lock_literal.v
python3 elements-lock/test-source.py "${JET_C_REPO:-..}" . C/jet_elements_lock_literal.v
python3 elements-check-lock/check-source.py --repo "${JET_C_REPO:-..}" --coq . --literal C/jet_elements_check_lock_literal.v --transport C/jet_application_partial_transport.v
python3 elements-check-lock/test-source.py "${JET_C_REPO:-..}" . C/jet_elements_check_lock_literal.v C/jet_application_partial_transport.v
python3 elements-pegin/check-source.py --repo "${JET_C_REPO:-..}" --coq . --literal C/jet_elements_pegin_literal.v
python3 elements-pegin/test-source.py "${JET_C_REPO:-..}" . C/jet_elements_pegin_literal.v
'''
    changes['check-jets.sh'] = replace_once(original, old, old + extra, 'mandatory canonical-source gates')
    original = (MAIN / 'audit-jet-contracts.sh').read_text()
    old = '         /^C\\.jet_haskell_hash_word$/ {print "Require " $0 "."; next}'
    original = replace_once(original, old, old + '\n         /^C\\.jet_application_partial_transport$/ {print "Require " $0 "."; next}', 'do not open shared transport')
    lines = re.findall(r'(?m)^    explicit = .*$', original)
    if len(lines) != 1:
        raise ValueError('ambiguous explicit-printer rule')
    selected = '|'.join('C[.]' + m for m in MODULES)
    changes['audit-jet-contracts.sh'] = replace_once(original, lines[0], lines[0] + ' || ($1 ~ /^(' + selected + ')$/)', 'scoped explicit parameters')
    original = (MAIN / 'test-jet-coverage.py').read_text()
    boundary = '    print("coverage tests passed: exact core/partial/application contracts; wrong function/global/logical environment and unknown/duplicate/helper/unaudited entries rejected")'
    extra = '''        # Seven whole-C contracts, including both failure-return contracts
        # and both pegin tags. These corrupted fixtures are never compiled.
        for suffix, filename, theorem, domain, output, contract in [
            ('tx_is_final', 'is_final_local', 'elements_tx_is_final_local_spec', 'Ty.Unit', 'Bit', 'application_jet_local_spec_sep'),
            ('tx_lock_height', 'lock_local', 'elements_tx_lock_height_local_spec', 'Ty.Unit', 'Word32', 'application_jet_local_spec_sep'),
            ('tx_lock_time', 'lock_local', 'elements_tx_lock_time_local_spec', 'Ty.Unit', 'Word32', 'application_jet_local_spec_sep'),
            ('check_lock_height', 'check_lock', 'elements_check_lock_height_local_spec', '(Word 5)', 'Ty.Unit', 'application_jet_partial_spec'),
            ('check_lock_time', 'check_lock', 'elements_check_lock_time_local_spec', '(Word 5)', 'Ty.Unit', 'application_jet_partial_spec'),
            ('input_pegin', 'pegin_local', 'elements_input_pegin_hash_local_spec', 'Word32', '(Ty.Sum Ty.Unit (Ty.Sum Ty.Unit Word256))', 'application_jet_local_spec_sep'),
            ('current_pegin', 'current_gen_jets', 'elements_current_pegin_local_spec', 'Ty.Unit', '(Ty.Sum Ty.Unit Word256)', 'application_jet_local_spec_sep'),
        ]:
            module = 'C.jet_elements_' + filename
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
                (contract + ' f_simplicity_' + suffix, 'application_jet_local_spec f_simplicity_' + suffix),
            ]:
                start = text.index(declaration)
                stop = text.index('Proof.', start)
                tail = text[start:stop]
                # Normalize whitespace only to locate the exact type fragment.
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
    changes['test-jet-coverage.py'] = replace_once(original, boundary, extra + boundary, '49 negative coverage fixtures')
    return changes


def additions():
    if len(MODULES) != 34 or len(set(MODULES)) != 34:
        raise ValueError('wrong combined dependency closure')
    results, definitions = [], []
    for m in MODULES:
        code = support.safe_source((PRIOR_TREE / 'Coq/C' / (m + '.v')).read_text(), m)
        results += ['C.' + m + ' ' + n for n in re.findall(r"^(?:Lemma|Theorem|Corollary)\s+([A-Za-z_][\w']*)", code, re.M)]
        definitions += ['C.' + m + ' ' + n for n in re.findall(r"^(?:Definition|Fixpoint|Record)\s+([A-Za-z_][\w']*)", code, re.M)]
    if (len(results), len(definitions)) != (308, 208):
        raise ValueError('wrong apostrophe-aware combined inventory')
    inherited = {m for m, _ in normal.rows(MAIN / 'C/jet_public_theorems.txt')}
    if inherited & {'C.' + m for m in MODULES}:
        raise ValueError('printer extension affects inherited module')
    return {'_CoqProject': ['C/' + m + '.v' for m in MODULES], '_CoqProject.jets': ['C/' + m + '.v' for m in MODULES],
            'C/jet_public_theorems.txt': results, 'C/jet_contract_definitions.txt': definitions}


def assemble():
    for directory in ['elements-check-lock-normal', 'elements-pegin-normal']:
        subprocess.run([sys.executable, '-B', str(HERE.parent / directory / 'review.py')], check=True)
    subprocess.run([sys.executable, '-B', str(HERE.parent / 'elements-direct-getters-admission/post-check.py')], check=True)
    before, index = support.input_map(), support.index_hash()
    for name, digest in before.items():
        if support.sha((PRIOR_TREE / name).read_bytes()) != digest:
            raise ValueError('immutable source base does not match current main: ' + name)
    work = Path(tempfile.mkdtemp(prefix='jet-timelock-pegin-admission.', dir='/tmp')).resolve()
    subprocess.run(['cp', '-cR', str(PRIOR_TREE / 'Coq'), str(work / 'Coq')], check=True)
    for name in ['C', 'Haskell']:
        (work / name).symlink_to(REPO / name, target_is_directory=True)
    extensions, changes = additions(), {}
    for name, rows in extensions.items():
        old = (MAIN / name).read_text()
        if not old.endswith('\n') or any(row in old.splitlines() for row in rows):
            raise ValueError('nonfresh inventory append')
        changes[work / 'Coq' / name] = old + '\n'.join(rows) + '\n'
    old = (MAIN / 'C/jet_coverage.tsv').read_text()
    if {row.split()[0] for row in COVERAGE.splitlines()} & {row.split()[0] for row in old.splitlines() if row.strip()}:
        raise ValueError('selected jet already registered')
    changes[work / 'Coq/C/jet_coverage.tsv'] = old + COVERAGE
    changes.update({work / 'Coq' / n: text for n, text in script_changes().items()})
    changes.update({work / 'Coq' / n: (HERE.parent / n).read_text() for n in GUARDS})
    support.changed(changes)
    meta = {'candidate': str(work), 'extensions': extensions, 'coverage_additions': COVERAGE,
            'main_input_sha256': support.inputs.fingerprint(MAIN, REPO), 'main_inputs': before, 'staged_patch_sha256': index,
            'main_metadata_sha256': {n: support.sha((MAIN / n).read_bytes()) for n in METADATA + SCRIPTS},
            'source_sha256': {'Coq/C/' + m + '.v': support.sha((work / 'Coq/C' / (m + '.v')).read_bytes()) for m in MODULES},
            'prior_preparations_sha256': {p.parent.name: support.sha(p.read_bytes()) for p in PRIOR_PATHS},
            'new_sources': NEW_SOURCES, 'coverage_added': 7, 'full_acceptance': False}
    write(work / 'ASSEMBLY.json', meta)
    write(HERE / 'ASSEMBLY.json', meta)
    print(json.dumps({'candidate': str(work), 'modules': 34, 'results': 308, 'definitions': 208}), flush=True)


def command(work, args, stem, timeout=10800):
    return support.run(work, args, stem, timeout)


def prepare(work):
    meta = json.loads((work / 'ASSEMBLY.json').read_text())
    built = command(work, ['bash', 'build-jets.sh', '-j2'], 'build')
    print('Whole candidate built; freshly compiling all 34 additions', flush=True)
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
        name = m + '.' + n
        assumptions += ['Goal True. idtac "JET_ASSUMPTIONS ' + name + '". exact I. Qed.', 'Print Assumptions ' + name + '.']
    wanted = [('TYPE', m + '.' + n) for m, n in results] + [('DEF', m + '.' + n) for m, n in definitions]
    driver += ['Import Simplicity.BitMachine Simplicity.Translate.', 'Set Printing All.', 'Set Printing Width 120.']
    for depth, marker in [(50, 'SEVEN_COMPACT_'), (1000000, 'SEVEN_DEEP_')]:
        driver += ['Set Printing Depth ' + str(depth) + '.']
        for kind, name in wanted:
            driver += ['Goal True. idtac "' + marker + kind + ' ' + name + '". exact I. Qed.',
                       ('Check @' if kind == 'TYPE' else 'Print ') + name + '.']
    support.changed({work / 'new_contracts.v': '\n'.join(driver) + '\n', work / 'new_assumptions.v': '\n'.join(assumptions) + '\n'})
    contracts = command(work, ['bash', 'build-jets.sh', '--coqc', '-q', str(work / 'new_contracts.v')], 'new_contracts')
    audited = command(work, ['bash', 'build-jets.sh', '--coqc', '-q', str(work / 'new_assumptions.v')], 'new_assumptions')
    report = (work / 'new_contracts.log').read_text().split('SEVEN_DEEP_', 1)[0]
    marks = list(re.finditer(r'(?m)^SEVEN_COMPACT_(TYPE|DEF) (\S+)\n', report))
    if [(m[1], m[2]) for m in marks] != wanted or report[:marks[0].start()]:
        raise ValueError('incomplete compact report')
    bodies = {wanted[i]: ''.join(line.rstrip() + '\n' for line in report[m.end():marks[i+1].start() if i+1 < len(marks) else len(report)].splitlines())
              for i, m in enumerate(marks)}
    inherited = normal.contract_records((MAIN / 'C/jet_contracts.expected').read_text(),
                                        normal.rows(MAIN / 'C/jet_public_theorems.txt'), normal.rows(MAIN / 'C/jet_contract_definitions.txt'))
    snapshot = ''.join(t for (k, _, _, _), t in inherited if k == 'TYPE')
    snapshot += ''.join(bodies[('TYPE', m + '.' + n)] for m, n in results)
    snapshot += ''.join(t for (k, _, _, _), t in inherited if k == 'DEF')
    snapshot += ''.join(bodies[('DEF', m + '.' + n)] for m, n in definitions)
    deps = normal.assumptions((work / 'new_assumptions.log').read_text())
    prior_deps = {n: ds for r in PRIORS for n, ds in r['dependencies'].items()}
    if set(deps) != {m + '.' + n for m, n in results} or any(sorted(ds) != prior_deps[n] for n, ds in deps.items()):
        raise ValueError('combined source changed checked assumption sets')
    old_deps = snapshot_deps((MAIN / 'C/jet_assumptions.expected').read_text())
    if set(old_deps) & set(deps):
        raise ValueError('overlapping assumption records')
    old_deps.update({n: sorted(ds) for n, ds in deps.items()})
    text = ''.join(n + ' : ' + (', '.join(ds) or 'closed') + '\n' for n, ds in sorted(old_deps.items()))
    support.changed({coq / 'C/jet_contracts.expected': snapshot, coq / 'C/jet_assumptions.expected': text})
    if support.input_map() != meta['main_inputs'] or support.index_hash() != meta['staged_patch_sha256']:
        raise ValueError('main/index changed')
    receipt = {'candidate': str(work), 'build': built, 'fresh_compiles': fresh, 'contracts': contracts, 'assumptions': audited,
               'new_dependencies': {n: sorted(ds) for n, ds in deps.items()},
               'new_objects_sha256': {'Coq/C/' + m + '.vo': support.sha((coq / 'C' / (m + '.vo')).read_bytes()) for m in MODULES},
               'coverage_added': 7, 'full_acceptance': False}
    write(work / 'PREPARATION.json', receipt)
    write(HERE / 'PREPARATION.json', receipt)
    print('Seven-jet normal preparation complete; independent review/full acceptance still required', flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('action', choices=['assemble', 'prepare'])
    p.add_argument('work', nargs='?')
    args = p.parse_args()
    assemble() if args.action == 'assemble' else prepare(Path(args.work).resolve())
