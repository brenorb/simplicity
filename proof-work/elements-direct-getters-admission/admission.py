"""Isolated normal admission of the three checked direct Elements getters."""
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


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


support = load('direct_admission_support', HERE.parent / 'elements-count/support.py')
normal = support.reports
snapshot_deps = load('direct_admission_dependencies', HERE.parent / 'nullable-admission/review.py').dependencies
PRIOR = json.loads((HERE.parent / 'elements-direct-getters-normal/PREPARATION.json').read_text())
PRIOR_TREE = Path(PRIOR['candidate'])
MODULES = [m.removeprefix('C.') for m in PRIOR['missing_dependency_modules']]
NEW_SOURCES = ['C/' + m + '.v' for m in PRIOR['modules']]
COVERAGE = ('simplicity_tapleaf_version C.jet_elements_tapleaf_version_local elements_tapleaf_version_local_spec\n'
            'simplicity_script_cmr C.jet_elements_script_cmr_local elements_script_cmr_local_spec\n'
            'simplicity_genesis_block_hash C.jet_elements_genesis_hash_local elements_genesis_block_hash_local_spec\n')
METADATA = ['_CoqProject', '_CoqProject.jets', 'C/jet_public_theorems.txt', 'C/jet_contract_definitions.txt',
            'C/jet_coverage.tsv', 'C/jet_assumptions.expected', 'C/jet_contracts.expected']
SCRIPTS = ['jet-coverage.py', 'test-jet-coverage.py', 'check-jets.sh', 'audit-jet-contracts.sh']
GUARDS = [d + '/' + s for d in ['elements-tapleaf-literal', 'elements-hash-literal'] for s in ['check-source.py', 'test-source.py']]


def write(path, value):
    support.changed({path: json.dumps(value, indent=2) + '\n'})


def replace_once(text, old, new, label):
    if text.count(old) != 1:
        raise ValueError('unexpected direct admission boundary: ' + label)
    return text.replace(old, new, 1)


def script_changes():
    changes = {}
    original = (MAIN / 'jet-coverage.py').read_text()
    old = '            if name == "simplicity_input_sequence":'
    new = '''            if name in {"simplicity_tapleaf_version", "simplicity_script_cmr", "simplicity_genesis_block_hash"}:
                output = "Word8" if name == "simplicity_tapleaf_version" else "Word256"
                contract = (rf"\\bapplication_jet_local_spec_sep\\s+f_{re.escape(name)}\\s+"
                            rf"elements_ge\\s+Elements\\.env\\s+Ty\\.Unit\\s+{output}\\b")
            elif name == "simplicity_input_sequence":'''
    changes['jet-coverage.py'] = replace_once(original, old, new, 'three exact separated getter shapes').replace(
        '# Only these seven selected correspondences have a reviewed', '# Only these ten selected correspondences have a reviewed')
    original = (MAIN / 'check-jets.sh').read_text()
    old = 'python3 elements-current-sequence/test-source.py "${JET_C_REPO:-..}" . C/jet_elements_sequence_literal.v C/jet_elements_current_sequence_literal.v\n'
    extra = ('python3 elements-tapleaf-literal/check-source.py --repo "${JET_C_REPO:-..}" --coq . --literal C/jet_elements_tapleaf_literal.v\n'
             'python3 elements-tapleaf-literal/test-source.py "${JET_C_REPO:-..}" . C/jet_elements_tapleaf_literal.v\n'
             'python3 elements-hash-literal/check-source.py --repo "${JET_C_REPO:-..}" --coq . --helper C/jet_haskell_hash_word.v --endpoint C/jet_elements_hash_literal.v\n'
             'python3 elements-hash-literal/test-source.py "${JET_C_REPO:-..}" . C/jet_haskell_hash_word.v C/jet_elements_hash_literal.v\n')
    changes['check-jets.sh'] = replace_once(original, old, old + extra, 'mandatory selected source gates')
    original = (MAIN / 'audit-jet-contracts.sh').read_text()
    old = '         /^C\\.jet_elements_/ {print "Require " $0 "."; next}'
    new = ('         /^C\\.jet_haskell_hash_word$/ {print "Require " $0 "."; next}\n' + old)
    original = replace_once(original, old, new, 'load numeric helper without opening it')
    lines = re.findall(r'(?m)^    explicit = .*$', original)
    if len(lines) != 1:
        raise ValueError('ambiguous inherited explicit-printer rule')
    selected = '|'.join(re.escape('C.' + m).replace('\\.', '[.]') for m in MODULES)
    changes['audit-jet-contracts.sh'] = replace_once(original, lines[0], lines[0] + ' || ($1 ~ /^(' + selected + ')$/)', 'new-module-only explicit types')
    original = (MAIN / 'test-jet-coverage.py').read_text()
    boundary = '    print("coverage tests passed: exact core/partial/application contracts; wrong function/global/logical environment and unknown/duplicate/helper/unaudited entries rejected")'
    extra = '''        # Direct getters retain exact separated contracts, widths, linked
        # and logical environments. Never compile these corrupted fixtures.
        for suffix, filename, width in [
            ('tapleaf_version', 'tapleaf_version', 'Word8'),
            ('script_cmr', 'script_cmr', 'Word256'),
            ('genesis_block_hash', 'genesis_hash', 'Word256'),
        ]:
            module = 'C.jet_elements_' + filename + '_local'
            theorem = 'elements_' + suffix + '_local_spec'
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
                (width, 'Word16'),
                (declaration, declaration + ' False ->'),
                ('application_jet_local_spec_sep f_simplicity_' + suffix, 'jet_local_spec f_simplicity_' + suffix),
            ]:
                start = text.index(declaration)
                assert old in text[start:]
                file.write_text(text[:start] + text[start:].replace(old, new, 1))
                rejects(coverage.inventory, 'not a direct canonical jet theorem')
            file.write_text(text)
            assert coverage.inventory()
'''
    changes['test-jet-coverage.py'] = replace_once(original, boundary, extra + boundary, '18 new negative coverage fixtures')
    return changes


def additions():
    results, definitions = [], []
    if len(MODULES) != 11:
        raise ValueError('unexpected direct-getter dependency inventory')
    for module in MODULES:
        code = support.safe_source((PRIOR_TREE / 'Coq/C' / (module + '.v')).read_text(), module)
        results += ['C.' + module + ' ' + n for n in re.findall(r'^(?:Lemma|Theorem|Corollary)\s+(\w+)', code, re.M)]
        definitions += ['C.' + module + ' ' + n for n in re.findall(r'^(?:Definition|Fixpoint|Record)\s+(\w+)', code, re.M)]
    if (len(results), len(definitions)) != (75, 34):
        raise ValueError('unexpected direct getter public inventory')
    old = {m for m, _ in normal.rows(MAIN / 'C/jet_public_theorems.txt')}
    if old & {'C.' + m for m in MODULES}:
        raise ValueError('new printer rule would affect inherited public records')
    return {'_CoqProject': ['C/' + m + '.v' for m in MODULES],
            '_CoqProject.jets': ['C/' + m + '.v' for m in MODULES],
            'C/jet_public_theorems.txt': results, 'C/jet_contract_definitions.txt': definitions}


def assemble():
    subprocess.run([sys.executable, '-B', str(HERE.parent / 'elements-direct-getters-normal/review.py')], check=True)
    subprocess.run([sys.executable, '-B', str(HERE.parent / 'elements-sequence-admission/post-check.py')], check=True)
    if support.inputs.fingerprint(MAIN, REPO) != PRIOR['base_input_sha256']:
        raise ValueError('main no longer matches the reviewed getter source base')
    work = Path(tempfile.mkdtemp(prefix='jet-direct-getters-admission.', dir='/tmp')).resolve()
    subprocess.run(['cp', '-cR', str(PRIOR_TREE / 'Coq'), str(work / 'Coq')], check=True)
    for name in ['C', 'Haskell']:
        (work / name).symlink_to(REPO / name, target_is_directory=True)
    extensions, changes = additions(), {}
    for name, rows in extensions.items():
        old = (MAIN / name).read_text()
        if not old.endswith('\n') or any(row in old.splitlines() for row in rows):
            raise ValueError('nonfresh direct-getter inventory extension')
        changes[work / 'Coq' / name] = old + '\n'.join(rows) + '\n'
    old = (MAIN / 'C/jet_coverage.tsv').read_text()
    if any(row.split()[:1] in [r.split()[:1] for r in COVERAGE.splitlines()] for row in old.splitlines()):
        raise ValueError('direct getter already registered')
    changes[work / 'Coq/C/jet_coverage.tsv'] = old + COVERAGE
    changes.update({work / 'Coq' / n: text for n, text in script_changes().items()})
    for name in GUARDS:
        changes[work / 'Coq' / name] = (HERE.parent / name).read_text()
    support.changed(changes)
    meta = {'candidate': str(work), 'extensions': extensions, 'coverage_additions': COVERAGE,
            'main_input_sha256': support.inputs.fingerprint(MAIN, REPO), 'main_inputs': support.input_map(),
            'staged_patch_sha256': support.index_hash(),
            'main_head': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=REPO, text=True).strip(),
            'main_metadata_sha256': {n: support.sha((MAIN / n).read_bytes()) for n in METADATA + SCRIPTS},
            'source_sha256': {'Coq/C/' + m + '.v': support.sha((work / 'Coq/C' / (m + '.v')).read_bytes()) for m in MODULES},
            'prior_preparation_sha256': support.sha((HERE.parent / 'elements-direct-getters-normal/PREPARATION.json').read_bytes()),
            'new_sources': NEW_SOURCES, 'coverage_added': 3, 'full_acceptance': False}
    write(work / 'ASSEMBLY.json', meta)
    write(HERE / 'ASSEMBLY.json', meta)
    print(json.dumps({'candidate': str(work), 'modules': 11, 'new_results': 75, 'new_definitions': 34}), flush=True)


def command(work, args, stem, timeout=10800):
    return support.run(work, args, stem, timeout)


def prepare(work):
    meta = json.loads((work / 'ASSEMBLY.json').read_text())
    built = command(work, ['bash', 'build-jets.sh', '-j2'], 'build')
    print('Whole direct-getter candidate built; freshly compiling all eleven additions', flush=True)
    fresh = {m: command(work, ['bash', 'build-jets.sh', '--coqc', '-q', 'C/' + m + '.v'], 'fresh-' + m, 180) for m in MODULES}
    coq = work / 'Coq'
    new_results = [tuple(row.split()) for row in meta['extensions']['C/jet_public_theorems.txt']]
    new_defs = [tuple(row.split()) for row in meta['extensions']['C/jet_contract_definitions.txt']]
    all_rows = normal.rows(coq / 'C/jet_public_theorems.txt') + normal.rows(coq / 'C/jet_contract_definitions.txt')
    driver = ['Set Warnings "-notation-overridden".']
    for module in sorted({m for m, _ in all_rows}):
        keyword = ('Require' if module.startswith(('Simplicity.', 'C.jet_elements_')) or
                   module in {'C.jet_secp_umul128_exec', 'C.jet_haskell_hash_word'} else 'Require Import')
        driver.append(keyword + ' ' + module + '.')
    assumptions = driver[:]
    for m, n in new_results:
        name = m + '.' + n
        assumptions += ['Goal True. idtac "JET_ASSUMPTIONS ' + name + '". exact I. Qed.', 'Print Assumptions ' + name + '.']
    wanted = [('TYPE', m + '.' + n) for m, n in new_results] + [('DEF', m + '.' + n) for m, n in new_defs]
    driver += ['Import Simplicity.BitMachine Simplicity.Translate.', 'Set Printing All.', 'Set Printing Width 120.']
    for depth, marker in [(50, 'DIRECT_COMPACT_'), (1000000, 'DIRECT_DEEP_')]:
        driver += ['Set Printing Depth ' + str(depth) + '.']
        for kind, name in wanted:
            driver += ['Goal True. idtac "' + marker + kind + ' ' + name + '". exact I. Qed.',
                       ('Check @' if kind == 'TYPE' else 'Print ') + name + '.']
    support.changed({work / 'new_contracts.v': '\n'.join(driver) + '\n', work / 'new_assumptions.v': '\n'.join(assumptions) + '\n'})
    contracts = command(work, ['bash', 'build-jets.sh', '--coqc', '-q', str(work / 'new_contracts.v')], 'new_contracts')
    audited = command(work, ['bash', 'build-jets.sh', '--coqc', '-q', str(work / 'new_assumptions.v')], 'new_assumptions')
    report = (work / 'new_contracts.log').read_text().split('DIRECT_DEEP_', 1)[0]
    marks = list(re.finditer(r'(?m)^DIRECT_COMPACT_(TYPE|DEF) (\S+)\n', report))
    if [(m[1], m[2]) for m in marks] != wanted or report[:marks[0].start()]:
        raise ValueError('unexpected compact result/definition report')
    bodies = {wanted[i]: ''.join(line.rstrip() + '\n' for line in report[m.end():marks[i+1].start() if i+1 < len(marks) else len(report)].splitlines())
              for i, m in enumerate(marks)}
    inherited = normal.contract_records((MAIN / 'C/jet_contracts.expected').read_text(),
                                        normal.rows(MAIN / 'C/jet_public_theorems.txt'), normal.rows(MAIN / 'C/jet_contract_definitions.txt'))
    snapshot = ''.join(t for (kind, _, _, _), t in inherited if kind == 'TYPE')
    snapshot += ''.join(bodies[('TYPE', m + '.' + n)] for m, n in new_results)
    snapshot += ''.join(t for (kind, _, _, _), t in inherited if kind == 'DEF')
    snapshot += ''.join(bodies[('DEF', m + '.' + n)] for m, n in new_defs)
    deps = normal.assumptions((work / 'new_assumptions.log').read_text())
    pure = {m + '.' + n for m, n in new_results if m == 'C.jet_haskell_hash_word'}
    if set(deps) != {m + '.' + n for m, n in new_results} or any(not ds <= support.SIX for ds in deps.values()) or any(deps[n] for n in pure):
        raise ValueError('unexpected new assumptions; shared digest lemmas must remain closed')
    old_deps = snapshot_deps((MAIN / 'C/jet_assumptions.expected').read_text())
    if set(old_deps) & set(deps):
        raise ValueError('new result overwrites an inherited dependency record')
    old_deps.update({n: sorted(ds) for n, ds in deps.items()})
    text = ''.join(n + ' : ' + (', '.join(ds) or 'closed') + '\n' for n, ds in sorted(old_deps.items()))
    support.changed({coq / 'C/jet_contracts.expected': snapshot, coq / 'C/jet_assumptions.expected': text})
    if support.input_map() != meta['main_inputs'] or support.index_hash() != meta['staged_patch_sha256']:
        raise ValueError('main source/index changed during direct preparation')
    receipt = {'candidate': str(work), 'build': built, 'fresh_compiles': fresh, 'contracts': contracts, 'assumptions': audited,
               'new_dependencies': {n: sorted(ds) for n, ds in deps.items()},
               'new_objects_sha256': {'Coq/C/' + m + '.vo': support.sha((coq / 'C' / (m + '.vo')).read_bytes()) for m in MODULES},
               'coverage_added': 3, 'full_acceptance': False}
    write(work / 'PREPARATION.json', receipt)
    write(HERE / 'PREPARATION.json', receipt)
    print('Direct-getter snapshots prepared; independent review and full acceptance remain required', flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('action', choices=['assemble', 'prepare'])
    parser.add_argument('work', nargs='?')
    args = parser.parse_args()
    if args.action == 'assemble':
        assemble()
    else:
        prepare(Path(args.work).resolve())
