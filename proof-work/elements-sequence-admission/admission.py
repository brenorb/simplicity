"""Prepare exact normal registration of the two actual-C sequence jets.

Main remains frozen while its count admission runs. New proof sources come
from the sealed final-C-name candidate, never from live compiler outputs.
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


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


support = load('sequence_admission_support', HERE.parent / 'elements-count/support.py')
normal = support.reports
snapshot_deps = load('sequence_admission_dependencies', HERE.parent / 'nullable-admission/review.py').dependencies
PRIOR = json.loads((HERE.parent / 'elements-sequence-normal/PREPARATION.json').read_text())
PRIOR_TREE = Path(PRIOR['candidate'])
MODULES = [m.removeprefix('C.') for m in PRIOR['missing_dependency_modules']]
NEW_SOURCES = ['C/jet_elements_sequence_literal.v', 'C/jet_elements_current_sequence_literal.v']
COVERAGE = ('simplicity_input_sequence C.jet_elements_indexed_scalar_jets elements_input_sequence_local_spec\n'
            'simplicity_current_sequence C.jet_elements_current_jets elements_current_sequence_local_spec\n')
METADATA = ['_CoqProject', '_CoqProject.jets', 'C/jet_public_theorems.txt', 'C/jet_contract_definitions.txt',
            'C/jet_coverage.tsv', 'C/jet_assumptions.expected', 'C/jet_contracts.expected']
SCRIPTS = ['jet-coverage.py', 'test-jet-coverage.py', 'check-jets.sh', 'audit-jet-contracts.sh']
GUARDS = [directory + '/' + script for directory in ['elements-sequence-review', 'elements-current-sequence']
          for script in ['check-source.py', 'test-source.py']]


def write(path, value):
    support.changed({path: json.dumps(value, indent=2) + '\n'})


def replace_once(text, old, new, label):
    if text.count(old) != 1:
        raise ValueError('unexpected sequence admission boundary: ' + label)
    return text.replace(old, new, 1)


def script_changes():
    changes = {}
    original = (MAIN / 'jet-coverage.py').read_text()
    old = '''        else:
            # Only these five selected primitive/program correspondences are reviewed so far.
            # Its literal target and environment relation have a source gate.
            contract = (rf"\\bapplication_jet_local_spec\\s+f_{re.escape(name)}\\s+"
                        r"elements_ge\\s+Elements\\.env\\s+Ty\\.Unit\\s+Word32\\b"
                        if name in {"simplicity_version", "simplicity_lock_time", "simplicity_current_index", "simplicity_num_inputs", "simplicity_num_outputs"} else r"(?!)")'''
    new = '''        else:
            # Only these seven selected correspondences have a reviewed
            # literal target, environment relation and whole-C-contract gate.
            if name == "simplicity_input_sequence":
                contract = (rf"\\bapplication_jet_local_spec_sep\\s+f_{re.escape(name)}\\s+"
                            r"elements_ge\\s+Elements\\.env\\s+Word32\\s+"
                            r"\\(Ty\\.Sum\\s+Ty\\.Unit\\s+Word32\\)")
            else:
                contract = (rf"\\bapplication_jet_local_spec\\s+f_{re.escape(name)}\\s+"
                            r"elements_ge\\s+Elements\\.env\\s+Ty\\.Unit\\s+Word32\\b"
                            if name in {"simplicity_version", "simplicity_lock_time", "simplicity_current_index", "simplicity_num_inputs", "simplicity_num_outputs", "simplicity_current_sequence"} else r"(?!)")'''
    changes['jet-coverage.py'] = replace_once(original, old, new, 'selected coverage types')
    original = (MAIN / 'check-jets.sh').read_text()
    boundary = 'python3 elements-count-review/test-source.py "${JET_C_REPO:-..}" .\n'
    extra = ('python3 elements-sequence-review/check-source.py --repo "${JET_C_REPO:-..}" --coq . --literal C/jet_elements_sequence_literal.v\n'
             'python3 elements-sequence-review/test-source.py "${JET_C_REPO:-..}" . C/jet_elements_sequence_literal.v\n'
             'python3 elements-current-sequence/check-source.py --repo "${JET_C_REPO:-..}" --coq . --sequence C/jet_elements_sequence_literal.v --literal C/jet_elements_current_sequence_literal.v\n'
             'python3 elements-current-sequence/test-source.py "${JET_C_REPO:-..}" . C/jet_elements_sequence_literal.v C/jet_elements_current_sequence_literal.v\n')
    changes['check-jets.sh'] = replace_once(original, boundary, boundary + extra, 'normal source gates')
    original = (MAIN / 'audit-jet-contracts.sh').read_text()
    old = '  awk \'!/^#/ && NF==2 {printf "Check %s.%s.\\n", $1, $2}\' C/jet_public_theorems.txt'
    selected = '|'.join(m.removeprefix('jet_elements_') for m in MODULES)
    # These modules have no inherited public records. Expose their implicit
    # parameters without changing the printer behavior of any old record.
    new = ('  awk \'!/^#/ && NF==2 {\n'
           '    explicit = ($1 ~ /^C\\.jet_elements_(' + selected + ')$/)\n'
           '    printf "Check %s%s.%s.\\n", (explicit ? "@" : ""), $1, $2\n'
           '  }\' C/jet_public_theorems.txt')
    changes['audit-jet-contracts.sh'] = replace_once(original, old, new, 'fully quantified new types')
    original = (MAIN / 'test-jet-coverage.py').read_text()
    boundary = '    print("coverage tests passed: exact core/partial/application contracts; wrong function/global/logical environment and unknown/duplicate/helper/unaudited entries rejected")'
    extra = '''        # Sequence contracts have different frame/input/output shapes. Test
        # each whole proposition, never compiled fake proofs.
        for suffix, module, contract in [
            ('input_sequence', 'C.jet_elements_indexed_scalar_jets', 'application_jet_local_spec_sep'),
            ('current_sequence', 'C.jet_elements_current_jets', 'application_jet_local_spec'),
        ]:
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
                ('Elements.env ' + ('Word32' if suffix == 'input_sequence' else 'Ty.Unit Word32'),
                 'Elements.env ' + ('Word64' if suffix == 'input_sequence' else 'Ty.Unit Word64')),
                (declaration, declaration + ' False ->'),
                (contract + ' f_simplicity_' + suffix, 'jet_local_spec f_simplicity_' + suffix),
            ]:
                start = text.index(declaration)
                assert old in text[start:]
                file.write_text(text[:start] + text[start:].replace(old, new, 1))
                rejects(coverage.inventory, 'not a direct canonical jet theorem')
            file.write_text(text)
            assert coverage.inventory()
'''
    changes['test-jet-coverage.py'] = replace_once(original, boundary, extra + boundary, 'new negative fixtures')
    return changes


def additions():
    results, definitions = [], []
    if len(MODULES) != 18:
        raise ValueError('unexpected sequence dependency inventory')
    for module in MODULES:
        code = support.safe_source((PRIOR_TREE / 'Coq/C' / (module + '.v')).read_text(), module)
        results += ['C.' + module + ' ' + n for n in re.findall(r'^(?:Lemma|Theorem|Corollary)\s+(\w+)', code, re.M)]
        definitions += ['C.' + module + ' ' + n for n in re.findall(r'^(?:Definition|Fixpoint)\s+(\w+)', code, re.M)]
    if (len(results), len(definitions)) != (98, 41):
        raise ValueError('unexpected public sequence inventory')
    old_modules = {m for m, _ in normal.rows(MAIN / 'C/jet_public_theorems.txt')}
    if old_modules & {'C.' + m for m in MODULES}:
        raise ValueError('new printer rule would affect inherited records')
    return {'_CoqProject': ['C/' + m + '.v' for m in MODULES],
            '_CoqProject.jets': ['C/' + m + '.v' for m in MODULES],
            'C/jet_public_theorems.txt': results, 'C/jet_contract_definitions.txt': definitions}


def assemble():
    # Recheck actual proof sources, compiled objects and completed checker logs.
    subprocess.run([sys.executable, '-B', str(HERE.parent / 'elements-sequence-normal/review.py')], check=True)
    subprocess.run([sys.executable, '-B', str(HERE.parent / 'elements-count-admission/post-check.py')], check=True)
    if support.inputs.fingerprint(MAIN, REPO) != PRIOR['main_input_sha256']:
        raise ValueError('sequence proof source base no longer matches main')
    work = Path(tempfile.mkdtemp(prefix='jet-sequence-admission.', dir='/tmp')).resolve()
    subprocess.run(['cp', '-cR', str(PRIOR_TREE / 'Coq'), str(work / 'Coq')], check=True)
    for name in ['C', 'Haskell']:
        (work / name).symlink_to(REPO / name, target_is_directory=True)
    extensions = additions()
    changes = {}
    for name, rows in extensions.items():
        old = (MAIN / name).read_text()
        if not old.endswith('\n') or any(row in old.splitlines() for row in rows):
            raise ValueError('nonfresh sequence inventory extension')
        changes[work / 'Coq' / name] = old + '\n'.join(rows) + '\n'
    old = (MAIN / 'C/jet_coverage.tsv').read_text()
    if any(line.split()[:1] in [['simplicity_input_sequence'], ['simplicity_current_sequence']] for line in old.splitlines()):
        raise ValueError('sequence already registered')
    changes[work / 'Coq/C/jet_coverage.tsv'] = old + COVERAGE
    changes.update({work / 'Coq' / name: text for name, text in script_changes().items()})
    for name in GUARDS:
        changes[work / 'Coq' / name] = (HERE.parent / name).read_text()
    support.changed(changes)
    meta = {'candidate': str(work), 'extensions': extensions, 'coverage_additions': COVERAGE,
            'main_input_sha256': support.inputs.fingerprint(MAIN, REPO), 'main_inputs': support.input_map(),
            'staged_patch_sha256': support.index_hash(),
            'main_head': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=REPO, text=True).strip(),
            'main_metadata_sha256': {n: support.sha((MAIN / n).read_bytes()) for n in METADATA + SCRIPTS},
            'source_sha256': {'Coq/C/' + m + '.v': support.sha((work / 'Coq/C' / (m + '.v')).read_bytes()) for m in MODULES},
            'prior_preparation_sha256': support.sha((HERE.parent / 'elements-sequence-normal/PREPARATION.json').read_bytes()),
            'new_sources': NEW_SOURCES, 'coverage_added': 2, 'full_acceptance': False}
    write(work / 'ASSEMBLY.json', meta)
    write(HERE / 'ASSEMBLY.json', meta)
    print(json.dumps({'candidate': str(work), 'modules': len(MODULES), 'new_results': 98, 'new_definitions': 41}), flush=True)


def command(work, command, stem, timeout=10800):
    return support.run(work, command, stem, timeout)


def prepare(work):
    meta = json.loads((work / 'ASSEMBLY.json').read_text())
    built = command(work, ['bash', 'build-jets.sh', '-j2'], 'build')
    print('Whole sequence candidate built; freshly compiling every new dependency', flush=True)
    fresh = {m: command(work, ['bash', 'build-jets.sh', '--coqc', '-q', 'C/' + m + '.v'], 'fresh-' + m, 180) for m in MODULES}
    coq = work / 'Coq'
    new_results = [tuple(row.split()) for row in meta['extensions']['C/jet_public_theorems.txt']]
    new_defs = [tuple(row.split()) for row in meta['extensions']['C/jet_contract_definitions.txt']]
    all_rows = normal.rows(coq / 'C/jet_public_theorems.txt') + normal.rows(coq / 'C/jet_contract_definitions.txt')
    driver = ['Set Warnings "-notation-overridden".']
    for module in sorted({m for m, _ in all_rows}):
        keyword = ('Require' if module.startswith(('Simplicity.', 'C.jet_elements_')) or
                   module == 'C.jet_secp_umul128_exec' else 'Require Import')
        driver.append(keyword + ' ' + module + '.')
    assumptions = driver[:]
    for m, n in new_results:
        name = m + '.' + n
        assumptions += ['Goal True. idtac "JET_ASSUMPTIONS ' + name + '". exact I. Qed.', 'Print Assumptions ' + name + '.']
    wanted = [('TYPE', m + '.' + n) for m, n in new_results] + [('DEF', m + '.' + n) for m, n in new_defs]
    driver += ['Import Simplicity.BitMachine Simplicity.Translate.', 'Set Printing All.', 'Set Printing Width 120.']
    for depth, marker in [(50, 'SEQUENCE_COMPACT_'), (1000000, 'SEQUENCE_DEEP_')]:
        driver += ['Set Printing Depth ' + str(depth) + '.']
        for kind, name in wanted:
            driver += ['Goal True. idtac "' + marker + kind + ' ' + name + '". exact I. Qed.',
                       ('Check @' if kind == 'TYPE' else 'Print ') + name + '.']
    support.changed({work / 'new_contracts.v': '\n'.join(driver) + '\n',
                     work / 'new_assumptions.v': '\n'.join(assumptions) + '\n'})
    contracts = command(work, ['bash', 'build-jets.sh', '--coqc', '-q', str(work / 'new_contracts.v')], 'new_contracts')
    audited = command(work, ['bash', 'build-jets.sh', '--coqc', '-q', str(work / 'new_assumptions.v')], 'new_assumptions')
    report = (work / 'new_contracts.log').read_text().split('SEQUENCE_DEEP_', 1)[0]
    marks = list(re.finditer(r'(?m)^SEQUENCE_COMPACT_(TYPE|DEF) (\S+)\n', report))
    if [(m[1], m[2]) for m in marks] != wanted or report[:marks[0].start()]:
        raise ValueError('wrong compact report inventory')
    bodies = {wanted[i]: ''.join(line.rstrip() + '\n' for line in report[m.end():marks[i+1].start() if i+1 < len(marks) else len(report)].splitlines())
              for i, m in enumerate(marks)}
    inherited = normal.contract_records((MAIN / 'C/jet_contracts.expected').read_text(),
                                        normal.rows(MAIN / 'C/jet_public_theorems.txt'), normal.rows(MAIN / 'C/jet_contract_definitions.txt'))
    snapshot = ''.join(t for (kind, _, _, _), t in inherited if kind == 'TYPE')
    snapshot += ''.join(bodies[('TYPE', m + '.' + n)] for m, n in new_results)
    snapshot += ''.join(t for (kind, _, _, _), t in inherited if kind == 'DEF')
    snapshot += ''.join(bodies[('DEF', m + '.' + n)] for m, n in new_defs)
    deps = normal.assumptions((work / 'new_assumptions.log').read_text())
    if set(deps) != {m + '.' + n for m, n in new_results} or any(not ds <= support.SIX for ds in deps.values()):
        raise ValueError('unexpected new assumptions')
    old_deps = snapshot_deps((MAIN / 'C/jet_assumptions.expected').read_text())
    if set(old_deps) & set(deps):
        raise ValueError('new results overwrite inherited dependencies')
    old_deps.update({name: sorted(ds) for name, ds in deps.items()})
    text = ''.join(n + ' : ' + (', '.join(ds) or 'closed') + '\n' for n, ds in sorted(old_deps.items()))
    support.changed({coq / 'C/jet_contracts.expected': snapshot, coq / 'C/jet_assumptions.expected': text})
    if support.input_map() != meta['main_inputs'] or support.index_hash() != meta['staged_patch_sha256']:
        raise ValueError('main inputs/staging changed during preparation')
    receipt = {'candidate': str(work), 'build': built, 'fresh_compiles': fresh,
               'contracts': contracts, 'assumptions': audited,
               'new_dependencies': {n: sorted(ds) for n, ds in deps.items()},
               'new_objects_sha256': {'Coq/C/' + m + '.vo': support.sha((coq / 'C' / (m + '.vo')).read_bytes()) for m in MODULES},
               'coverage_added': 2, 'full_acceptance': False}
    write(work / 'PREPARATION.json', receipt)
    write(HERE / 'PREPARATION.json', receipt)
    print('Sequence snapshots prepared; exact delta review and full acceptance remain required', flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('action', choices=['assemble', 'prepare'])
    parser.add_argument('work', nargs='?')
    args = parser.parse_args()
    if args.action == 'assemble':
        assemble()
    else:
        prepare(Path(args.work).resolve())
