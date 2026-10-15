"""Two original-C Elements count jets: isolated normal-registry admission.

Assembly and preparation are not acceptance. Never write main metadata until
the entire copied normal registry passes --accept with reviewed snapshots.
"""
import argparse
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
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


support = load('count_admission_support', HERE.parent / 'elements-count/support.py')
normal = support.reports
snapshot_deps = load('count_admission_dependencies', HERE.parent / 'nullable-admission/review.py').dependencies
MODULES = ['jet_elements_count_canonical', 'jet_elements_count_bridge',
           'jet_elements_count_local', 'jet_elements_count_payload']
ROOTS = ['C.jet_elements_count_payload']
COVERAGE = ''.join('simplicity_' + suffix + ' C.jet_elements_count_local elements_' + suffix + '_local_spec\n'
                   for suffix in ['num_inputs', 'num_outputs'])
METADATA = ['_CoqProject', '_CoqProject.jets', 'C/jet_public_theorems.txt',
            'C/jet_contract_definitions.txt', 'C/jet_coverage.tsv',
            'C/jet_assumptions.expected', 'C/jet_contracts.expected']
SCRIPTS = ['jet-coverage.py', 'test-jet-coverage.py', 'check-jets.sh']
GUARDS = ['elements-count-review/check-source.py', 'elements-count-review/test-source.py']


def write(path, value):
    support.changed({path: json.dumps(value, indent=2) + '\n'})


def script_changes():
    changes = {}
    path = 'jet-coverage.py'
    original = (MAIN / path).read_text()
    old = 'if name in {"simplicity_version", "simplicity_lock_time", "simplicity_current_index"} else r"(?!)")'
    new = 'if name in {"simplicity_version", "simplicity_lock_time", "simplicity_current_index", "simplicity_num_inputs", "simplicity_num_outputs"} else r"(?!)")'
    if original.count(old) != 1:
        raise ValueError('unexpected Elements coverage whitelist')
    changes[path] = original.replace(old, new).replace(
        '# Only these three primitive correspondences are reviewed so far.',
        '# Only these five selected primitive/program correspondences are reviewed so far.')
    path = 'check-jets.sh'
    original = (MAIN / path).read_text()
    old = 'python3 elements-version-review/test-getters-source.py "${JET_C_REPO:-..}" .\n'
    if original.count(old) != 1:
        raise ValueError('unexpected normal static gate boundary')
    changes[path] = original.replace(old, old +
        'python3 elements-count-review/check-source.py --repo "${JET_C_REPO:-..}" --coq .\n' +
        'python3 elements-count-review/test-source.py "${JET_C_REPO:-..}" .\n')
    path = 'test-jet-coverage.py'
    original = (MAIN / path).read_text()
    old = '    print("coverage tests passed: exact core/partial/application contracts; wrong function/global/logical environment and unknown/duplicate/helper/unaudited entries rejected")'
    if original.count(old) != 1:
        raise ValueError('unexpected coverage test boundary')
    extra = '''        # Count contracts retain the exact function, linked environment, width
        # and entire proposition. The separate source gate pins their literal
        # firstFail specification and initial environment relation.
        for suffix in ['num_inputs', 'num_outputs']:
            module = 'C.jet_elements_count_local'
            theorem = 'elements_' + suffix + '_local_spec'
            file = project / 'C/jet_elements_count_local.v'
            shutil.copy2(SOURCE / 'C/jet_elements_count_local.v', file)
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
                ('Elements.env Ty.Unit Word32', 'Elements.env Ty.Unit Word64'),
                (declaration, declaration + ' False ->'),
                ('application_jet_local_spec f_simplicity_' + suffix, 'jet_local_spec f_simplicity_' + suffix),
            ]:
                start = text.index(declaration)
                assert old in text[start:]
                file.write_text(text[:start] + text[start:].replace(old, new, 1))
                rejects(coverage.inventory, 'not a direct canonical jet theorem')
            file.write_text(text)
            assert coverage.inventory()
'''
    changes[path] = original.replace(old, extra + old)
    return changes


def additions():
    results, definitions = [], []
    for module in MODULES:
        text = support.safe_source((MAIN / 'C' / (module + '.v')).read_text(), module)
        results += ['C.' + module + ' ' + n for n in re.findall(r'^(?:Lemma|Theorem)\s+(\w+)', text, re.M)]
        definitions += ['C.' + module + ' ' + n for n in re.findall(r'^Definition\s+(\w+)', text, re.M)]
    if (len(results), len(definitions)) != (18, 6):
        raise ValueError('unexpected count result/definition inventory')
    return {'_CoqProject': ['C/' + n + '.v' for n in MODULES],
            '_CoqProject.jets': ['C/' + n + '.v' for n in MODULES],
            'C/jet_public_theorems.txt': results, 'C/jet_contract_definitions.txt': definitions}


def assemble():
    prior = json.loads((HERE.parent / 'elements-count/payload/REVIEW.json').read_text())
    load('count_admission_prior', HERE.parent / 'elements-count/review.py').validate(Path(prior['candidate']))
    work = Path(tempfile.mkdtemp(prefix='jet-count-admission.', dir='/tmp')).resolve()
    subprocess.run(['cp', '-cR', str(MAIN), str(work / 'Coq')], check=True)
    for name in ['C', 'Haskell']:
        (work / name).symlink_to(REPO / name, target_is_directory=True)
    extensions = additions()
    changes = {}
    for name, rows in extensions.items():
        old = (MAIN / name).read_text()
        if not old.endswith('\n') or any(row in old.splitlines() for row in rows):
            raise ValueError('nonfresh normal inventory extension')
        changes[work / 'Coq' / name] = old + '\n'.join(rows) + '\n'
    old = (MAIN / 'C/jet_coverage.tsv').read_text()
    if any(row.split()[:1] in [['simplicity_num_inputs'], ['simplicity_num_outputs']] for row in old.splitlines()):
        raise ValueError('count already registered')
    changes[work / 'Coq/C/jet_coverage.tsv'] = old + COVERAGE
    changes.update({work / 'Coq' / n: text for n, text in script_changes().items()})
    for name in GUARDS:
        changes[work / 'Coq' / name] = (HERE.parent / 'elements-count' / Path(name).name).read_text()
    support.changed(changes)
    # Use freshly checked, source-identical dependency objects, never main
    # output symlinks. The full normal build still checks all its dependencies.
    reused = {}
    for receipt_path in [HERE.parent / 'elements-count/payload/REVIEW.json',
                         HERE.parent / 'secp-checked-conversions/REVIEW.json']:
        checked = json.loads(receipt_path.read_text())
        base = Path(checked['candidate'])
        for relative, digest in checked['evidence_sha256'].items():
            source = base / relative
            if not relative.startswith('Coq/') or source.suffix != '.vo':
                continue
            target = work / relative
            v = target.with_suffix('.v')
            if (v.exists() and source.exists() and source.with_suffix('.v').exists() and
                    source.with_suffix('.v').read_bytes() == v.read_bytes() and support.sha(source.read_bytes()) == digest):
                # All imported objects have their byte-identical sources and
                # exact checker receipt. New count modules are recompiled.
                if v.stem in MODULES:
                    continue
                stat = source.with_suffix('.v').stat()
                os.utime(v, ns=(stat.st_atime_ns, stat.st_mtime_ns))
                shutil.copy2(source, target)
                reused[relative] = digest
    meta = {'candidate': str(work), 'extensions': extensions, 'coverage_additions': COVERAGE,
            'main_head': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=REPO, text=True).strip(),
            'main_input_sha256': support.inputs.fingerprint(MAIN, REPO), 'main_inputs': support.input_map(),
            'staged_patch_sha256': support.index_hash(),
            'main_metadata_sha256': {n: support.sha((MAIN / n).read_bytes()) for n in METADATA + SCRIPTS},
            'source_sha256': {'Coq/C/' + n + '.v': support.sha((MAIN / 'C' / (n + '.v')).read_bytes()) for n in MODULES},
            'reused_checked_objects': reused, 'coverage_added': 2, 'full_acceptance': False}
    write(work / 'ASSEMBLY.json', meta)
    write(HERE / 'ASSEMBLY.json', meta)
    print(json.dumps({'candidate': str(work), 'new_modules': MODULES, 'new_results': 18,
                      'new_definitions': 6, 'reused_checked_objects': len(reused)}), flush=True)


def command(work, args, stem, timeout=10800):
    return support.run(work, args, stem, timeout)


def prepare(work):
    meta = json.loads((work / 'ASSEMBLY.json').read_text())
    built = command(work, ['bash', 'build-jets.sh', '-j2'], 'build')
    print('Whole normal candidate built; printing new records', flush=True)
    fresh = {n: command(work, ['bash', 'build-jets.sh', '--coqc', '-q', 'C/' + n + '.v'],
                        'fresh-' + n) for n in MODULES}
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
        full = m + '.' + n
        assumptions += ['Goal True. idtac "JET_ASSUMPTIONS ' + full + '". exact I. Qed.', 'Print Assumptions ' + full + '.']
    wanted = [('TYPE', m + '.' + n) for m, n in new_results] + [('DEF', m + '.' + n) for m, n in new_defs]
    driver += ['Import Simplicity.BitMachine Simplicity.Translate.', 'Set Printing All.', 'Set Printing Width 120.']
    for depth, marker in [(50, 'COUNT_COMPACT_'), (1000000, 'COUNT_DEEP_')]:
        driver += ['Set Printing Depth ' + str(depth) + '.']
        for kind, name in wanted:
            driver += ['Goal True. idtac "' + marker + kind + ' ' + name + '". exact I. Qed.',
                       ('Check ' if kind == 'TYPE' else 'Print ') + name + '.']
    support.changed({work / 'new_contracts.v': '\n'.join(driver) + '\n',
                     work / 'new_assumptions.v': '\n'.join(assumptions) + '\n'})
    contracts = command(work, ['bash', 'build-jets.sh', '--coqc', '-q', str(work / 'new_contracts.v')], 'new_contracts')
    audited = command(work, ['bash', 'build-jets.sh', '--coqc', '-q', str(work / 'new_assumptions.v')], 'new_assumptions')
    report = (work / 'new_contracts.log').read_text().split('COUNT_DEEP_', 1)[0]
    marks = list(re.finditer(r'(?m)^COUNT_COMPACT_(TYPE|DEF) (\S+)\n', report))
    if [(m[1], m[2]) for m in marks] != wanted or report[:marks[0].start()]:
        raise ValueError('wrong compact report inventory')
    bodies = {wanted[i]: ''.join(line.rstrip() + '\n' for line in report[m.end():marks[i+1].start() if i+1 < len(marks) else len(report)].splitlines())
              for i, m in enumerate(marks)}
    inherited = normal.contract_records((MAIN / 'C/jet_contracts.expected').read_text(),
                                        normal.rows(MAIN / 'C/jet_public_theorems.txt'), normal.rows(MAIN / 'C/jet_contract_definitions.txt'))
    snapshot = ''.join(text for (kind, _, _, _), text in inherited if kind == 'TYPE')
    snapshot += ''.join(bodies[('TYPE', m + '.' + n)] for m, n in new_results)
    snapshot += ''.join(text for (kind, _, _, _), text in inherited if kind == 'DEF')
    snapshot += ''.join(bodies[('DEF', m + '.' + n)] for m, n in new_defs)
    deps = normal.assumptions((work / 'new_assumptions.log').read_text())
    if set(deps) != {m + '.' + n for m, n in new_results} or any(not ds <= support.SIX for ds in deps.values()):
        raise ValueError('unexpected new assumption inventory')
    old_deps = snapshot_deps((MAIN / 'C/jet_assumptions.expected').read_text())
    if set(old_deps) & set(deps):
        raise ValueError('new results overwrite inherited dependency records')
    old_deps.update({name: sorted(ds) for name, ds in deps.items()})
    text = ''.join(n + ' : ' + (', '.join(ds) or 'closed') + '\n' for n, ds in sorted(old_deps.items()))
    support.changed({coq / 'C/jet_contracts.expected': snapshot, coq / 'C/jet_assumptions.expected': text})
    if (support.inputs.fingerprint(MAIN, REPO) != meta['main_input_sha256'] or
            support.index_hash() != meta['staged_patch_sha256']):
        raise ValueError('main inputs or staging changed during preparation')
    receipt = {'candidate': str(work), 'build': built, 'fresh_compiles': fresh,
               'contracts': contracts, 'assumptions': audited,
               'new_dependencies': {n: sorted(ds) for n, ds in deps.items()},
               'new_objects_sha256': {'Coq/C/' + n + '.vo': support.sha((coq / 'C' / (n + '.vo')).read_bytes()) for n in MODULES},
               'coverage_added': 2, 'full_acceptance': False}
    write(work / 'PREPARATION.json', receipt)
    write(HERE / 'PREPARATION.json', receipt)
    print('Candidate snapshots prepared; independent review is required before --accept', flush=True)


def seal(work):
    """Pin objects after a preparation launched before object hashes were added.

    This does not reclassify preparation as proof acceptance or change an exit
    status. The original terminal receipt is preserved byte-for-byte.
    """
    path = work / 'PREPARATION.json'
    original = path.read_text()
    receipt = json.loads(original)
    if 'new_objects_sha256' in receipt:
        return
    meta = json.loads((work / 'ASSEMBLY.json').read_text())
    if support.input_map() != meta['main_inputs'] or support.index_hash() != meta['staged_patch_sha256']:
        raise ValueError('main drift before sealing')
    for name in MODULES:
        evidence = receipt['fresh_compiles'][name]
        if (evidence['exit_code'] != 0 or evidence['command'] !=
                ['bash', 'build-jets.sh', '--coqc', '-q', 'C/' + name + '.v'] or
                evidence['log_sha256'] != support.sha((work / ('fresh-' + name + '.log')).read_bytes()) or
                (work / 'Coq/C' / (name + '.v')).read_bytes() != (MAIN / 'C' / (name + '.v')).read_bytes()):
            raise ValueError('fresh compile/source evidence drift before sealing')
    receipt['new_objects_sha256'] = {'Coq/C/' + name + '.vo': support.sha((work / 'Coq/C' / (name + '.vo')).read_bytes()) for name in MODULES}
    support.changed({work / 'PREPARATION-unsealed.json': original})
    write(path, receipt)
    write(HERE / 'PREPARATION.json', receipt)
    print('Fresh object hashes sealed; original preparation receipt retained', flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('action', choices=['assemble', 'prepare', 'seal'])
    parser.add_argument('work', nargs='?')
    args = parser.parse_args()
    if args.action == 'assemble':
        assemble()
    elif args.action == 'prepare':
        prepare(Path(args.work).resolve())
    else:
        seal(Path(args.work).resolve())
