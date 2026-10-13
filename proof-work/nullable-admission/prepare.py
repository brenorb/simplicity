"""Prepare only the nine new snapshots; full acceptance still checks all results."""
import argparse
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
REPO = HERE.parent.parent


def load(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec); spec.loader.exec_module(mod)
    return mod


def prepare(candidate):
    assembly = load(HERE / 'assemble.py', 'nullable_prep_assembly')
    normal = load(HERE.parent / 'scalar-multiply-integration/review-normal.py', 'nullable_prep_records')
    meta = json.loads((candidate / 'ASSEMBLY.json').read_text())
    coq = candidate / 'Coq'
    results = [tuple(row.split()) for row in meta['extensions']['C/jet_public_theorems.txt']]
    definitions = [tuple(row.split()) for row in meta['extensions']['C/jet_contract_definitions.txt']]
    all_results = normal.rows(coq / 'C/jet_public_theorems.txt')
    all_defs = normal.rows(coq / 'C/jet_contract_definitions.txt')
    driver = ['Set Warnings "-notation-overridden".']
    for module in sorted({module for module, _ in all_results + all_defs}):
        # Match the actual contract gate's import context, without reprinting
        # the unchanged results. Final --accept will compare all of them.
        keyword = 'Require' if module.startswith('Simplicity.') or module == 'C.jet_secp_umul128_exec' else 'Require Import'
        driver.append(keyword + ' ' + module + '.')
    driver += ['Import Simplicity.BitMachine Simplicity.Translate.', 'Set Printing All.', 'Set Printing Width 120.']
    for kind, rows in [('TYPE', results), ('DEF', definitions)]:
        for module, name in rows:
            full = module + '.' + name
            driver += ['Goal True. idtac "NULLABLE_ADMISSION_' + kind + ' ' + full + '". exact I. Qed.',
                       ('Check ' if kind == 'TYPE' else 'Print ') + full + '.']
    driver.append('Set Printing Depth 1000000.')
    for kind, rows in [('TYPE', results), ('DEF', definitions)]:
        for module, name in rows:
            full = module + '.' + name
            driver += ['Goal True. idtac "NULLABLE_DEEP_' + kind + ' ' + full + '". exact I. Qed.',
                       ('Check ' if kind == 'TYPE' else 'Print ') + full + '.']
    assembly.patch_files({candidate / 'new_contracts.v': '\n'.join(driver) + '\n'})
    env = dict(os.environ, PATH='/nix/store/57myhb98wx8k9dr21cf51bsmvxjs67h6-coq-8.17.1/bin:' + os.environ['PATH'],
               PYTHONDONTWRITEBYTECODE='1')
    with (candidate / 'new_contracts.out').open('wb') as output, (candidate / 'new_contracts.err').open('wb') as error:
        command = ['bash', 'build-jets.sh', '--coqc', '-q', str(candidate / 'new_contracts.v')]
        done = subprocess.run(command, cwd=coq, env=env, stdout=output, stderr=error, timeout=600)
    if done.returncode or (candidate / 'new_contracts.err').read_bytes():
        raise ValueError('new contract driver failed; inspect retained diagnostics')
    text = (candidate / 'new_contracts.out').read_text().split('NULLABLE_DEEP_', 1)[0]
    markers = list(re.finditer(r'(?m)^NULLABLE_ADMISSION_(TYPE|DEF) (\S+)\n', text))
    wanted = [('TYPE', module + '.' + name) for module, name in results]
    wanted += [('DEF', module + '.' + name) for module, name in definitions]
    if [(m[1], m[2]) for m in markers] != wanted or text[:markers[0].start()]:
        raise ValueError('new records missing or reordered')
    chunks = {}
    for i, marker in enumerate(markers):
        full = marker[2]; module, name = full.rsplit('.', 1)
        chunk = text[marker.end():markers[i+1].start() if i+1 < len(markers) else len(text)]
        chunks[(marker[1], module, name, 1)] = ''.join(line.rstrip() + '\n' for line in chunk.splitlines())
    old_results = normal.rows(REPO / 'Coq/C/jet_public_theorems.txt')
    old_defs = normal.rows(REPO / 'Coq/C/jet_contract_definitions.txt')
    old_records = normal.contract_records((REPO / 'Coq/C/jet_contracts.expected').read_text(), old_results, old_defs)
    old_types = ''.join(body for (kind, _, _, _), body in old_records if kind == 'TYPE')
    old_definitions = ''.join(body for (kind, _, _, _), body in old_records if kind == 'DEF')
    contracts = old_types + ''.join(chunks[('TYPE', m, n, 1)] for m, n in results)
    contracts += old_definitions + ''.join(chunks[('DEF', m, n, 1)] for m, n in definitions)
    # Independently kernel-checked assumption sets for these exact normal-C
    # sources, not newly inferred premises or a broad regenerated allowlist.
    checked = json.loads((HERE.parent / 'shared-foundations-integration/REVIEW.json').read_text())['assumptions']
    old = {}
    for line in (REPO / 'Coq/C/jet_assumptions.expected').read_text().splitlines():
        name, deps = line.split(' : ', 1); old[name] = deps
    for module, name in results:
        full = module + '.' + name
        if full in old:
            raise ValueError('result already registered')
        old[full] = ', '.join(checked[full]) or 'closed'
    assumptions = ''.join(name + ' : ' + deps + '\n' for name, deps in sorted(old.items()))
    assembly.patch_files({coq / 'C/jet_contracts.expected': contracts,
                          coq / 'C/jet_assumptions.expected': assumptions})
    print(json.dumps({'candidate': str(candidate), 'driver_exit_code': 0,
                      'new_types': len(results), 'new_definitions': len(definitions),
                      'full_acceptance': False, 'coverage_added': 0}, indent=2))


if __name__ == '__main__':
    cli = argparse.ArgumentParser(); cli.add_argument('--candidate', type=Path, required=True)
    prepare(cli.parse_args().candidate.resolve())
