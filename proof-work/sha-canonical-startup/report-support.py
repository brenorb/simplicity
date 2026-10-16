"""Inventory the actual startup dependency closure for eventual normal admission.

The nine support modules were freshly compiled and recursively kernel-checked
already. Print their complete public types, definitions and assumption sets;
do not mistake source-file presence or adapters alone for build registration.
"""
import importlib.util
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('sha_startup_dependency_inventory', HERE / 'check.py')
g = importlib.util.module_from_spec(sp)
sp.loader.exec_module(g)
s = g.s


def main(work):
    if (HERE / 'SUPPORT-REPORT.json').exists():
        raise ValueError('startup support reports already recorded; inspect their existing evidence')
    checked = json.loads((HERE / 'CHECKED.json').read_text())
    if (checked['candidate'] != str(work) or checked['recursive_kernel_check'] is not True or
        checked['freshly_compiled_support'] != g.SUPPORT or checked['coverage_added'] != 0):
        raise ValueError('actual completed startup kernel evidence required')
    g.tree(work)
    before, index = s.input_map(), s.index_hash()
    fingerprint = s.inputs.fingerprint(work / 'Coq', work)
    if before != checked['main_inputs'] or index != checked['staged_patch_sha256'] or fingerprint != checked['candidate_input_sha256']:
        raise ValueError('startup dependency report source/main/index differs')
    for field, suffix in [('source_sha256', '.v'), ('object_sha256', '.vo')]:
        for m in g.SUPPORT + [g.MODULE]:
            path = work / 'Coq' / (m.replace('.', '/') + suffix)
            if path.is_symlink() or s.sha(path.read_bytes()) != checked[field][m]:
                raise ValueError('completed startup source/object differs')
    results, definitions = [], []
    for module in g.SUPPORT:
        a, b = g.shared.declarations((work / 'Coq' / (module.replace('.', '/') + '.v')).read_text(), module)
        results += a
        definitions += b
    if len(results) != len(set(results)) or len(definitions) != len(set(definitions)):
        raise ValueError('duplicate startup public declarations')
    header = ['Require ' + m + '.' for m in g.SUPPORT]
    assumptions = header[:]
    contracts = header + ['Set Printing All.', 'Set Printing Width 120.', 'Set Printing Depth 1000000.']
    for n in results:
        assumptions += ['Goal True. idtac "JET_ASSUMPTIONS ' + n + '". exact I. Qed.', 'Print Assumptions ' + n + '.']
        contracts += ['Goal True. idtac "TAP_TYPE ' + n + '". exact I. Qed.', 'Check @' + n + '.']
    for n in definitions:
        contracts += ['Goal True. idtac "TAP_DEF ' + n + '". exact I. Qed.', 'Print ' + n + '.']
    commands = {}
    for stem, lines in [('sha-startup-support-assumptions', assumptions), ('sha-startup-support-contracts', contracts)]:
        path = work / (stem.replace('-', '_') + '.v')
        s.changed({path: '\n'.join(lines) + '\n'})
        commands[stem] = s.run(work, ['bash', 'build-jets.sh', '--coqc', '-q', str(path)], stem, 900)
        print('Passed ' + stem, flush=True)
    deps = s.reports.assumptions((work / 'sha-startup-support-assumptions.log').read_text())
    text = (work / 'sha-startup-support-contracts.log').read_text()
    wanted = [('TYPE', n) for n in results] + [('DEF', n) for n in definitions]
    if (set(deps) != set(results) or any(not ds <= g.EIGHT for ds in deps.values()) or
        re.findall(r'(?m)^TAP_(TYPE|DEF) (\S+)$', text) != wanted or
        '...' in text or re.search(r'\?[A-Za-z]', text)):
        raise ValueError('incomplete startup support report or unreviewed inherited assumption')
    g.tree(work)
    if s.input_map() != before or s.index_hash() != index or s.inputs.fingerprint(work / 'Coq', work) != fingerprint:
        raise ValueError('startup support reporting changed private/main/index inputs')
    record = dict(candidate=str(work), candidate_input_sha256=fingerprint,
        checked_sha256=s.sha((HERE / 'CHECKED.json').read_bytes()), staged_patch_sha256=index,
        modules=g.SUPPORT, results=results, definitions=definitions,
        closed_results=[n for n in results if not deps[n]],
        dependencies={n: sorted(ds) for n, ds in deps.items()}, commands=commands,
        source_sha256={m: checked['source_sha256'][m] for m in g.SUPPORT},
        object_sha256={m: checked['object_sha256'][m] for m in g.SUPPORT},
        tool_sha256=s.sha(Path(__file__).read_bytes()), new_axioms=0,
        full_types_and_definitions=True, normal_registration=False, coverage_added=0, full_acceptance=False)
    s.changed({HERE / 'SUPPORT-REPORT.json': json.dumps(record, indent=2) + '\n',
        **{HERE / (n + '.log'): (work / (n + '.log')).read_text() for n in commands}})
    print('Startup support closure fully reported; normal admission still required', flush=True)


if __name__ == '__main__':
    if len(sys.argv) != 2:
        raise ValueError('usage: report-support.py COMPLETED_SHA_TREE')
    main(Path(sys.argv[1]).resolve())
