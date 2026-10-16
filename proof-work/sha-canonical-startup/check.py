"""Fresh explicit SHA startup targets; no new coverage or acceptance claim.

Reuse completed execution/startup proofs. Preserve the seventeen libc premises
and the two inherited CompCert semantic-properties assumptions used to keep
the startup invariant. Do not relabel these results as six-assumption proofs.
"""
import importlib.util
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('sha_canonical_completed_source', HERE.parent / 'elements-inputs/check.py')
base = importlib.util.module_from_spec(sp)
sp.loader.exec_module(base)
shared, s = base.shared, base.s
RECEIPT = HERE.parent / 'elements-inputs/CHECKED.json'
BASE_RECORD = json.loads(RECEIPT.read_text())
BASE = Path(BASE_RECORD['candidate'])
MODULE = 'C.jet_sha_canonical_startup'
NAME = MODULE.replace('.', '/') + '.v'
SUPPORT = ['C.jet_sha_initial_globals', 'C.jet_sha_startup_globals', 'C.jet_sha_startup_state',
           'C.jet_sha_startup_jets', 'C.jet_sha_startup_setup', 'C.jet_sha_startup_lifecycle',
           'C.jet_sha_startup_init', 'C.jet_sha_startup_executable', 'C.jet_sha_startup_runs']
EIGHT = s.SIX | {'Events.external_functions_properties', 'Events.inline_assembly_properties'}
FOUR = s.SIX - {'Events.external_functions_sem', 'Events.inline_assembly_sem'}


def tree(work):
    if (work == s.REPO or s.REPO in work.parents or work == BASE or
        (work / 'Coq').is_symlink() or BASE_RECORD['recursive_kernel_check'] is not True or
        s.inputs.fingerprint(BASE / 'Coq', BASE) != BASE_RECORD['candidate_input_sha256']):
        raise ValueError('distinct private SHA tree and completed source base required')
    base.tree(BASE)
    old = shared.inventory(BASE / 'Coq')
    if shared.inventory(work / 'Coq') != old | {NAME}:
        raise ValueError('unexpected SHA source/metadata inventory')
    for name in old:
        if (work / 'Coq' / name).read_bytes() != (BASE / 'Coq' / name).read_bytes():
            raise ValueError('SHA adapter changes inherited source: ' + name)
    source = work / 'Coq' / NAME
    if source.is_symlink() or source.read_bytes() != (HERE / 'source' / (source.name + '.source')).read_bytes():
        raise ValueError('private/archive SHA adapter source differs')
    s.safe_source(source.read_text(), NAME)


def reports(work, commands):
    results, definitions = shared.declarations((work / 'Coq' / NAME).read_text(), MODULE)
    if len(results) != 19 or definitions:
        raise ValueError('expected nineteen complete explicit results, no new program definitions')
    axioms = ['Require ' + MODULE + '.']
    types = axioms + ['Set Printing All.', 'Set Printing Width 120.', 'Set Printing Depth 1000000.']
    for n in results:
        axioms += ['Goal True. idtac "JET_ASSUMPTIONS ' + n + '". exact I. Qed.', 'Print Assumptions ' + n + '.']
        types += ['Goal True. idtac "TAP_TYPE ' + n + '". exact I. Qed.', 'Check @' + n + '.']
    for stem, source in [('sha-canonical-assumptions', axioms), ('sha-canonical-contracts', types)]:
        path = work / (stem.replace('-', '_') + '.v')
        s.changed({path: '\n'.join(source) + '\n'})
        commands[stem] = s.run(work, ['bash', 'build-jets.sh', '--coqc', '-q', str(path)], stem, 180)
    deps = s.reports.assumptions((work / 'sha-canonical-assumptions.log').read_text())
    expected = {n: FOUR if n.endswith('.sha_canonical_startup_nonvacuous') else EIGHT for n in results}
    text = (work / 'sha-canonical-contracts.log').read_text()
    if (deps != expected or '...' in text or re.search(r'\?[A-Za-z]', text) or
        re.findall(r'(?m)^TAP_(TYPE|DEF) (\S+)$', text) != [('TYPE', n) for n in results]):
        raise ValueError('incomplete explicit SHA target or changed inherited assumption set')
    return results, definitions, deps


def main(work):
    if (HERE / 'RUN.json').exists():
        raise ValueError('SHA compilation already recorded; inspect existing evidence')
    tree(work)
    before, index = s.input_map(), s.index_hash()
    fingerprint = s.inputs.fingerprint(work / 'Coq', work)
    commands = {}
    for module in SUPPORT + [MODULE]:
        commands[module] = s.run(work, ['bash', 'build-jets.sh', '--coqc', '-q', module.replace('.', '/') + '.v'], module, 900)
        print('Freshly compiled ' + module, flush=True)
    results, definitions, deps = reports(work, commands)
    endpoints = results[1:]
    if (not results[0].endswith('.sha_canonical_startup_nonvacuous') or
        sum('memcpy_model ->' in x for x in re.findall(r'\bTheorem\s+\w+\s*:(.*?)\bProof\.',
            (work / 'Coq' / NAME).read_text(), re.S)) != 17):
        raise ValueError('wrong nonvacuity/libc boundary')
    tree(work)
    if (s.input_map() != before or s.index_hash() != index or
        s.inputs.fingerprint(work / 'Coq', work) != fingerprint):
        raise ValueError('SHA compilation changed main/index/private input')
    record = dict(candidate=str(work), base_candidate=str(BASE),
        base_checked_sha256=s.sha(RECEIPT.read_bytes()),
        base_review_sha256=s.sha((HERE.parent / 'elements-inputs/EVIDENCE-REVIEW.json').read_bytes()),
        candidate_input_sha256=fingerprint, main_inputs=before, staged_patch_sha256=index,
        modules=[MODULE], new_sources=[NAME], freshly_compiled_support=SUPPORT,
        results=results, definitions=definitions, endpoints=endpoints,
        closed_results=[], dependencies={n: sorted(ds) for n, ds in deps.items()}, commands=commands,
        source_sha256={m: s.sha((work / 'Coq' / (m.replace('.', '/') + '.v')).read_bytes()) for m in SUPPORT + [MODULE]},
        object_sha256={m: s.sha((work / 'Coq' / (m.replace('.', '/') + '.vo')).read_bytes()) for m in SUPPORT + [MODULE]},
        tools_sha256={'check.py': s.sha(Path(__file__).read_bytes())},
        existing_execution_and_startup_proofs_reused=True, named_original_startup_state=True,
        actual_initial_memory_exists=True, whole_c_endpoints=18, conditional_memcpy_endpoints=17,
        inherited_endpoint_assumptions=8, new_axioms=0,
        canonical_source_review_complete=False, recursive_kernel_check=False,
        normal_registration=False, coverage_added=0, full_acceptance=False)
    s.changed({HERE / 'RUN.json': json.dumps(record, indent=2) + '\n',
        **{HERE / (n + '.log'): (work / (n + '.log')).read_text() for n in commands}})
    print('Eighteen explicit SHA startup targets freshly compiled/reported; source/kernel/admission remain', flush=True)


if __name__ == '__main__':
    if len(sys.argv) != 2:
        raise ValueError('usage: check.py PRIVATE_TREE')
    main(Path(sys.argv[1]).resolve())
