"""Fresh compile/full contracts for the Elements output-nonces C endpoint.

Separate from source-fidelity review, recursive kernel check and admission.
"""
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('nonces_checked_base', HERE.parent / 'elements-outpoints/check.py')
base = importlib.util.module_from_spec(sp)
sp.loader.exec_module(base)
shared, s = base.shared, base.s
RECEIPT = HERE.parent / 'elements-outpoints/CHECKED.json'
BASE_RECORD = json.loads(RECEIPT.read_text())
BASE = Path(BASE_RECORD['candidate'])
MODULES = ['C.jet_sha_tagged_word_spec', 'C.jet_elements_nonce_hash_spec',
           'C.jet_elements_nonces_hash_program']
NAMES = [m.replace('.', '/') + '.v' for m in MODULES]
MODULE = MODULES[-1]
ENDPOINT = MODULE + '.elements_output_nonces_hash_program_local_spec'
FUNEXT = [MODULE + '.elements_output_nonces_hash_spec_sem']


def tree(work):
    if (work == s.REPO or s.REPO in work.parents or work == BASE or
        (work / 'Coq').is_symlink() or BASE_RECORD['recursive_kernel_check'] is not True or
        s.inputs.fingerprint(BASE / 'Coq', BASE) != BASE_RECORD['candidate_input_sha256']):
        raise ValueError('distinct private nonces tree and completed outpoints base required')
    base.tree(BASE)
    old = shared.inventory(BASE / 'Coq')
    if shared.inventory(work / 'Coq') != old | set(NAMES):
        raise ValueError('unexpected nonces source/metadata inventory')
    for name in old:
        if (work / 'Coq' / name).read_bytes() != (BASE / 'Coq' / name).read_bytes():
            raise ValueError('nonces proof changes inherited source: ' + name)
    for name in NAMES:
        source = work / 'Coq' / name
        if source.is_symlink() or source.read_bytes() != (HERE / 'source' / (source.name + '.source')).read_bytes():
            raise ValueError('private/archive nonce proof differs: ' + name)
        s.safe_source(source.read_text(), name)


def main(work):
    if (HERE / 'RUN.json').exists():
        raise ValueError('nonce compilation already recorded; inspect existing evidence')
    tree(work)
    before, index = s.input_map(), s.index_hash()
    fingerprint = s.inputs.fingerprint(work / 'Coq', work)
    commands = {}
    for module, name in zip(MODULES, NAMES):
        commands[module] = s.run(work, ['bash', 'build-jets.sh', '--coqc', '-q', name], module, 60)
    results, definitions, deps = shared.reports(work,
        [(m, work / 'Coq' / n) for m, n in zip(MODULES, NAMES)], 'elements-nonces', commands)
    expected = {n: set() for n in results}
    expected.update({n: {'FunctionalExtensionality.functional_extensionality_dep'} for n in FUNEXT})
    expected[ENDPOINT] = s.SIX
    if ((len(results), len(definitions)) != (11, 12) or ENDPOINT not in results or deps != expected):
        raise ValueError('wrong complete nonces declaration/assumption inventory')
    tree(work)
    if (s.input_map() != before or s.index_hash() != index or
        s.inputs.fingerprint(work / 'Coq', work) != fingerprint):
        raise ValueError('nonces compilation changed main/index/private input')
    record = dict(candidate=str(work), base_candidate=str(BASE),
        base_checked_sha256=s.sha(RECEIPT.read_bytes()),
        base_review_sha256=s.sha((HERE.parent / 'elements-outpoints/EVIDENCE-REVIEW.json').read_bytes()),
        candidate_input_sha256=fingerprint, main_inputs=before, staged_patch_sha256=index,
        modules=MODULES, new_sources=NAMES, results=results, definitions=definitions, endpoints=[ENDPOINT],
        closed_results=[n for n in results if not deps[n]],
        dependencies={n: sorted(ds) for n, ds in deps.items()}, commands=commands,
        source_sha256={m: s.sha((work / 'Coq' / n).read_bytes()) for m, n in zip(MODULES, NAMES)},
        object_sha256={m: s.sha((work / 'Coq' / n).with_suffix('.vo').read_bytes()) for m, n in zip(MODULES, NAMES)},
        tools_sha256={'check.py': s.sha(Path(__file__).read_bytes())},
        shared_tagged_absorber=True, native_word256_payload=True, outer_and_inner_absence_distinct=True,
        whole_c_endpoints=1, caller_cached_hashes_established=False, canonical_source_review_complete=False,
        recursive_kernel_check=False, normal_registration=False, coverage_added=0, full_acceptance=False)
    s.changed({HERE / 'RUN.json': json.dumps(record, indent=2) + '\n',
        **{HERE / (n + '.log'): (work / (n + '.log')).read_text() for n in commands}})
    print('Output-nonces C endpoint freshly compiled/reported; kernel/source/admission remain', flush=True)


if __name__ == '__main__':
    if len(sys.argv) != 2:
        raise ValueError('usage: check.py PRIVATE_TREE')
    main(Path(sys.argv[1]).resolve())
