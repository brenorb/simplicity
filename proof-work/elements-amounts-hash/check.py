"""Fresh complete reports for both original Elements amounts-hash C jets."""
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('amounts_hash_checked_base', HERE.parent / 'elements-nonces/check.py')
base = importlib.util.module_from_spec(sp)
sp.loader.exec_module(base)
shared, s = base.shared, base.s
RECEIPT = HERE.parent / 'elements-nonces/CHECKED.json'
BASE_RECORD = json.loads(RECEIPT.read_text())
BASE = Path(BASE_RECORD['candidate'])
MODULES = ['C.jet_elements_asset_amount_hash_spec', 'C.jet_elements_amounts_hash_program']
NAMES = [m.replace('.', '/') + '.v' for m in MODULES]
MODULE = MODULES[-1]
ENDPOINTS = [MODULE + '.elements_' + name + '_amounts_hash_program_local_spec' for name in ['output', 'input']]
FUNEXT = [MODULE + '.' + n for n in ['elements_amounts_hash_spec_sem',
    'elements_output_amounts_of_sem', 'elements_input_amounts_of_sem']]
EXECUTION = [MODULE + '.elements_tx_amounts_hash_jet', *ENDPOINTS]


def tree(work):
    if (work == s.REPO or s.REPO in work.parents or work == BASE or
        (work / 'Coq').is_symlink() or BASE_RECORD['recursive_kernel_check'] is not True or
        s.inputs.fingerprint(BASE / 'Coq', BASE) != BASE_RECORD['candidate_input_sha256']):
        raise ValueError('distinct private amounts tree and completed nonce base required')
    base.tree(BASE)
    old = shared.inventory(BASE / 'Coq')
    if shared.inventory(work / 'Coq') != old | set(NAMES):
        raise ValueError('unexpected amounts source/metadata inventory')
    for name in old:
        if (work / 'Coq' / name).read_bytes() != (BASE / 'Coq' / name).read_bytes():
            raise ValueError('amounts proof changes inherited source: ' + name)
    for name in NAMES:
        source = work / 'Coq' / name
        if source.is_symlink() or source.read_bytes() != (HERE / 'source' / (source.name + '.source')).read_bytes():
            raise ValueError('private/archive amounts proof differs: ' + name)
        s.safe_source(source.read_text(), name)


def main(work):
    if (HERE / 'RUN.json').exists():
        raise ValueError('amounts compilation already recorded; inspect existing evidence')
    tree(work)
    before, index = s.input_map(), s.index_hash()
    fingerprint = s.inputs.fingerprint(work / 'Coq', work)
    commands = {}
    for module, name in zip(MODULES, NAMES):
        commands[module] = s.run(work, ['bash', 'build-jets.sh', '--coqc', '-q', name], module, 60)
    results, definitions, deps = shared.reports(work,
        [(m, work / 'Coq' / n) for m, n in zip(MODULES, NAMES)], 'elements-amounts-hash', commands)
    expected = {n: set() for n in results}
    expected.update({n: {'FunctionalExtensionality.functional_extensionality_dep'} for n in FUNEXT})
    expected.update({n: s.SIX for n in EXECUTION})
    if ((len(results), len(definitions)) != (22, 23) or not set(ENDPOINTS) <= set(results) or deps != expected):
        raise ValueError('wrong complete amounts declaration/assumption inventory')
    tree(work)
    if (s.input_map() != before or s.index_hash() != index or
        s.inputs.fingerprint(work / 'Coq', work) != fingerprint):
        raise ValueError('amounts compilation changed main/index/private input')
    record = dict(candidate=str(work), base_candidate=str(BASE),
        base_checked_sha256=s.sha(RECEIPT.read_bytes()),
        base_review_sha256=s.sha((HERE.parent / 'elements-nonces/EVIDENCE-REVIEW.json').read_bytes()),
        candidate_input_sha256=fingerprint, main_inputs=before, staged_patch_sha256=index,
        modules=MODULES, new_sources=NAMES, results=results, definitions=definitions, endpoints=ENDPOINTS,
        closed_results=[n for n in results if not deps[n]],
        dependencies={n: sorted(ds) for n, ds in deps.items()}, commands=commands,
        source_sha256={m: s.sha((work / 'Coq' / n).read_bytes()) for m, n in zip(MODULES, NAMES)},
        object_sha256={m: s.sha((work / 'Coq' / n).with_suffix('.vo').read_bytes()) for m, n in zip(MODULES, NAMES)},
        tools_sha256={'check.py': s.sha(Path(__file__).read_bytes())},
        shared_tagged_absorber=True, canonical_amount_pair_program_reused=True,
        explicit_amount_bytes=8, confidential_amount_bytes=32, whole_c_endpoints=2,
        caller_cached_hashes_established=False, canonical_source_review_complete=False,
        recursive_kernel_check=False, normal_registration=False, coverage_added=0, full_acceptance=False)
    s.changed({HERE / 'RUN.json': json.dumps(record, indent=2) + '\n',
        **{HERE / (n + '.log'): (work / (n + '.log')).read_text() for n in commands}})
    print('Both amounts-hash C endpoints freshly compiled/reported; kernel/source/admission remain', flush=True)


if __name__ == '__main__':
    if len(sys.argv) != 2:
        raise ValueError('usage: check.py PRIVATE_TREE')
    main(Path(sys.argv[1]).resolve())
