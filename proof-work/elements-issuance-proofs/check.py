"""Fresh full reports for the Elements composite issuance-proofs-hash C endpoint.

This development checkpoint does not claim kernel/source review or admission.
"""
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('elements_issuance_proofs_source_base', HERE.parent / 'elements-outpoints/check.py')
base = importlib.util.module_from_spec(sp)
sp.loader.exec_module(base)
shared, s = base.shared, base.s
RECEIPT = HERE.parent / 'elements-outpoints/CHECKED.json'
BASE_RECORD = json.loads(RECEIPT.read_text())
BASE = Path(BASE_RECORD['candidate'])
MODULE = 'C.jet_elements_issuance_proofs_hash_program'
NAME = MODULE.replace('.', '/') + '.v'
ENDPOINT = MODULE + '.elements_issuance_range_proofs_hash_program_local_spec'


def tree(work):
    if (work == s.REPO or s.REPO in work.parents or work == BASE or
        (work / 'Coq').is_symlink() or BASE_RECORD['recursive_kernel_check'] is not True or
        s.inputs.fingerprint(BASE / 'Coq', BASE) != BASE_RECORD['candidate_input_sha256']):
        raise ValueError('distinct private issuance-proofs tree and completed Elements source base required')
    base.tree(BASE)
    old = shared.inventory(BASE / 'Coq')
    if shared.inventory(work / 'Coq') != old | {NAME}:
        raise ValueError('unexpected issuance-proofs source/metadata inventory')
    for name in old:
        if (work / 'Coq' / name).read_bytes() != (BASE / 'Coq' / name).read_bytes():
            raise ValueError('issuance-proofs proof changes inherited source: ' + name)
    source = work / 'Coq' / NAME
    if source.is_symlink() or source.read_bytes() != (HERE / 'source' / (source.name + '.source')).read_bytes():
        raise ValueError('private/archive issuance-proofs proof differs')
    s.safe_source(source.read_text(), NAME)


def main(work):
    if (HERE / 'RUN.json').exists():
        raise ValueError('issuance-proofs compilation already recorded; inspect existing evidence')
    tree(work)
    before, index = s.input_map(), s.index_hash()
    fingerprint = s.inputs.fingerprint(work / 'Coq', work)
    commands = {MODULE: s.run(work, ['bash', 'build-jets.sh', '--coqc', '-q', NAME], MODULE, 60)}
    results, definitions, deps = shared.reports(work,
        [(MODULE, work / 'Coq' / NAME)], 'elements-issuance-proofs', commands)
    if ((len(results), len(definitions)) != (11, 7) or ENDPOINT not in results or
        deps[ENDPOINT] != s.SIX or any(not ds <= s.SIX for ds in deps.values())):
        raise ValueError('wrong complete issuance-proofs declaration/assumption inventory')
    tree(work)
    if (s.input_map() != before or s.index_hash() != index or
        s.inputs.fingerprint(work / 'Coq', work) != fingerprint):
        raise ValueError('issuance-proofs compilation changed main/index/private input')
    record = dict(candidate=str(work), base_candidate=str(BASE),
        base_checked_sha256=s.sha(RECEIPT.read_bytes()),
        base_review_sha256=s.sha((HERE.parent / 'elements-outpoints/EVIDENCE-REVIEW.json').read_bytes()),
        candidate_input_sha256=fingerprint, main_inputs=before, staged_patch_sha256=index,
        modules=[MODULE], new_sources=[NAME], results=results, definitions=definitions, endpoints=[ENDPOINT],
        closed_results=[n for n in results if not deps[n]],
        dependencies={n: sorted(ds) for n, ds in deps.items()}, commands=commands,
        source_sha256={MODULE: s.sha((work / 'Coq' / NAME).read_bytes())},
        object_sha256={MODULE: s.sha((work / 'Coq' / NAME).with_suffix('.vo').read_bytes())},
        tools_sha256={'check.py': s.sha(Path(__file__).read_bytes())},
        literal_two_primitive_loop=True, generic_loop_body_equivalence_proved=True, whole_c_endpoints=1,
        caller_cached_hashes_established=False, canonical_source_review_complete=False,
        recursive_kernel_check=False, normal_registration=False, coverage_added=0, full_acceptance=False)
    s.changed({HERE / 'RUN.json': json.dumps(record, indent=2) + '\n',
        **{HERE / (n + '.log'): (work / (n + '.log')).read_text() for n in commands}})
    print('Elements composite issuance-proofs-hash C endpoint freshly compiled/reported; kernel/source/admission remain', flush=True)


if __name__ == '__main__':
    if len(sys.argv) != 2:
        raise ValueError('usage: check.py PRIVATE_TREE')
    main(Path(sys.argv[1]).resolve())
