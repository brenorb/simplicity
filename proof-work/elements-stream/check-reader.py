"""Once-only fresh compile/full reports for the environment-generic helper.

This development checkpoint is not a jet endpoint, recursive kernel check,
normal registration or full acceptance. Main/audit inputs are never changed.
"""
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('elements_stream_shared', HERE.parent / 'elements-tap-getters/check.py')
shared = importlib.util.module_from_spec(sp)
sp.loader.exec_module(shared)
s = shared.s
MODULE = 'C.jet_sha_hash_words_reader'
NAME = 'C/jet_sha_hash_words_reader.v'
BASE_RECEIPT = HERE.parent / 'scalar-lambda-admission/ACCEPTANCE.json'


def main(work):
    if (HERE / 'READER-CHECKED.json').exists():
        raise ValueError('reader checkpoint already completed; inspect its evidence')
    base_record = json.loads(BASE_RECEIPT.read_text())
    base = Path(base_record['candidate'])
    if (work == s.REPO or s.REPO in work.parents or work == base or
        (work / 'Coq').is_symlink() or base_record['full_acceptance'] is not True or
        s.inputs.fingerprint(base / 'Coq', base) != base_record['audit_input_sha256']):
        raise ValueError('distinct private tree and completed420 source base required')
    inherited = shared.inventory(base / 'Coq')
    if shared.inventory(work / 'Coq') != inherited | {NAME}:
        raise ValueError('unexpected reader source/metadata inventory')
    for name in inherited:
        if (work / 'Coq' / name).read_bytes() != (base / 'Coq' / name).read_bytes():
            raise ValueError('reader checkpoint changes inherited source: ' + name)
    source = work / 'Coq' / NAME
    if source.read_bytes() != (HERE / 'source' / (source.name + '.source')).read_bytes():
        raise ValueError('archived/private reader helper differs')
    s.safe_source(source.read_text(), NAME)
    before, index = s.input_map(), s.index_hash()
    fingerprint = s.inputs.fingerprint(work / 'Coq', work)
    commands = {MODULE: s.run(work, ['bash', 'build-jets.sh', '--coqc', '-q', NAME], MODULE, 60)}
    results, definitions, deps = shared.reports(work, [(MODULE, source)], 'elements-reader', commands)
    if (len(results), len(definitions)) != (15, 1):
        raise ValueError('wrong complete reader declaration inventory')
    if s.input_map() != before or s.index_hash() != index or s.inputs.fingerprint(work / 'Coq', work) != fingerprint:
        raise ValueError('reader compile/report phase changed main/index/private sources')
    record = dict(candidate=str(work), base_candidate=str(base),
        base_acceptance_sha256=s.sha(BASE_RECEIPT.read_bytes()),
        base_input_sha256=base_record['audit_input_sha256'], candidate_input_sha256=fingerprint,
        staged_patch_sha256=index, main_inputs=before, module=MODULE, new_source=NAME,
        source_sha256=s.sha(source.read_bytes()), object_sha256=s.sha(source.with_suffix('.vo').read_bytes()),
        commands=commands, results=results, definitions=definitions,
        dependencies={n: sorted(ds) for n, ds in deps.items()},
        closed_results=[n for n in results if not deps[n]],
        tools_sha256={'check-reader.py': s.sha(Path(__file__).read_bytes())},
        any_environment_type=True, existing_pure_traversal_reused=True,
        whole_c_endpoints=0, recursive_kernel_check=False, normal_registration=False,
        coverage_added=0, full_acceptance=False)
    s.changed({HERE / 'READER-CHECKED.json': json.dumps(record, indent=2) + '\n',
        **{HERE / (n + '.log'): (work / (n + '.log')).read_text() for n in commands}})
    print('Generic Reader hashLoop/hashWords helper freshly compiled/reported; no C endpoint or kernel claim', flush=True)


if __name__ == '__main__':
    main(Path(sys.argv[1]).resolve())
