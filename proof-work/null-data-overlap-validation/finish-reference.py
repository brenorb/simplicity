"""Finish the pure reference check with its actual smaller library profile.

The first coqchk exited zero but its parent then required the full Clight
profile. Preserve that failed parent/receipt and rerun only the bounded kernel
phase against the exact pure-root profile, a strict subset of the normal one.
No normal audit or theorem assumption allowance is changed.
"""
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('overlap_reference_finish_base', HERE / 'check-reference.py')
g = importlib.util.module_from_spec(sp)
sp.loader.exec_module(g)
s = g.s


def main(work):
    if (HERE / 'REFERENCE-CHECKED.json').exists():
        raise ValueError('pure reference kernel completion already recorded')
    r = json.loads((HERE / 'REFERENCE-RUN.json').read_text())
    g.tree(work)
    before, index = s.input_map(), s.index_hash()
    if (r['candidate'] != str(work) or r['command'] != g.KERNEL or
        r['driver_sha256'] != s.sha((HERE / 'check-reference.py').read_bytes()) or
        r['main_inputs'] != before or r['staged_patch_sha256'] != index or
        r['candidate_input_sha256'] != s.inputs.fingerprint(work / 'Coq', work) or
        r['source_sha256'] != s.sha((work / 'Coq' / g.NAME).read_bytes()) or
        r['object_sha256'] != s.sha((work / 'Coq' / g.NAME).with_suffix('.vo').read_bytes()) or
        r['recursive_kernel_check'] is not False or r['compcert_execution_counterexample_proved'] is not False):
        raise ValueError('original reference compile/launch identity differs')
    if len(r['results']) != 5 or len(r['definitions']) != 2 or any(r['dependencies'].values()):
        raise ValueError('expected exactly five closed reference results')
    for n, row in r['commands'].items():
        log = work / (n + '.log')
        if row['exit_code'] != 0 or row['log_sha256'] != s.sha(log.read_bytes()) or (HERE / log.name).read_bytes() != log.read_bytes():
            raise ValueError('original compile/report command log differs')
    allowed = sorted((work / 'Coq/C/jet_coqchk_axioms.expected').read_text().split())
    profile = sorted((HERE / 'reference-kernel-axioms.expected').read_text().split())
    if len(profile) != 10 or not set(profile) < set(allowed):
        raise ValueError('pure kernel profile must be the exact strict subset of the unchanged normal profile')
    # This establishes why the prior full-C-profile comparison failed, without
    # rewriting it into a successful parent exit or changing its bound tool.
    s.kernel.kernel((work / 'reference-kernel.log').read_text(), profile)
    kernel = s.run(work, g.KERNEL, 'reference-kernel-checked', 1800)
    s.kernel.kernel((work / 'reference-kernel-checked.log').read_text(), profile)
    g.tree(work)
    if (s.input_map() != before or s.index_hash() != index or
        s.inputs.fingerprint(work / 'Coq', work) != r['candidate_input_sha256']):
        raise ValueError('pure reference finish changed main/index/private source')
    record = dict(candidate=str(work), original_launch_sha256=s.sha((HERE / 'REFERENCE-RUN.json').read_bytes()),
        original_parent_phase='failed full-Clight-profile comparison after successful coqchk',
        kernel_check=kernel, kernel_axioms=profile,
        tools_sha256={n: s.sha((HERE / n).read_bytes()) for n in
            ['check-reference.py', 'finish-reference.py', 'reference-kernel-axioms.expected']},
        source_sha256=r['source_sha256'], object_sha256=r['object_sha256'],
        candidate_input_sha256=r['candidate_input_sha256'], staged_patch_sha256=index,
        results=r['results'], definitions=r['definitions'], dependencies=r['dependencies'],
        closed_results=5, recursive_kernel_check=True,
        compcert_execution_counterexample_proved=False, whole_jet_equivalence_proved=False, coverage_added=0)
    s.changed({HERE / 'REFERENCE-CHECKED.json': json.dumps(record, indent=2) + '\n',
        **{HERE / n: (work / n).read_text() for n in ['reference-kernel.log', 'reference-kernel-checked.log']}})
    print('Five closed reference facts freshly kernel-checked with unchanged normal audit profile; no Clight counterexample claimed', flush=True)


if __name__ == '__main__':
    if len(sys.argv) != 2:
        raise ValueError('usage: finish-reference.py PRIVATE_TREE')
    main(Path(sys.argv[1]).resolve())
