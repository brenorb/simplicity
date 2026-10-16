"""Check formal expected values, not execution of the overlapping C call."""
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('overlap_reference_base', HERE.parent / 'elements-inputs/check.py')
base = importlib.util.module_from_spec(sp)
sp.loader.exec_module(base)
s, shared = base.s, base.shared
MODULE = 'C.jet_null_data_overlap_reference'
NAME = MODULE.replace('.', '/') + '.v'
BASE = Path(json.loads((HERE.parent / 'elements-inputs/CHECKED.json').read_text())['candidate'])
KERNEL = ['bash', '-c', 'ulimit -s 65520; exec bash build-jets.sh --coqchk -silent -o ' + MODULE]


def tree(work):
    base.tree(BASE)
    old = shared.inventory(BASE / 'Coq')
    if work == BASE or work == s.REPO or s.REPO in work.parents or shared.inventory(work / 'Coq') != old | {NAME}:
        raise ValueError('distinct private source-only reference tree required')
    for name in old:
        if (work / 'Coq' / name).read_bytes() != (BASE / 'Coq' / name).read_bytes():
            raise ValueError('reference changes inherited source: ' + name)
    path = work / 'Coq' / NAME
    if path.is_symlink() or path.read_bytes() != (HERE / 'jet_null_data_overlap_reference.v.source').read_bytes():
        raise ValueError('reference archive/private source differs')
    s.safe_source(path.read_text(), NAME)


def main(work):
    if (HERE / 'REFERENCE-RUN.json').exists():
        raise ValueError('reference verification already launched; inspect its existing handle')
    tree(work)
    before, index = s.input_map(), s.index_hash()
    fp = s.inputs.fingerprint(work / 'Coq', work)
    commands = {MODULE: s.run(work, ['bash', 'build-jets.sh', '--coqc', '-q', NAME], MODULE, 60)}
    results, definitions, deps = shared.reports(work, [(MODULE, work / 'Coq' / NAME)], 'overlap-reference', commands)
    if len(results) != 5 or len(definitions) != 2 or any(deps.values()):
        raise ValueError('expected five closed specification/mechanism results and two definitions')
    launch = dict(candidate=str(work), candidate_input_sha256=fp, command=KERNEL,
        main_inputs=before, staged_patch_sha256=index, commands=commands,
        results=results, definitions=definitions, dependencies={n: sorted(d) for n, d in deps.items()},
        source_sha256=s.sha((work / 'Coq' / NAME).read_bytes()),
        object_sha256=s.sha((work / 'Coq' / NAME).with_suffix('.vo').read_bytes()),
        driver_sha256=s.sha(Path(__file__).read_bytes()),
        compcert_execution_counterexample_proved=False, recursive_kernel_check=False, coverage_added=0)
    s.changed({HERE / 'REFERENCE-RUN.json': json.dumps(launch, indent=2) + '\n',
        **{HERE / (n + '.log'): (work / (n + '.log')).read_text() for n in commands}})
    commands['reference-kernel'] = s.run(work, KERNEL, 'reference-kernel', 1800)
    s.kernel.kernel((work / 'reference-kernel.log').read_text(), sorted((work / 'Coq/C/jet_coqchk_axioms.expected').read_text().split()))
    tree(work)
    if (s.input_map() != before or s.index_hash() != index or s.inputs.fingerprint(work / 'Coq', work) != fp):
        raise ValueError('reference check changed main/index/private source')
    record = dict(launch, commands=commands, recursive_kernel_check=True,
                  launch_sha256=s.sha((HERE / 'REFERENCE-RUN.json').read_bytes()))
    s.changed({HERE / 'REFERENCE-CHECKED.json': json.dumps(record, indent=2) + '\n',
               HERE / 'reference-kernel.log': (work / 'reference-kernel.log').read_text()})
    print('Five closed specification/reference facts kernel-checked; no formal C execution counterexample claimed', flush=True)


if __name__ == '__main__':
    if len(sys.argv) != 2:
        raise ValueError('usage: check-reference.py PRIVATE_TREE')
    main(Path(sys.argv[1]).resolve())
