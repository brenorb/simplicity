"""Once-only recursive kernel/AST phase for the compiled outpoints endpoint."""
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('elements_outpoints_fresh_kernel', HERE / 'check.py')
g = importlib.util.module_from_spec(sp)
sp.loader.exec_module(g)
s = g.s
COMMAND = ['bash', '-c', 'ulimit -s 65520; exec bash build-jets.sh --coqchk -silent -o ' + g.MODULE]


def main(work):
    if (HERE / 'KERNEL-RUN.json').exists():
        raise ValueError('outpoints kernel phase already launched; poll its existing handle')
    record = json.loads((HERE / 'RUN.json').read_text())
    if (record['candidate'] != str(work) or record['recursive_kernel_check'] is not False or
        record['tools_sha256'] != {'check.py': s.sha((HERE / 'check.py').read_bytes())}):
        raise ValueError('outpoints fresh compilation identity/scope differs')
    g.tree(work)
    for field, suffix in [('source_sha256', '.v'), ('object_sha256', '.vo')]:
        if set(record[field]) != {g.MODULE}:
            raise ValueError('incomplete outpoints source/object inventory')
        for module, digest in record[field].items():
            if s.sha((work / 'Coq' / (module.replace('.', '/') + suffix)).read_bytes()) != digest:
                raise ValueError('outpoints source/object changed before kernel phase')
    for stem, row in record['commands'].items():
        log = work / (stem + '.log')
        if (row['exit_code'] != 0 or row['log_sha256'] != s.sha(log.read_bytes()) or
            (HERE / log.name).read_bytes() != log.read_bytes()):
            raise ValueError('outpoints fresh compilation report changed')
    before, index = s.input_map(), s.index_hash()
    if (before != record['main_inputs'] or index != record['staged_patch_sha256'] or
        s.inputs.fingerprint(work / 'Coq', work) != record['candidate_input_sha256']):
        raise ValueError('outpoints private/main/index input changed between phases')
    launch = dict(candidate=str(work), command=COMMAND,
        compiled_receipt_sha256=s.sha((HERE / 'RUN.json').read_bytes()),
        candidate_input_sha256=record['candidate_input_sha256'], staged_patch_sha256=index,
        driver_sha256=s.sha(Path(__file__).read_bytes()), recursive_kernel_check=False)
    s.changed({HERE / 'KERNEL-RUN.json': json.dumps(launch, indent=2) + '\n'})
    commands = dict(record['commands'])
    commands['ast'] = s.run(work, ['bash', 'C/check-elements-jets-generation.sh'], 'ast', 300)
    commands['kernel'] = s.run(work, COMMAND, 'kernel', 3600)
    s.kernel.kernel((work / 'kernel.log').read_text(), sorted((work / 'Coq/C/jet_coqchk_axioms.expected').read_text().split()))
    g.tree(work)
    if (s.input_map() != before or s.index_hash() != index or
        s.inputs.fingerprint(work / 'Coq', work) != record['candidate_input_sha256']):
        raise ValueError('outpoints kernel changed main/index/private source')
    record.update(commands=commands, recursive_kernel_check=True,
        kernel_launch_sha256=s.sha((HERE / 'KERNEL-RUN.json').read_bytes()))
    s.changed({HERE / 'CHECKED.json': json.dumps(record, indent=2) + '\n',
        **{HERE / (n + '.log'): (work / (n + '.log')).read_text() for n in ['ast', 'kernel']}})
    print('Original Elements literal-tag outpoints C endpoint recursively kernel-checked; source/admission remain', flush=True)


if __name__ == '__main__':
    if len(sys.argv) != 2:
        raise ValueError('usage: kernel.py PRIVATE_TREE')
    main(Path(sys.argv[1]).resolve())
