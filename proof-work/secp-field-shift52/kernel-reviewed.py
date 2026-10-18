"""Strict small-closure kernel context, preserving the original failed gate."""
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('shift_original_verifier', HERE / 'verify.py')
v = importlib.util.module_from_spec(sp)
sp.loader.exec_module(v)
s = v.s


def main(work):
    if (HERE / 'KERNEL-REVIEW-RUN.json').exists():
        raise ValueError('reviewed kernel already launched; inspect original handle')
    modules, extra = v.sources(work)
    r = json.loads((HERE / 'RUN.json').read_text())
    failure = json.loads((HERE / 'FIRST-KERNEL-GATE-FAILURE.json').read_text())
    expected = sorted((HERE / 'kernel-axioms.expected').read_text().split())
    omitted = {'Coq.Logic.PropExtensionality.propositional_extensionality',
               'Coq.Sets.Ensembles.Extensionality_Ensembles', 'VST.msl.Axioms.prop_ext'}
    full = set((work / 'Coq/C/jet_coqchk_axioms.expected').read_text().split())
    if (len(expected) != 12 or set(expected) != full - omitted or
            set(failure['omitted_library_context']) != omitted or failure['additional_axioms'] or
            failure['proof_sources_changed'] or failure['coqchk_exit_code'] != 0 or
            failure['kernel_log_sha256'] != s.sha((HERE / 'first-shift-kernel.log').read_bytes())):
        raise ValueError('not the reviewed strict subset of the inherited library context')
    s.kernel.kernel((HERE / 'first-shift-kernel.log').read_text(), expected)
    tools = {n: s.sha((HERE / n).read_bytes()) for n in
             ['verify.py', 'kernel-reviewed.py', 'kernel-axioms.expected', 'FIRST-KERNEL-GATE-FAILURE.json']}

    def bound():
        v.sources(work)
        if (r['candidate'] != str(work) or r['main_inputs'] != s.input_map() or
                r['staged_patch_sha256'] != s.index_hash() or r['tools_sha256'] != {'verify.py': tools['verify.py']} or
                tools != {n: s.sha((HERE / n).read_bytes()) for n in tools}):
            raise ValueError('checked input or review policy changed')
        v.profile(r['results'], r['definitions'], {n: set(d) for n, d in r['dependencies'].items()})
        for n, row in r['loaded_local_source_objects'].items():
            p = work / 'Coq' / n
            if row != dict(source_sha256=s.sha(p.read_bytes()), object_sha256=s.sha(p.with_suffix('.vo').read_bytes())):
                raise ValueError('forced local source/object changed: ' + n)
        for m, p in modules:
            if r['extension_sources_objects'][m] != dict(source_sha256=s.sha(p.read_bytes()),
                    object_sha256=s.sha(p.with_suffix('.vo').read_bytes())):
                raise ValueError('extension source/object changed: ' + m)
    bound()
    cmd = ['bash', '-c', 'ulimit -s 65520; exec bash build-jets.sh --coqchk -silent -o '
           + ' '.join(extra + v.ROOTS)]
    s.changed({HERE / 'KERNEL-REVIEW-RUN.json': json.dumps(dict(command=cmd, tools_sha256=tools,
        compile_sha256=s.sha((HERE / 'RUN.json').read_bytes()), recursive_kernel_check=False), indent=2) + '\n'})
    row = s.run(work, cmd, 'shift-reviewed-kernel', 3600)
    log = (work / 'shift-reviewed-kernel.log').read_text()
    s.kernel.kernel(log, expected)
    bound()
    r.update(recursive_kernel_check=True, kernel=row, reviewed_kernel_tools_sha256=tools,
        kernel_launch_sha256=s.sha((HERE / 'KERNEL-REVIEW-RUN.json').read_bytes()))
    s.changed({HERE / 'CHECKED.json': json.dumps(r, indent=2) + '\n', HERE / 'shift-kernel.log': log})
    print('18 original-C shift results recursively kernel-checked; exact inherited 12-axiom library context', flush=True)


if __name__ == '__main__':
    if len(sys.argv) != 2:
        raise ValueError('usage: kernel-reviewed.py PRIVATE_TREE')
    main(Path(sys.argv[1]).resolve())
