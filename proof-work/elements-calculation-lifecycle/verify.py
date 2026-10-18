"""Check actual calculation-jet lifecycle pieces against a source-bound AST.

This package has no complete public-jet theorem or accepted coverage yet.
"""
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
BASE = HERE.parent / 'elements-calculation-calls'
sp = importlib.util.spec_from_file_location('lifecycle_base', BASE / 'calls.py')
base = importlib.util.module_from_spec(sp)
sp.loader.exec_module(base)
s, g = base.s, base.g
NAMES = ['Entry', 'Allocation', 'Shape', 'Read', 'Writer']
MODULES = ['CalculationLifecycle.' + n for n in NAMES]


def profile(results, definitions, deps):
    four = ['Allocation.calc_alloc_list_props', 'Shape.calc_local_addr',
            'Shape.calc_local_array', 'Shape.eval_calc_helper_args', 'Writer.calc_mid_arg']
    six = ['Shape.' + n for n in ['exec_calc_source_copy', 'exec_calc_read',
           'exec_calc_helper', 'exec_calc_result_copy', 'exec_calc_write', 'calc_function_composes']]
    six += ['Read.calc_read_prefix', 'Writer.calc_writehash_wrap', 'Writer.calc_writehash_from_frame']
    expected = {n: set() for n in results}
    expected.update({'CalculationLifecycle.' + n: base.FOUR for n in four})
    expected.update({'CalculationLifecycle.' + n: s.SIX for n in six})
    if (len(results), len(definitions)) != (32, 19) or deps != expected:
        raise ValueError('complete per-result lifecycle assumption profile differs')


def main(external):
    if (HERE / 'RUN.json').exists():
        raise ValueError('audit already launched; inspect its original process')
    bound = json.loads((BASE / 'SOURCE-CLOSURE.json').read_text())
    work = Path(bound['candidate'])
    if not json.loads((BASE / 'CALLS-CHECKED.json').read_text())['recursive_kernel_check']:
        raise ValueError('completed original-program basis required')
    force = s.load('lifecycle_closure', HERE.parent / 'verify-forced-closure.py')
    sources = [(m, external / (n + '.v')) for m, n in zip(MODULES, NAMES)]

    def identity():
        base.base.tree(work)
        base.basis_profile(json.loads((BASE / 'RUN.json').read_text()))
        force.objects(work, bound['compiled_and_loaded_local_modules'])
        if s.sha((BASE / 'RUN.json').read_bytes()) != bound['compile_sha256']:
            raise ValueError('basis source closure identity differs')
        if (external == work or external == s.REPO or s.REPO in external.parents or
            {p.name for p in external.glob('*.v')} != {n + '.v' for n in NAMES}):
            raise ValueError('distinct exact external lifecycle tree required')
        for module, p in sources:
            if p.is_symlink() or p.read_bytes() != (HERE / (p.name + '.source')).read_bytes():
                raise ValueError('lifecycle source differs: ' + module)
            s.safe_source(p.read_text(), module)

    identity()
    before, index = s.input_map(), s.index_hash()
    extra = ['-Q', str(external), 'CalculationLifecycle']
    commands = {}
    for module, p in sources:
        stem = 'lifecycle-' + p.stem.lower() + '-fresh'
        commands[stem] = s.run(work, ['bash', 'build-jets.sh', '--coqc', '-q', *extra, str(p)], stem, 60)
    results, definitions, deps = g.reports(work, sources, 'lifecycle-checked', commands, extra)
    profile(results, definitions, deps)
    command = ['bash', 'build-jets.sh', '--coqtop', '-quiet', *extra]
    query = subprocess.run(command, input='Require ' + ' '.join(MODULES) + '.\nPrint Libraries.\n',
        cwd=work / 'Coq', env=s.ENV, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=60)
    if query.returncode or re.search(r'(?m)^(?:Error|Anomaly):', query.stdout):
        raise ValueError('lifecycle loaded-library query failed')
    local = {m.replace('.', '/') + '.v' for m in
        re.findall(r'^  ((?:C|Simplicity|Util)\.[A-Za-z0-9_.]+)$', query.stdout, re.M)}
    if not local or not local <= set(bound['compiled_and_loaded_local_modules']):
        raise ValueError('a lifecycle dependency lacks fresh source-bound provenance')
    if set(re.findall(r'^  (CalculationLifecycle\.[A-Za-z0-9_.]+)$', query.stdout, re.M)) != set(MODULES):
        raise ValueError('unexpected lifecycle libraries')
    objects = {m: dict(source_sha256=s.sha(p.read_bytes()), object_sha256=s.sha(p.with_suffix('.vo').read_bytes()))
               for m, p in sources}
    identity()
    if s.input_map() != before or s.index_hash() != index:
        raise ValueError('lifecycle compilation changed main inputs or staging')
    record = dict(candidate=str(work), external=str(external), modules=MODULES,
        main_inputs=before, staged_patch_sha256=index, commands=commands,
        results=results, definitions=definitions, dependencies={n: sorted(d) for n, d in deps.items()},
        basis_source_closure_sha256=s.sha((BASE / 'SOURCE-CLOSURE.json').read_bytes()),
        loaded_local_source_objects={n: bound['compiled_and_loaded_local_modules'][n] for n in sorted(local)},
        extension_sources_objects=objects, tools_sha256={'verify.py': s.sha(Path(__file__).read_bytes())},
        library_query=dict(command=command, exit_code=query.returncode, log_sha256=s.sha(query.stdout.encode())),
        actual_target_genv='elements_ge', recursive_kernel_check=False,
        public_frame_jet_lifecycle_proved=False, normal_registration=False, coverage_added=0)
    s.changed({HERE / 'RUN.json': json.dumps(record, indent=2) + '\n',
        HERE / 'loaded-libraries.log': query.stdout,
        **{HERE / (stem + '.log'): (work / (stem + '.log')).read_text() for stem in commands}})
    command = ['bash', '-c', 'ulimit -s 65520; exec bash build-jets.sh --coqchk -silent -o '
               + ' '.join(extra + MODULES)]
    s.changed({HERE / 'KERNEL-RUN.json': json.dumps(dict(command=command,
        compile_sha256=s.sha((HERE / 'RUN.json').read_bytes()), recursive_kernel_check=False), indent=2) + '\n'})
    row = s.run(work, command, 'lifecycle-kernel', 3600)
    log = (work / 'lifecycle-kernel.log').read_text()
    context = sorted(log.split('* Axioms:\n', 1)[1].split('* Constants/Inductives', 1)[0].split())
    if not set(context) <= set((work / 'Coq/C/jet_coqchk_axioms.expected').read_text().split()):
        raise ValueError('unexpected library dependency in lifecycle audit')
    s.kernel.kernel(log, context)
    identity()
    for m, p in sources:
        if objects[m] != dict(source_sha256=s.sha(p.read_bytes()), object_sha256=s.sha(p.with_suffix('.vo').read_bytes())):
            raise ValueError('lifecycle extension source/object changed during kernel check')
    if s.input_map() != before or s.index_hash() != index:
        raise ValueError('lifecycle kernel audit changed main or index')
    record.update(recursive_kernel_check=True, kernel=row, exact_library_context=context,
        kernel_launch_sha256=s.sha((HERE / 'KERNEL-RUN.json').read_bytes()))
    s.changed({HERE / 'CHECKED.json': json.dumps(record, indent=2) + '\n', HERE / 'lifecycle-kernel.log': log})
    print('32 actual calculation lifecycle-piece results recursively kernel-checked; full public composition remains open', flush=True)


if __name__ == '__main__':
    if len(sys.argv) != 2:
        raise ValueError('usage: verify.py EXTERNAL_DIRECTORY')
    main(Path(sys.argv[1]).resolve())
