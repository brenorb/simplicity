"""Check six closed entry/header lemmas on the source-bound original AST."""
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('frame_source_base', HERE.parent / 'elements-issuance-computed/verify.py')
base = importlib.util.module_from_spec(sp)
sp.loader.exec_module(base)
s, g = base.s, base.g
MODULE = 'CalculationFrame.CalculationFrame'
BASE = HERE.parent / 'elements-issuance-computed'


def main(external):
    if (HERE / 'RUN.json').exists():
        raise ValueError('entry verification already launched; inspect the original process')
    bound = json.loads((BASE / 'SOURCE-CLOSURE.json').read_text())
    if not json.loads((BASE / 'SOURCE-CHECKED.json').read_text())['recursive_kernel_check']:
        raise ValueError('completed source-bound basis required')
    work = Path(bound['candidate'])
    force = s.load('frame_source_objects', HERE.parent / 'verify-forced-closure.py')
    source = external / 'CalculationFrame.v'
    def identity():
        base.tree(work)
        force.objects(work, bound['compiled_and_loaded_local_modules'])
        if s.sha((BASE / 'RUN.json').read_bytes()) != bound['compile_sha256']:
            raise ValueError('source-bound base compile differs')
        if (external == work or external == s.REPO or s.REPO in external.parents or
            source.is_symlink() or source.read_bytes() != (HERE / 'CalculationFrame.v.source').read_bytes() or
            {p.name for p in external.glob('*.v')} != {'CalculationFrame.v'}):
            raise ValueError('distinct exact source required')
        s.safe_source(source.read_text(), MODULE)
    identity()
    before, index = s.input_map(), s.index_hash()
    extra = ['-Q', str(external), 'CalculationFrame']
    commands = {'frame-entry-fresh': s.run(work, ['bash', 'build-jets.sh', '--coqc', '-q',
        *extra, str(source)], 'frame-entry-fresh', 60)}
    results, definitions, deps = g.reports(work, [(MODULE, source)], 'frame-entry', commands, extra)
    if (len(results), len(definitions)) != (6, 5) or any(deps.values()):
        raise ValueError('expected six closed preparation results and five definitions')
    command = ['bash', 'build-jets.sh', '--coqtop', '-quiet', *extra]
    query = subprocess.run(command, input='Require ' + MODULE + '.\nPrint Libraries.\n',
        cwd=work / 'Coq', env=s.ENV, text=True, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT, timeout=60)
    if query.returncode or re.search(r'(?m)^(?:Error|Anomaly):', query.stdout):
        raise ValueError('entry library query failed')
    local = {m.replace('.', '/') + '.v' for m in
        re.findall(r'^  ((?:C|Simplicity|Util)\.[A-Za-z0-9_.]+)$', query.stdout, re.M)}
    if not local or not local <= set(bound['compiled_and_loaded_local_modules']):
        raise ValueError('an imported local object lacks source-bound provenance')
    if re.findall(r'^  (CalculationFrame\.[A-Za-z0-9_.]+)$', query.stdout, re.M) != [MODULE]:
        raise ValueError('unexpected entry extension libraries')
    identity()
    record = dict(candidate=str(work), external=str(external), module=MODULE,
        main_inputs=before, staged_patch_sha256=index, commands=commands,
        results=results, definitions=definitions, dependencies={n: sorted(d) for n, d in deps.items()},
        base_source_closure_sha256=s.sha((BASE / 'SOURCE-CLOSURE.json').read_bytes()),
        loaded_local_source_objects={n: bound['compiled_and_loaded_local_modules'][n] for n in sorted(local)},
        source_sha256=s.sha(source.read_bytes()), object_sha256=s.sha(source.with_suffix('.vo').read_bytes()),
        tools_sha256={'verify.py': s.sha(Path(__file__).read_bytes())},
        recursive_kernel_check=False, complete_jet_equivalence=False, coverage_added=0)
    s.changed({HERE / 'RUN.json': json.dumps(record, indent=2) + '\n',
        HERE / 'loaded-libraries.log': query.stdout,
        **{HERE / (stem + '.log'): (work / (stem + '.log')).read_text() for stem in commands}})
    command = ['bash', '-c', 'ulimit -s 65520; exec bash build-jets.sh --coqchk -silent -o '
               + ' '.join(extra) + ' ' + MODULE]
    s.changed({HERE / 'KERNEL-RUN.json': json.dumps(dict(command=command,
        compile_sha256=s.sha((HERE / 'RUN.json').read_bytes()), recursive_kernel_check=False), indent=2) + '\n'})
    row = s.run(work, command, 'frame-entry-kernel', 600)
    log = (work / 'frame-entry-kernel.log').read_text()
    context = sorted(log.split('* Axioms:\n', 1)[1].split('* Constants/Inductives', 1)[0].split())
    # This small prefix loads fewer libraries. It may only use a subset of the
    # already approved library context; all six theorem dependencies are empty.
    allowed = set((work / 'Coq/C/jet_coqchk_axioms.expected').read_text().split())
    if not set(context) <= allowed:
        raise ValueError('unreviewed library axiom in the entry-only prefix')
    s.kernel.kernel(log, context)
    identity()
    if (s.input_map() != before or s.index_hash() != index or
        record['source_sha256'] != s.sha(source.read_bytes()) or
        record['object_sha256'] != s.sha(source.with_suffix('.vo').read_bytes())):
        raise ValueError('entry audit changed source/object/base/main/index')
    record.update(recursive_kernel_check=True, kernel=row, exact_library_context=context,
                  kernel_launch_sha256=s.sha((HERE / 'KERNEL-RUN.json').read_bytes()))
    s.changed({HERE / 'CHECKED.json': json.dumps(record, indent=2) + '\n',
               HERE / 'frame-entry-kernel.log': log})
    print('Six closed four-local frame-entry/header lemmas recursively kernel-checked; jet body remains open', flush=True)


if __name__ == '__main__':
    if len(sys.argv) != 2:
        raise ValueError('usage: verify.py EXTERNAL_DIRECTORY')
    main(Path(sys.argv[1]).resolve())
