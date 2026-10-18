"""Source-bound nonce-program bridge and original C body/entry checks."""
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
BASE = HERE.parent / 'elements-entropy-calls'
sp = importlib.util.spec_from_file_location('nonce_context_basis', BASE / 'kernel.py')
base = importlib.util.module_from_spec(sp)
sp.loader.exec_module(base)
s, g = base.s, base.v.g
NAMES = ['Spec', 'Shape']
MODULES = ['NonceContext.' + n for n in NAMES]
ROOTS = ['NonceContext.Spec', 'NonceContext.Shape']


def canonical_review():
    r = json.loads((HERE / 'SOURCE-REVIEW.json').read_text())
    if len(r['canonical_regions']) != 10:
        raise ValueError('canonical region inventory differs')
    for row in r['canonical_regions']:
        if (s.sha(row['text'].encode()) != row['sha256'] or
            (s.REPO / row['path']).read_text().count(row['text']) != 1):
            raise ValueError('canonical source region differs: ' + row['path'])
    if r['coq_sources_sha256'] != {n + '.v': s.sha((HERE / (n + '.v.source')).read_bytes()) for n in NAMES}:
        raise ValueError('reviewed nonce Coq source differs')


def identity(external):
    canonical_review()
    parent = json.loads((BASE / 'RUN.json').read_text())
    work = Path(parent['candidate'])
    base.identity(work)
    sources = [(m, external / (n + '.v')) for m, n in zip(MODULES, NAMES)]
    if (external == work or external == s.REPO or s.REPO in external.parents or
        {p.name for p in external.glob('*.v')} != {n + '.v' for n in NAMES}):
        raise ValueError('distinct exact external prefix tree required')
    for module, source in sources:
        if source.is_symlink() or source.read_bytes() != (HERE / (source.name + '.source')).read_bytes():
            raise ValueError('prefix source/archive differs: ' + module)
        s.safe_source(source.read_text(), module)
    return work, sources, ['-Q', str(external), 'NonceContext']


def profile(results, definitions, deps):
    if (len(results), len(definitions)) != (17, 20) or any(deps.values()):
        raise ValueError('expected seventeen closed results and twenty definitions')


def compile(external):
    if (HERE / 'RUN.json').exists():
        raise ValueError('prefix compile already recorded')
    work, sources, extra = identity(external)
    before, index = s.input_map(), s.index_hash()
    commands = {}
    for module, source in sources:
        stem = 'nonce-context-' + source.stem.lower() + '-fresh'
        commands[stem] = s.run(work, ['bash', 'build-jets.sh', '--coqc', '-q', *extra, str(source)], stem, 60)
    results, definitions, deps = g.reports(work, sources, 'nonce-context', commands, extra)
    profile(results, definitions, deps)
    command = ['bash', 'build-jets.sh', '--coqtop', '-quiet', *extra]
    query = subprocess.run(command, input='Require ' + ' '.join(ROOTS) + '.\nPrint Libraries.\n',
        cwd=work / 'Coq', env=s.ENV, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=60)
    if query.returncode or re.search(r'(?m)^(?:Error|Anomaly):', query.stdout):
        raise ValueError('prefix library query failed')
    local = {m.replace('.', '/') + '.v' for m in
        re.findall(r'^  ((?:C|Simplicity|Util)\.[A-Za-z0-9_.]+)$', query.stdout, re.M)}
    bound = json.loads((BASE / 'SOURCE-CLOSURE.json').read_text())
    objects = bound['compiled_and_loaded_local_modules']
    if len(local) != 111 or not local <= set(objects):
        raise ValueError('prefix imports lack the exact forced-source provenance')
    if set(re.findall(r'^  (NonceContext\.[A-Za-z0-9_.]+)$', query.stdout, re.M)) != set(MODULES):
        raise ValueError('unexpected prefix extension inventory')
    ext_objects = {m: dict(source_sha256=s.sha(p.read_bytes()), object_sha256=s.sha(p.with_suffix('.vo').read_bytes()))
                   for m, p in sources}
    identity(external)
    if before != s.input_map() or index != s.index_hash():
        raise ValueError('prefix compilation changed main/index')
    record = dict(candidate=str(work), external=str(external), main_inputs=before,
        staged_patch_sha256=index, commands=commands, results=results, definitions=definitions,
        dependencies={n: sorted(d) for n, d in deps.items()},
        parent_compile_sha256=s.sha((BASE / 'RUN.json').read_bytes()),
        parent_source_closure_sha256=s.sha((BASE / 'SOURCE-CLOSURE.json').read_bytes()),
        loaded_local_source_objects={n: objects[n] for n in sorted(local)}, extension_sources_objects=ext_objects,
        tools_sha256={'verify.py': s.sha(Path(__file__).read_bytes()), 'SOURCE-REVIEW.json': s.sha((HERE / 'SOURCE-REVIEW.json').read_bytes())},
        library_query=dict(command=command, exit_code=query.returncode, log_sha256=s.sha(query.stdout.encode())),
        actual_target_genv='elements_ge', logical_input_bits=1089,
        canonical_nonce_byte_bridge_proved=True, exact_c_body_and_entry_proved=True, recursive_kernel_check=False,
        public_frame_jet_lifecycle_proved=False, normal_registration=False, coverage_added=0)
    s.changed({HERE / 'RUN.json': json.dumps(record, indent=2) + '\n',
        HERE / 'loaded-libraries.log': query.stdout,
        **{HERE / (stem + '.log'): (work / (stem + '.log')).read_text() for stem in commands}})
    print('Nonce bridges and C body/entry compiled: 17 closed results, 111 source-bound imports', flush=True)


def kernel(external):
    if (HERE / 'KERNEL-RUN.json').exists():
        raise ValueError('prefix kernel already launched; inspect original process')
    work, sources, extra = identity(external)
    r = json.loads((HERE / 'RUN.json').read_text())
    force = s.load('entropy_frame_bound_objects', HERE.parent / 'verify-forced-closure.py')

    def bound():
        identity(external)
        force.objects(work, r['loaded_local_source_objects'])
        profile(r['results'], r['definitions'], {n: set(d) for n, d in r['dependencies'].items()})
        for m, p in sources:
            if r['extension_sources_objects'][m] != dict(source_sha256=s.sha(p.read_bytes()),
                object_sha256=s.sha(p.with_suffix('.vo').read_bytes())):
                raise ValueError('prefix source/object changed: ' + m)
        if (r['external'] != str(external) or r['main_inputs'] != s.input_map() or
            r['staged_patch_sha256'] != s.index_hash() or
            r['tools_sha256'] != {'verify.py': s.sha(Path(__file__).read_bytes()), 'SOURCE-REVIEW.json': s.sha((HERE / 'SOURCE-REVIEW.json').read_bytes())} or
            r['parent_compile_sha256'] != s.sha((BASE / 'RUN.json').read_bytes()) or
            r['parent_source_closure_sha256'] != s.sha((BASE / 'SOURCE-CLOSURE.json').read_bytes())):
            raise ValueError('prefix checked-input identity differs')
    bound()
    command = ['bash', '-c', 'ulimit -s 65520; exec bash build-jets.sh --coqchk -silent -o '
               + ' '.join(extra + ROOTS)]
    s.changed({HERE / 'KERNEL-RUN.json': json.dumps(dict(command=command,
        compile_sha256=s.sha((HERE / 'RUN.json').read_bytes()), recursive_kernel_check=False), indent=2) + '\n'})
    row = s.run(work, command, 'nonce-context-kernel', 3600)
    log = (work / 'nonce-context-kernel.log').read_text()
    context = sorted(log.split('* Axioms:\n', 1)[1].split('* Constants/Inductives', 1)[0].split())
    if not set(context) <= set((work / 'Coq/C/jet_coqchk_axioms.expected').read_text().split()):
        raise ValueError('unexpected prefix library dependency')
    s.kernel.kernel(log, context)
    bound()
    r.update(recursive_kernel_check=True, kernel=row, exact_library_context=context,
        kernel_launch_sha256=s.sha((HERE / 'KERNEL-RUN.json').read_bytes()))
    s.changed({HERE / 'CHECKED.json': json.dumps(r, indent=2) + '\n', HERE / 'nonce-context-kernel.log': log})
    print('Nonce bridges and C body/entry recursively kernel-checked; whole-jet execution remains open', flush=True)


if __name__ == '__main__':
    if len(sys.argv) != 3 or sys.argv[1] not in ['compile', 'kernel']:
        raise ValueError('usage: verify.py compile|kernel EXTERNAL_DIRECTORY')
    globals()[sys.argv[1]](Path(sys.argv[2]).resolve())
