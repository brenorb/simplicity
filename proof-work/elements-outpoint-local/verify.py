"""Complete original Elements outpoint_hash C-to-canonical specification proof."""
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
PARENT = HERE.parent / 'elements-outpoint-middle'
sp = importlib.util.spec_from_file_location('outpoint_local_parent', PARENT / 'verify.py')
middle = importlib.util.module_from_spec(sp)
sp.loader.exec_module(middle)
s, g = middle.s, middle.g
NAMES = ['Spec', 'Counter', 'Bridges', 'Local', 'Actual']
MODULES = ['OutpointLocal.' + n for n in NAMES]
ROOT = 'OutpointLocal.Actual'


def profile(results, definitions, deps):
    closed = ['Spec.elements_outpoint_hash_spec_parametric', 'Spec.op_annex_bytes', 'Spec.elements_outpoint_hash_option',
              'Counter.sha_chain_overflow', 'Counter.op_counter_total', 'Counter.op_overflow_total',
              'Bridges.op_entry_sha', 'Bridges.op_blocks_sha']
    four = ['Actual.outpoint_globals_equiv']
    six = ['Bridges.op_source_copy', 'Local.op_hash_sha_local_spec', 'Actual.outpoint_hash_local_spec']
    expected = {'OutpointLocal.' + n: d for ns, d in [(closed, set()),
                (four, middle.calls.phase.context.base.FOUR), (six, s.SIX)] for n in ns}
    defs = {'OutpointLocal.Spec.elements_outpoint_hash_spec', 'OutpointLocal.Actual.outpoint_elements_globals_ok',
            'OutpointLocal.Actual.outpoint_elements_partial_local_spec'}
    if len(results) != 12 or set(results) != set(expected) or set(definitions) != defs or deps != expected:
        raise ValueError('exact twelve-result/three-definition profile differs: eight closed, one FOUR, three SIX')


def review():
    r = json.loads((HERE / 'SOURCE-REVIEW.json').read_text())
    if len(r['canonical_regions']) != 10:
        raise ValueError('canonical region inventory differs')
    for row in r['canonical_regions']:
        if s.sha(row['text'].encode()) != row['sha256'] or (s.REPO / row['path']).read_text().count(row['text']) != 1:
            raise ValueError('canonical reviewed source differs: ' + row['path'])
    if r['coq_sources_sha256'] != {n + '.v': s.sha((HERE / (n + '.v.source')).read_bytes()) for n in NAMES}:
        raise ValueError('reviewed lifecycle sources differ')
    old = (HERE.parent / 'elements-asset-local/Counter.v.source').read_text()
    new = (HERE / 'Counter.v.source').read_text()
    old = old[old.index('Lemma sha_chain_overflow'):old.index('Lemma asset_amount_counter')]
    new = new[new.index('Lemma sha_chain_overflow'):new.index('Lemma op_counter_total')]
    if old != new:
        raise ValueError('reused sticky-overflow proof changed')


def identity(external):
    review()
    parent = json.loads((PARENT / 'RUN.json').read_text())
    work, parent_ext = Path(parent['candidate']), Path(parent['external'])
    _, parent_sources, inherited, parent_extra = middle.identity(parent_ext)
    if parent['main_inputs'] != s.input_map() or parent['staged_patch_sha256'] != s.index_hash():
        raise ValueError('parent outpoint-middle input identity differs')
    if parent['tools_sha256'] != {'verify.py': s.sha((PARENT / 'verify.py').read_bytes())}:
        raise ValueError('parent outpoint-middle driver differs')
    for m, p in parent_sources:
        row = dict(source_sha256=s.sha(p.read_bytes()), object_sha256=s.sha(p.with_suffix('.vo').read_bytes()))
        if parent['extension_sources_objects'][m] != row:
            raise ValueError('inherited middle source/object differs: ' + m)
        inherited[m] = row
    support = []
    for name, modules in [('elements-nonce-local', ['NonceLocal.Common']),
                          ('elements-asset-local', ['AssetLocal.Buffer', 'AssetLocal.ContextHashes']),
                          ('elements-nonce-phase', ['NonceExec.Phase'])]:
        archive = HERE.parent / name
        r = json.loads((archive / 'CHECKED.json').read_text())
        if (not r['recursive_kernel_check'] or r['kernel']['exit_code'] != 0 or Path(r['candidate']) != work or
            r['main_inputs'] != s.input_map() or r['staged_patch_sha256'] != s.index_hash()):
            raise ValueError('checked support basis differs: ' + name)
        for module in modules:
            p = Path(r['external']) / (module.rsplit('.', 1)[1] + '.v')
            row = dict(source_sha256=s.sha(p.read_bytes()), object_sha256=s.sha(p.with_suffix('.vo').read_bytes()))
            if p.is_symlink() or p.read_bytes() != (archive / (p.name + '.source')).read_bytes() or row != r['extension_sources_objects'][module]:
                raise ValueError('checked support source/object differs: ' + module)
            inherited[module] = row
        if name != 'elements-nonce-phase':
            support += ['-Q', r['external'], modules[0].split('.')[0]]
    sources = [(m, external / (n + '.v')) for m, n in zip(MODULES, NAMES)]
    if (external in [work, parent_ext, s.REPO] or s.REPO in external.parents or
        {p.name for p in external.glob('*.v')} != {n + '.v' for n in NAMES}):
        raise ValueError('distinct exact external full outpoint lifecycle tree required')
    for m, p in sources:
        if p.is_symlink() or p.read_bytes() != (HERE / (p.name + '.source')).read_bytes():
            raise ValueError('lifecycle archive differs: ' + m)
        s.safe_source(p.read_text(), m)
    return work, sources, inherited, parent_extra + support + ['-Q', str(external), 'OutpointLocal']


def compile(external):
    if (HERE / 'RUN.json').exists():
        raise ValueError('outpoint lifecycle compilation already recorded')
    work, sources, inherited, extra = identity(external)
    before, index = s.input_map(), s.index_hash()
    commands = {}
    for m, p in sources:
        stem = 'outpoint-local-' + p.stem.lower() + '-fresh'
        commands[stem] = s.run(work, ['bash', 'build-jets.sh', '--coqc', '-q', *extra, str(p)], stem, 60)
    results, definitions, deps = g.reports(work, sources, 'outpoint-local', commands, extra)
    profile(results, definitions, deps)
    command = ['bash', 'build-jets.sh', '--coqtop', '-quiet', *extra]
    query = subprocess.run(command, input='Require ' + ROOT + '.\nPrint Libraries.\n', cwd=work / 'Coq',
        env=s.ENV, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=60)
    if query.returncode or re.search(r'(?m)^(?:Error|Anomaly):', query.stdout):
        raise ValueError('outpoint lifecycle library query failed')
    local = {m.replace('.', '/') + '.v' for m in
        re.findall(r'^  ((?:C|Simplicity|Util)\.[A-Za-z0-9_.]+)$', query.stdout, re.M)}
    bound = json.loads((middle.calls.phase.context.BASE / 'SOURCE-CLOSURE.json').read_text())
    if len(local) != 260 or not local <= set(bound['compiled_and_loaded_local_modules']):
        raise ValueError('outpoint lifecycle imports lack exact forced-source provenance')
    extensions = set(re.findall(r'^  ((?:OutpointLocal|OutpointMiddle|OutpointExec|AssetLocal|NonceLocal|NonceExec|NonceContext)\.[A-Za-z0-9_.]+)$', query.stdout, re.M))
    if extensions != set(MODULES) | set(inherited):
        raise ValueError('unexpected outpoint lifecycle extension inventory')
    own = {m: dict(source_sha256=s.sha(p.read_bytes()), object_sha256=s.sha(p.with_suffix('.vo').read_bytes()))
           for m, p in sources}
    identity(external)
    if before != s.input_map() or index != s.index_hash():
        raise ValueError('outpoint lifecycle build changed main/index')
    record = dict(candidate=str(work), external=str(external), main_inputs=before, staged_patch_sha256=index,
        commands=commands, results=results, definitions=definitions, dependencies={n: sorted(d) for n, d in deps.items()},
        parent_middle_compile_sha256=s.sha((PARENT / 'RUN.json').read_bytes()),
        support_checked_sha256={n: s.sha((HERE.parent / n / 'CHECKED.json').read_bytes()) for n in
            ['elements-nonce-local', 'elements-asset-local', 'elements-nonce-phase']},
        parent_context_checked_sha256=s.sha((middle.calls.phase.PARENT / 'CHECKED.json').read_bytes()),
        parent_source_closure_sha256=s.sha((middle.calls.phase.context.BASE / 'SOURCE-CLOSURE.json').read_bytes()),
        loaded_local_source_objects={n: bound['compiled_and_loaded_local_modules'][n] for n in sorted(local)},
        inherited_extension_sources_objects=inherited, extension_sources_objects=own,
        tools_sha256={'verify.py': s.sha(Path(__file__).read_bytes()), 'SOURCE-REVIEW.json': s.sha((HERE / 'SOURCE-REVIEW.json').read_bytes())},
        library_query=dict(command=command, exit_code=query.returncode, log_sha256=s.sha(query.stdout.encode())),
        actual_target_genv='elements_ge', logical_input_bits=1375, output_bits=830,
        memcpy_model_explicit=True, dispatch_and_max_counter_explicit=True,
        whole_jet_execution_proved=True, canonical_option_program=True,
        initial_context_rejection=True, final_overflow_rejection=True,
        all_pegin_hash_index_values=True, arbitrary_valid_frames=True,
        recursive_kernel_check=False, normal_registration=False, coverage_added=0)
    s.changed({HERE / 'RUN.json': json.dumps(record, indent=2) + '\n', HERE / 'loaded-libraries.log': query.stdout,
        **{HERE / (stem + '.log'): (work / (stem + '.log')).read_text() for stem in commands}})
    print('Complete original outpoint_hash C-to-canonical equivalence compiled; exact twelve-result profile and 260 source-bound imports', flush=True)


def kernel(external):
    if (HERE / 'KERNEL-RUN.json').exists():
        raise ValueError('outpoint lifecycle kernel already launched; inspect original process')
    work, sources, inherited, extra = identity(external)
    r = json.loads((HERE / 'RUN.json').read_text())
    force = s.load('nonce_local_bound_objects', HERE.parent / 'verify-forced-closure.py')

    def bound():
        _, _, current, _ = identity(external)
        force.objects(work, r['loaded_local_source_objects'])
        profile(r['results'], r['definitions'], {n: set(d) for n, d in r['dependencies'].items()})
        if (r['external'] != str(external) or r['main_inputs'] != s.input_map() or
            r['staged_patch_sha256'] != s.index_hash() or r['inherited_extension_sources_objects'] != current or
            r['tools_sha256'] != {'verify.py': s.sha(Path(__file__).read_bytes()), 'SOURCE-REVIEW.json': s.sha((HERE / 'SOURCE-REVIEW.json').read_bytes())} or
            r['parent_middle_compile_sha256'] != s.sha((PARENT / 'RUN.json').read_bytes()) or
            r['support_checked_sha256'] != {n: s.sha((HERE.parent / n / 'CHECKED.json').read_bytes()) for n in
                ['elements-nonce-local', 'elements-asset-local', 'elements-nonce-phase']} or
            r['parent_context_checked_sha256'] != s.sha((middle.calls.phase.PARENT / 'CHECKED.json').read_bytes()) or
            r['parent_source_closure_sha256'] != s.sha((middle.calls.phase.context.BASE / 'SOURCE-CLOSURE.json').read_bytes())):
            raise ValueError('outpoint lifecycle checked-input identity differs')
        for m, p in sources:
            if r['extension_sources_objects'][m] != dict(source_sha256=s.sha(p.read_bytes()),
                object_sha256=s.sha(p.with_suffix('.vo').read_bytes())):
                raise ValueError('outpoint lifecycle source/object changed: ' + m)
    bound()
    command = ['bash', '-c', 'ulimit -s 65520; exec bash build-jets.sh --coqchk -silent -o '
               + ' '.join(extra + [ROOT])]
    s.changed({HERE / 'KERNEL-RUN.json': json.dumps(dict(command=command,
        compile_sha256=s.sha((HERE / 'RUN.json').read_bytes()), recursive_kernel_check=False), indent=2) + '\n'})
    row = s.run(work, command, 'outpoint-local-kernel', 3600)
    log = (work / 'outpoint-local-kernel.log').read_text()
    s.kernel.kernel(log, sorted((work / 'Coq/C/jet_coqchk_axioms.expected').read_text().split()))
    bound()
    r.update(recursive_kernel_check=True, kernel=row,
        kernel_launch_sha256=s.sha((HERE / 'KERNEL-RUN.json').read_bytes()))
    s.changed({HERE / 'CHECKED.json': json.dumps(r, indent=2) + '\n', HERE / 'outpoint-local-kernel.log': log})
    print('Complete original outpoint_hash C-to-canonical equivalence recursively kernel-checked', flush=True)


if __name__ == '__main__':
    if len(sys.argv) != 3 or sys.argv[1] not in ['compile', 'kernel']:
        raise ValueError('usage: verify.py compile|kernel EXTERNAL_DIRECTORY')
    globals()[sys.argv[1]](Path(sys.argv[2]).resolve())
