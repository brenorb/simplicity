"""Source-bound original asset/amount middle-phase execution proofs."""
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
PARENT = HERE.parent / 'elements-asset-phase'
sp = importlib.util.spec_from_file_location('amount_phase_parent', PARENT / 'verify.py')
asset = importlib.util.module_from_spec(sp)
sp.loader.exec_module(asset)
s, g = asset.s, asset.g
NAMES = ['Common', 'Payload8', 'Phase', 'Seq', 'Compose']
MODULES = ['AmountExec.' + n for n in NAMES]
ROOT = 'AmountExec.Compose'


def profile(results, definitions, deps):
    closed = ['Common.' + n for n in ['amount_explicit_encoding', 'amount_confidential_encoding',
              'amount_prefix_machine', 'amount_bytes_length', 'amount_counter_one_then_8']]
    six = ['Common.amount_skip_exec', 'Payload8.amount_payload8_exec', 'Phase.amount_explicit_exec',
           'Phase.amount_confidential_exec', 'Phase.amount_phase_exec', 'Seq.amount_seq_normal_inv',
           'Compose.asset_amount_middle_exec', 'Compose.asset_amount_middle_then']
    expected = {'AmountExec.' + n: d for ns, d in [(closed, set()), (six, s.SIX)] for n in ns}
    defs = {'AmountExec.Common.' + n for n in ['amount_value_type', 'amount_bytes', 'amount_count',
             'amount_payload_count', 'amount_overflow', 'amount_temps']}
    defs |= {'AmountExec.Compose.asset_amount_middle', 'AmountExec.Compose.asset_overflow'}
    if len(results) != 13 or set(results) != set(expected) or set(definitions) != defs or deps != expected:
        raise ValueError('exact thirteen-result/eight-definition profile differs: five closed, eight SIX')


def identity(external):
    parent = json.loads((PARENT / 'RUN.json').read_text())
    work, parent_ext = Path(parent['candidate']), Path(parent['external'])
    _, parent_sources, inherited, parent_extra = asset.identity(parent_ext)
    if parent['main_inputs'] != s.input_map() or parent['staged_patch_sha256'] != s.index_hash():
        raise ValueError('parent asset-phase input identity differs')
    if parent['tools_sha256'] != {'verify.py': s.sha((PARENT / 'verify.py').read_bytes())}:
        raise ValueError('parent asset-phase driver differs')
    for m, p in parent_sources:
        row = dict(source_sha256=s.sha(p.read_bytes()), object_sha256=s.sha(p.with_suffix('.vo').read_bytes()))
        if parent['extension_sources_objects'][m] != row:
            raise ValueError('inherited asset source/object changed: ' + m)
        inherited[m] = row
    sources = [(m, external / (n + '.v')) for m, n in zip(MODULES, NAMES)]
    if (external in [work, parent_ext, s.REPO] or s.REPO in external.parents or
        {p.name for p in external.glob('*.v')} != {n + '.v' for n in NAMES}):
        raise ValueError('distinct exact external amount/middle tree required')
    for m, p in sources:
        if p.is_symlink() or p.read_bytes() != (HERE / (p.name + '.source')).read_bytes():
            raise ValueError('amount/middle archive differs: ' + m)
        s.safe_source(p.read_text(), m)
    return work, sources, inherited, parent_extra + ['-Q', str(external), 'AmountExec']


def compile(external):
    if (HERE / 'RUN.json').exists():
        raise ValueError('amount/middle phase compilation already recorded')
    work, sources, inherited, extra = identity(external)
    before, index = s.input_map(), s.index_hash()
    commands = {}
    for m, p in sources:
        stem = 'amount-phase-' + p.stem.lower() + '-fresh'
        commands[stem] = s.run(work, ['bash', 'build-jets.sh', '--coqc', '-q', *extra, str(p)], stem, 60)
    results, definitions, deps = g.reports(work, sources, 'amount-phase', commands, extra)
    profile(results, definitions, deps)
    command = ['bash', 'build-jets.sh', '--coqtop', '-quiet', *extra]
    query = subprocess.run(command, input='Require ' + ROOT + '.\nPrint Libraries.\n', cwd=work / 'Coq',
        env=s.ENV, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=60)
    if query.returncode or re.search(r'(?m)^(?:Error|Anomaly):', query.stdout):
        raise ValueError('amount/middle phase library query failed')
    local = {m.replace('.', '/') + '.v' for m in
        re.findall(r'^  ((?:C|Simplicity|Util)\.[A-Za-z0-9_.]+)$', query.stdout, re.M)}
    bound = json.loads((asset.phase.context.BASE / 'SOURCE-CLOSURE.json').read_text())
    if len(local) != 251 or not local <= set(bound['compiled_and_loaded_local_modules']):
        raise ValueError('amount/middle phase imports lack exact forced-source provenance')
    extensions = set(re.findall(r'^  ((?:AmountExec|AssetExec|NonceExec|NonceContext)\.[A-Za-z0-9_.]+)$', query.stdout, re.M))
    if extensions != set(MODULES) | set(inherited):
        raise ValueError('unexpected amount/middle phase extension inventory')
    own = {m: dict(source_sha256=s.sha(p.read_bytes()), object_sha256=s.sha(p.with_suffix('.vo').read_bytes()))
           for m, p in sources}
    identity(external)
    if before != s.input_map() or index != s.index_hash():
        raise ValueError('amount/middle phase build changed main/index')
    record = dict(candidate=str(work), external=str(external), main_inputs=before, staged_patch_sha256=index,
        commands=commands, results=results, definitions=definitions, dependencies={n: sorted(d) for n, d in deps.items()},
        parent_asset_compile_sha256=s.sha((PARENT / 'RUN.json').read_bytes()),
        parent_context_checked_sha256=s.sha((asset.phase.PARENT / 'CHECKED.json').read_bytes()),
        parent_source_closure_sha256=s.sha((asset.phase.context.BASE / 'SOURCE-CLOSURE.json').read_bytes()),
        loaded_local_source_objects={n: bound['compiled_and_loaded_local_modules'][n] for n in sorted(local)},
        inherited_extension_sources_objects=inherited, extension_sources_objects=own,
        tools_sha256={'verify.py': s.sha(Path(__file__).read_bytes())},
        library_query=dict(command=command, exit_code=query.returncode, log_sha256=s.sha(query.stdout.encode())),
        actual_target_genv='elements_ge', logical_jet_input_bits=1346, phase_input_bits=516,
        memcpy_model_explicit=True, initial_live_context_explicit=True,
        whole_middle_execution_proved=True, whole_jet_execution_proved=False, canonical_option_program=False,
        explicit_and_confidential_amounts=True, all_asset_variants=True,
        arbitrary_valid_frames=True, private_source_advance_bits=516,
        recursive_kernel_check=False, normal_registration=False, coverage_added=0)
    s.changed({HERE / 'RUN.json': json.dumps(record, indent=2) + '\n', HERE / 'loaded-libraries.log': query.stdout,
        **{HERE / (stem + '.log'): (work / (stem + '.log')).read_text() for stem in commands}})
    print('Complete original asset/amount C middle execution compiled; exact thirteen-result profile and 251 source-bound imports', flush=True)


def kernel(external):
    if (HERE / 'KERNEL-RUN.json').exists():
        raise ValueError('amount/middle phase kernel already launched; inspect original process')
    work, sources, inherited, extra = identity(external)
    r = json.loads((HERE / 'RUN.json').read_text())
    force = s.load('nonce_local_bound_objects', HERE.parent / 'verify-forced-closure.py')

    def bound():
        _, _, current, _ = identity(external)
        force.objects(work, r['loaded_local_source_objects'])
        profile(r['results'], r['definitions'], {n: set(d) for n, d in r['dependencies'].items()})
        if (r['external'] != str(external) or r['main_inputs'] != s.input_map() or
            r['staged_patch_sha256'] != s.index_hash() or r['inherited_extension_sources_objects'] != current or
            r['tools_sha256'] != {'verify.py': s.sha(Path(__file__).read_bytes())} or
            r['parent_asset_compile_sha256'] != s.sha((PARENT / 'RUN.json').read_bytes()) or
            r['parent_context_checked_sha256'] != s.sha((asset.phase.PARENT / 'CHECKED.json').read_bytes()) or
            r['parent_source_closure_sha256'] != s.sha((asset.phase.context.BASE / 'SOURCE-CLOSURE.json').read_bytes())):
            raise ValueError('amount/middle phase checked-input identity differs')
        for m, p in sources:
            if r['extension_sources_objects'][m] != dict(source_sha256=s.sha(p.read_bytes()),
                object_sha256=s.sha(p.with_suffix('.vo').read_bytes())):
                raise ValueError('amount/middle phase source/object changed: ' + m)
    bound()
    command = ['bash', '-c', 'ulimit -s 65520; exec bash build-jets.sh --coqchk -silent -o '
               + ' '.join(extra + [ROOT])]
    s.changed({HERE / 'KERNEL-RUN.json': json.dumps(dict(command=command,
        compile_sha256=s.sha((HERE / 'RUN.json').read_bytes()), recursive_kernel_check=False), indent=2) + '\n'})
    row = s.run(work, command, 'amount-phase-kernel', 3600)
    log = (work / 'amount-phase-kernel.log').read_text()
    s.kernel.kernel(log, sorted((work / 'Coq/C/jet_coqchk_axioms.expected').read_text().split()))
    bound()
    r.update(recursive_kernel_check=True, kernel=row,
        kernel_launch_sha256=s.sha((HERE / 'KERNEL-RUN.json').read_bytes()))
    s.changed({HERE / 'CHECKED.json': json.dumps(r, indent=2) + '\n', HERE / 'amount-phase-kernel.log': log})
    print('Complete original asset/amount C middle execution recursively kernel-checked', flush=True)


if __name__ == '__main__':
    if len(sys.argv) != 3 or sys.argv[1] not in ['compile', 'kernel']:
        raise ValueError('usage: verify.py compile|kernel EXTERNAL_DIRECTORY')
    globals()[sys.argv[1]](Path(sys.argv[2]).resolve())
