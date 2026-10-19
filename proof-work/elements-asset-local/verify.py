"""Complete original Elements asset_amount_hash C-to-canonical specification proof."""
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
PARENT = HERE.parent / 'elements-amount-phase'
sp = importlib.util.spec_from_file_location('asset_local_parent', PARENT / 'verify.py')
middle = importlib.util.module_from_spec(sp)
sp.loader.exec_module(middle)
s, g = middle.s, middle.g
NAMES = ['Buffer', 'ContextHashes', 'TaggedWord', 'Spec', 'Counter', 'Bridges', 'Local', 'Actual']
MODULES = ['AssetLocal.' + n for n in NAMES]
ROOT = 'AssetLocal.Actual'


def profile(results, definitions, deps):
    groups = {
        'Buffer': ['ctx8_add_buffer_spec_parametric', 'ctx8_add_buffer_option', 'ctx8_add1_some_count',
                   'ctx8_add_list_some_count', 'ctx8_add_buffer_model_list', 'ctx8_add_values'],
        'ContextHashes': ['outpoint_hash_spec_parametric', 'annex_hash_spec_parametric', 'outpoint_hash_option', 'annex_hash_option'],
        'TaggedWord': ['ctx8_tagged_word_spec_parametric', 'ctx8_tagged_word_option'],
        'Spec': ['conf_tag_byte_spec_parametric', 'conf_tag_byte_value', 'conf_tag_byte_option',
                 'asset_tag_payload_spec_parametric', 'asset_tag_payload_value', 'elements_asset_hash_spec_parametric',
                 'elements_asset_hash_option', 'elements_amount_hash_spec_parametric', 'elements_amount_hash_option',
                 'elements_asset_amount_hash_spec_parametric', 'elements_asset_amount_hash_option',
                 'elements_asset_bytes_length', 'elements_amount_bytes_bound', 'elements_asset_amount_bytes_bound'],
        'Counter': ['sha_chain_overflow', 'asset_amount_counter', 'asset_amount_overflow'],
        'Bridges': ['asset_bytes_canonical', 'amount_bytes_canonical', 'asset_amount_bytes_canonical',
                    'asset_amount_option', 'asset_amount_stream_count', 'asset_entry_sha', 'amount_temps_other', 'asset_temps_other'],
        'Local': ['asset_amount_hash_sha_local_spec'], 'Actual': ['asset_globals_equiv', 'asset_amount_hash_local_spec']}
    expected = {'AssetLocal.' + m + '.' + n: set() for m, names in groups.items() for n in names}
    for m in ['Local.asset_amount_hash_sha_local_spec', 'Actual.asset_amount_hash_local_spec']:
        expected['AssetLocal.' + m] = s.SIX
    expected['AssetLocal.Actual.asset_globals_equiv'] = middle.asset.phase.context.base.FOUR
    ds = {'Buffer': ['ctx8_add_buffer_spec', 'ctx8_count', 'ctx8_add_buffer_model'],
          'ContextHashes': ['outpoint_hash_spec', 'byte_one', 'annex_hash_spec', 'byte_zero'],
          'TaggedWord': ['ctx8_tagged_word_spec'],
          'Spec': ['elements_hash_conf_type', 'elements_asset_hash_type', 'elements_amount_hash_type', 'elements_asset_amount_type',
                   'asset_byte_even', 'asset_byte_odd', 'amount_byte_even', 'amount_byte_odd', 'conf_tag_byte_spec', 'asset_tag_payload_spec',
                   'elements_asset_hash_spec', 'elements_asset_bytes', 'elements_amount_hash_spec', 'elements_amount_bytes',
                   'elements_asset_amount_hash_spec', 'elements_asset_amount_bytes'],
          'Actual': ['asset_elements_globals_ok', 'asset_elements_partial_local_spec']}
    defs = {'AssetLocal.' + m + '.' + n for m, names in ds.items() for n in names}
    if len(results) != 40 or set(results) != set(expected) or set(definitions) != defs or deps != expected:
        raise ValueError('exact forty-result/twenty-six-definition profile differs: 37 closed, one FOUR, two SIX')


def review():
    r = json.loads((HERE / 'SOURCE-REVIEW.json').read_text())
    if len(r['canonical_regions']) != 6 or set(r['ports']) != {'Buffer', 'ContextHashes', 'TaggedWord', 'Spec'}:
        raise ValueError('canonical source/port inventory differs')
    for row in r['canonical_regions']:
        if s.sha(row['text'].encode()) != row['sha256'] or (s.REPO / row['path']).read_text().count(row['text']) != 1:
            raise ValueError('canonical reviewed source differs: ' + row['path'])
    for n, row in r['ports'].items():
        raw = (s.REPO / row['path']).read_text()
        if s.sha(raw.encode()) != row['source_sha256']:
            raise ValueError('port basis differs: ' + n)
        for old, new in r['import_replacements'].items():
            raw = raw.replace(old, new)
        if raw != (HERE / (n + '.v.source')).read_text() or s.sha(raw.encode()) != row['ported_sha256']:
            raise ValueError('non-import port change: ' + n)
    if r['coq_sources_sha256'] != {n + '.v': s.sha((HERE / (n + '.v.source')).read_bytes()) for n in NAMES}:
        raise ValueError('reviewed lifecycle sources differ')


def identity(external):
    review()
    parent = json.loads((PARENT / 'RUN.json').read_text())
    work, parent_ext = Path(parent['candidate']), Path(parent['external'])
    _, parent_sources, inherited, parent_extra = middle.identity(parent_ext)
    if parent['main_inputs'] != s.input_map() or parent['staged_patch_sha256'] != s.index_hash():
        raise ValueError('parent middle-phase input identity differs')
    if parent['tools_sha256'] != {'verify.py': s.sha((PARENT / 'verify.py').read_bytes())}:
        raise ValueError('parent middle-phase driver differs')
    for m, p in parent_sources:
        row = dict(source_sha256=s.sha(p.read_bytes()), object_sha256=s.sha(p.with_suffix('.vo').read_bytes()))
        if parent['extension_sources_objects'][m] != row:
            raise ValueError('inherited middle source/object differs: ' + m)
        inherited[m] = row
    nonce_dir = HERE.parent / 'elements-nonce-local'
    nonce = json.loads((nonce_dir / 'CHECKED.json').read_text())
    common = Path(nonce['external']) / 'Common.v'
    if (not nonce['recursive_kernel_check'] or nonce['kernel']['exit_code'] != 0 or
        nonce['main_inputs'] != s.input_map() or nonce['staged_patch_sha256'] != s.index_hash() or
        common.is_symlink() or common.read_bytes() != (nonce_dir / 'Common.v.source').read_bytes() or
        nonce['extension_sources_objects']['NonceLocal.Common'] != dict(source_sha256=s.sha(common.read_bytes()),
            object_sha256=s.sha(common.with_suffix('.vo').read_bytes()))):
        raise ValueError('checked generic frame contract/source copy differs')
    inherited['NonceLocal.Common'] = nonce['extension_sources_objects']['NonceLocal.Common']
    sources = [(m, external / (n + '.v')) for m, n in zip(MODULES, NAMES)]
    if (external in [work, parent_ext, Path(nonce['external']), s.REPO] or s.REPO in external.parents or
        {p.name for p in external.glob('*.v')} != {n + '.v' for n in NAMES}):
        raise ValueError('distinct exact external full lifecycle tree required')
    for m, p in sources:
        if p.is_symlink() or p.read_bytes() != (HERE / (p.name + '.source')).read_bytes():
            raise ValueError('lifecycle archive differs: ' + m)
        s.safe_source(p.read_text(), m)
    return work, sources, inherited, parent_extra + ['-Q', nonce['external'], 'NonceLocal', '-Q', str(external), 'AssetLocal']


def compile(external):
    if (HERE / 'RUN.json').exists():
        raise ValueError('asset/amount lifecycle compilation already recorded')
    work, sources, inherited, extra = identity(external)
    before, index = s.input_map(), s.index_hash()
    commands = {}
    for m, p in sources:
        stem = 'asset-local-' + p.stem.lower() + '-fresh'
        commands[stem] = s.run(work, ['bash', 'build-jets.sh', '--coqc', '-q', *extra, str(p)], stem, 60)
    results, definitions, deps = g.reports(work, sources, 'asset-local', commands, extra)
    profile(results, definitions, deps)
    command = ['bash', 'build-jets.sh', '--coqtop', '-quiet', *extra]
    query = subprocess.run(command, input='Require ' + ROOT + '.\nPrint Libraries.\n', cwd=work / 'Coq',
        env=s.ENV, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=60)
    if query.returncode or re.search(r'(?m)^(?:Error|Anomaly):', query.stdout):
        raise ValueError('asset/amount lifecycle library query failed')
    local = {m.replace('.', '/') + '.v' for m in
        re.findall(r'^  ((?:C|Simplicity|Util)\.[A-Za-z0-9_.]+)$', query.stdout, re.M)}
    bound = json.loads((middle.asset.phase.context.BASE / 'SOURCE-CLOSURE.json').read_text())
    if len(local) != 260 or not local <= set(bound['compiled_and_loaded_local_modules']):
        raise ValueError('asset/amount lifecycle imports lack exact forced-source provenance')
    extensions = set(re.findall(r'^  ((?:AssetLocal|AmountExec|AssetExec|NonceLocal|NonceExec|NonceContext)\.[A-Za-z0-9_.]+)$', query.stdout, re.M))
    if extensions != set(MODULES) | set(inherited):
        raise ValueError('unexpected asset/amount lifecycle extension inventory')
    own = {m: dict(source_sha256=s.sha(p.read_bytes()), object_sha256=s.sha(p.with_suffix('.vo').read_bytes()))
           for m, p in sources}
    identity(external)
    if before != s.input_map() or index != s.index_hash():
        raise ValueError('asset/amount lifecycle build changed main/index')
    record = dict(candidate=str(work), external=str(external), main_inputs=before, staged_patch_sha256=index,
        commands=commands, results=results, definitions=definitions, dependencies={n: sorted(d) for n, d in deps.items()},
        parent_middle_compile_sha256=s.sha((PARENT / 'RUN.json').read_bytes()),
        parent_context_checked_sha256=s.sha((middle.asset.phase.PARENT / 'CHECKED.json').read_bytes()),
        parent_source_closure_sha256=s.sha((middle.asset.phase.context.BASE / 'SOURCE-CLOSURE.json').read_bytes()),
        loaded_local_source_objects={n: bound['compiled_and_loaded_local_modules'][n] for n in sorted(local)},
        inherited_extension_sources_objects=inherited, extension_sources_objects=own,
        tools_sha256={'verify.py': s.sha(Path(__file__).read_bytes()), 'SOURCE-REVIEW.json': s.sha((HERE / 'SOURCE-REVIEW.json').read_bytes())},
        library_query=dict(command=command, exit_code=query.returncode, log_sha256=s.sha(query.stdout.encode())),
        actual_target_genv='elements_ge', logical_input_bits=1346, output_bits=830,
        memcpy_model_explicit=True, dispatch_and_max_counter_explicit=True,
        whole_jet_execution_proved=True, canonical_option_program=True,
        initial_context_rejection=True, final_overflow_rejection=True,
        explicit_and_confidential_amounts=True, all_asset_variants=True, arbitrary_valid_frames=True,
        recursive_kernel_check=False, normal_registration=False, coverage_added=0)
    s.changed({HERE / 'RUN.json': json.dumps(record, indent=2) + '\n', HERE / 'loaded-libraries.log': query.stdout,
        **{HERE / (stem + '.log'): (work / (stem + '.log')).read_text() for stem in commands}})
    print('Complete original asset_amount_hash C-to-canonical equivalence compiled; exact forty-result profile and 260 source-bound imports', flush=True)


def kernel(external):
    if (HERE / 'KERNEL-RUN.json').exists():
        raise ValueError('asset/amount lifecycle kernel already launched; inspect original process')
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
            r['parent_context_checked_sha256'] != s.sha((middle.asset.phase.PARENT / 'CHECKED.json').read_bytes()) or
            r['parent_source_closure_sha256'] != s.sha((middle.asset.phase.context.BASE / 'SOURCE-CLOSURE.json').read_bytes())):
            raise ValueError('asset/amount lifecycle checked-input identity differs')
        for m, p in sources:
            if r['extension_sources_objects'][m] != dict(source_sha256=s.sha(p.read_bytes()),
                object_sha256=s.sha(p.with_suffix('.vo').read_bytes())):
                raise ValueError('asset/amount lifecycle source/object changed: ' + m)
    bound()
    command = ['bash', '-c', 'ulimit -s 65520; exec bash build-jets.sh --coqchk -silent -o '
               + ' '.join(extra + [ROOT])]
    s.changed({HERE / 'KERNEL-RUN.json': json.dumps(dict(command=command,
        compile_sha256=s.sha((HERE / 'RUN.json').read_bytes()), recursive_kernel_check=False), indent=2) + '\n'})
    row = s.run(work, command, 'asset-local-kernel', 3600)
    log = (work / 'asset-local-kernel.log').read_text()
    s.kernel.kernel(log, sorted((work / 'Coq/C/jet_coqchk_axioms.expected').read_text().split()))
    bound()
    r.update(recursive_kernel_check=True, kernel=row,
        kernel_launch_sha256=s.sha((HERE / 'KERNEL-RUN.json').read_bytes()))
    s.changed({HERE / 'CHECKED.json': json.dumps(r, indent=2) + '\n', HERE / 'asset-local-kernel.log': log})
    print('Complete original asset_amount_hash C-to-canonical equivalence recursively kernel-checked', flush=True)


if __name__ == '__main__':
    if len(sys.argv) != 3 or sys.argv[1] not in ['compile', 'kernel']:
        raise ValueError('usage: verify.py compile|kernel EXTERNAL_DIRECTORY')
    globals()[sys.argv[1]](Path(sys.argv[2]).resolve())
