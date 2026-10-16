"""Fresh seven-getter Elements proof/report and recursive kernel phases.

This extends the completed generic Reader checkpoint by one endpoint module.
Each phase freezes its main/index/private sources; no running audit cache or
main proof input is written. Coverage and canonical source review are separate.
"""
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('elements_stream_reader_checkpoint', HERE / 'check-reader.py')
reader = importlib.util.module_from_spec(sp)
sp.loader.exec_module(reader)
shared, s = reader.shared, reader.s
MODULES = [reader.MODULE, 'C.jet_elements_words_hash_program']
NEW = [m.replace('.', '/') + '.v' for m in MODULES]
FRESH = ['C.jet_elements_hash_getter_local', 'C.jet_elements_hash_getter_writehash', *MODULES]
ENDPOINTS = [MODULES[1] + '.elements_' + n + '_program_local_spec' for n in [
    'output_scripts_hash', 'output_range_proofs_hash', 'output_surjection_proofs_hash',
    'input_scripts_hash', 'input_sequences_hash', 'input_script_sigs_hash', 'tappath_hash']]
KERNEL = ['bash', '-c', 'ulimit -s 65520; exec bash build-jets.sh --coqchk -silent -o ' + ' '.join(MODULES)]


def tree(work):
    prior = json.loads((HERE / 'READER-CHECKED.json').read_text())
    base_record = json.loads(reader.BASE_RECEIPT.read_text())
    base = Path(base_record['candidate'])
    if (work == s.REPO or s.REPO in work.parents or work == base or (work / 'Coq').is_symlink() or
        prior['candidate'] != str(work) or prior['base_candidate'] != str(base) or
        prior['base_acceptance_sha256'] != s.sha(reader.BASE_RECEIPT.read_bytes()) or
        prior['base_input_sha256'] != base_record['audit_input_sha256'] or
        s.inputs.fingerprint(base / 'Coq', base) != base_record['audit_input_sha256'] or
        prior['tools_sha256'] != {'check-reader.py': s.sha((HERE / 'check-reader.py').read_bytes())}):
        raise ValueError('completed reader/private/full420 source boundary changed')
    inherited = shared.inventory(base / 'Coq')
    if shared.inventory(work / 'Coq') != inherited | set(NEW):
        raise ValueError('unexpected stream source/metadata inventory')
    for name in inherited:
        if (work / 'Coq' / name).read_bytes() != (base / 'Coq' / name).read_bytes():
            raise ValueError('inherited stream source differs: ' + name)
    for name in NEW:
        p = work / 'Coq' / name
        if p.is_symlink() or p.read_bytes() != (HERE / 'source' / (p.name + '.source')).read_bytes():
            raise ValueError('archived/private stream proof differs')
        s.safe_source(p.read_text(), name)
    if s.sha((work / 'Coq' / reader.NAME).read_bytes()) != prior['source_sha256']:
        raise ValueError('completed generic Reader source changed')
    return base, prior


def compile(work):
    if (HERE / 'RUN.json').exists():
        raise ValueError('stream compilation already completed; inspect its recorded evidence')
    base, prior = tree(work)
    if s.sha((work / 'Coq' / reader.NAME).with_suffix('.vo').read_bytes()) != prior['object_sha256']:
        raise ValueError('fresh generic Reader object changed before extension')
    before, index = s.input_map(), s.index_hash()
    fingerprint = s.inputs.fingerprint(work / 'Coq', work)
    commands = {}
    for module in FRESH:
        commands[module] = s.run(work, ['bash', 'build-jets.sh', '--coqc', '-q', module.replace('.', '/') + '.v'], module, 120)
        print('Freshly compiled ' + module, flush=True)
    results, definitions, deps = shared.reports(work,
        [(m, work / 'Coq' / n) for m, n in zip(MODULES, NEW)], 'elements-stream', commands)
    if (len(results), len(definitions)) != (36, 10) or not set(ENDPOINTS) <= set(results):
        raise ValueError('wrong complete Elements stream declaration inventory')
    if any(deps[n] != s.SIX for n in ENDPOINTS):
        raise ValueError('Elements stream endpoint assumptions changed')
    tree(work)
    if (s.input_map() != before or s.index_hash() != index or
        s.inputs.fingerprint(work / 'Coq', work) != fingerprint):
        raise ValueError('stream compile/report phase changed main/index/private source')
    record = dict(candidate=str(work), base_candidate=str(base),
        reader_checkpoint_sha256=s.sha((HERE / 'READER-CHECKED.json').read_bytes()),
        base_acceptance_sha256=s.sha(reader.BASE_RECEIPT.read_bytes()),
        candidate_input_sha256=fingerprint, main_inputs_at_compile=before, staged_patch_sha256=index,
        modules=MODULES, fresh_modules=FRESH, new_sources=NEW, results=results, definitions=definitions,
        endpoints=ENDPOINTS, closed_results=[n for n in results if not deps[n]],
        dependencies={n: sorted(ds) for n, ds in deps.items()}, commands=commands,
        source_sha256={m: s.sha((work / 'Coq' / (m.replace('.', '/') + '.v')).read_bytes()) for m in FRESH},
        object_sha256={m: s.sha((work / 'Coq' / (m.replace('.', '/') + '.vo')).read_bytes()) for m in FRESH},
        tools_sha256={'check.py': s.sha(Path(__file__).read_bytes())},
        literal_programs_over_raw_elements_data=True, whole_c_endpoints=7,
        caller_cached_hashes_established=False, canonical_family_source_review_complete=False,
        recursive_kernel_check=False, normal_registration=False, coverage_added=0, full_acceptance=False)
    s.changed({HERE / 'RUN.json': json.dumps(record, indent=2) + '\n',
        **{HERE / (n + '.log'): (work / (n + '.log')).read_text() for n in commands}})
    print('Seven whole-C Elements hash-program endpoints freshly compiled/reported; kernel/source/admission remain', flush=True)


def kernel(work):
    if (HERE / 'KERNEL-RUN.json').exists():
        raise ValueError('Elements stream kernel phase already launched; inspect existing handle/terminal')
    record = json.loads((HERE / 'RUN.json').read_text())
    if record['candidate'] != str(work) or record['tools_sha256'] != {'check.py': s.sha(Path(__file__).read_bytes())}:
        raise ValueError('stream compile phase candidate/checker differs')
    tree(work)
    for field, suffix in [('source_sha256', '.v'), ('object_sha256', '.vo')]:
        for module, digest in record[field].items():
            if s.sha((work / 'Coq' / (module.replace('.', '/') + suffix)).read_bytes()) != digest:
                raise ValueError('fresh stream source/object changed between phases')
    before, index = s.input_map(), s.index_hash()
    if index != record['staged_patch_sha256']:
        raise ValueError('original stage changed between stream phases')
    launch = dict(candidate=str(work), command=KERNEL,
        compiled_receipt_sha256=s.sha((HERE / 'RUN.json').read_bytes()),
        candidate_input_sha256=record['candidate_input_sha256'], main_inputs_at_kernel=before,
        staged_patch_sha256=index, recursive_kernel_check=False)
    s.changed({HERE / 'KERNEL-RUN.json': json.dumps(launch, indent=2) + '\n'})
    commands = dict(record['commands'])
    commands['ast'] = s.run(work, ['bash', 'C/check-elements-jets-generation.sh'], 'ast', 300)
    commands['kernel'] = s.run(work, KERNEL, 'kernel', 3600)
    s.kernel.kernel((work / 'kernel.log').read_text(), sorted((work / 'Coq/C/jet_coqchk_axioms.expected').read_text().split()))
    tree(work)
    if (s.input_map() != before or s.index_hash() != index or
        s.inputs.fingerprint(work / 'Coq', work) != record['candidate_input_sha256']):
        raise ValueError('stream kernel phase changed main/index/private source')
    record.update(commands=commands, main_inputs_at_kernel=before,
        kernel_launch_sha256=s.sha((HERE / 'KERNEL-RUN.json').read_bytes()), recursive_kernel_check=True)
    s.changed({HERE / 'CHECKED.json': json.dumps(record, indent=2) + '\n',
        **{HERE / (n + '.log'): (work / (n + '.log')).read_text() for n in ['ast', 'kernel']}})
    print('Seven original-C Elements hash-program endpoints recursively kernel-checked; source/admission review remains', flush=True)


if __name__ == '__main__':
    if len(sys.argv) != 3 or sys.argv[1] not in ['compile', 'kernel']:
        raise ValueError('usage: check.py compile|kernel PRIVATE_TREE')
    (compile if sys.argv[1] == 'compile' else kernel)(Path(sys.argv[2]).resolve())
