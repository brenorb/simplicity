"""Fresh raw-program transport and sixteen whole-C getter proofs.

Compilation and recursive kernel checking are separate once-only phases.
Guarded main integration may happen between them; neither phase writes main,
and both bind the same immutable private sources and exact fresh objects.
"""
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('raw_program_shared', HERE.parent / 'elements-tap-getters/check.py')
shared = importlib.util.module_from_spec(sp)
sp.loader.exec_module(shared)
s = shared.s
BASE_RECEIPT = HERE.parent / 'bitcoin-tapleaf-literal/EVIDENCE-REVIEW.json'
MODULES = ['C.jet_bitcoin_raw_program', 'C.jet_bitcoin_hash_raw_program']
NEW = [m.replace('.', '/') + '.v' for m in MODULES]
FRESH = ['C.jet_bitcoin_words_hash', 'C.jet_bitcoin_composite_hash', 'C.jet_bitcoin_tx_hash',
         'C.jet_bitcoin_sig_all_hash', *MODULES]
ENDPOINTS = [MODULES[1] + '.bitcoin_' + n + '_raw_program_local_spec' for n in [
    'output_values_hash', 'output_scripts_hash', 'input_values_hash', 'input_scripts_hash',
    'input_sequences_hash', 'input_script_sigs_hash', 'tappath_hash', 'tapleaf_hash',
    'outputs_hash', 'input_utxos_hash', 'tap_env_hash', 'input_outpoints_hash',
    'input_annexes_hash', 'inputs_hash', 'tx_hash', 'sig_all_hash']]
KERNEL = ['bash', '-c', 'ulimit -s 65520; exec bash build-jets.sh --coqchk -silent -o ' + ' '.join(MODULES)]


def tree(work):
    receipt = json.loads(BASE_RECEIPT.read_text())
    base = Path(receipt['review']['candidate'])
    if work == base or work == s.REPO or s.REPO in work.parents or (work / 'Coq').is_symlink():
        raise ValueError('use a distinct private raw-program tree')
    if (receipt['review']['recursive_kernel_check'] is not True or
        receipt['checked_sha256'] != s.sha((BASE_RECEIPT.parent / 'CHECKED.json').read_bytes()) or
        s.inputs.fingerprint(base / 'Coq', base) != receipt['candidate_input_sha256']):
        raise ValueError('completed tapleaf proof base changed')
    inherited = shared.inventory(base / 'Coq')
    if shared.inventory(work / 'Coq') != inherited | set(NEW):
        raise ValueError('unexpected raw-program source/metadata inventory')
    for n in inherited:
        if (work / 'Coq' / n).read_bytes() != (base / 'Coq' / n).read_bytes():
            raise ValueError('inherited source changed: ' + n)
    for n in NEW:
        p = work / 'Coq' / n
        if p.read_bytes() != (HERE / 'source' / (p.name + '.source')).read_bytes():
            raise ValueError('archived/private raw-program proof differs')
        s.safe_source(p.read_text(), n)
    return base, receipt


def compile(work):
    if (HERE / 'RUN.json').exists():
        raise ValueError('compile phase already completed; inspect its recorded evidence')
    base, prior = tree(work)
    before, index = s.input_map(), s.index_hash()
    fingerprint = s.inputs.fingerprint(work / 'Coq', work)
    commands = {}
    for m in FRESH:
        commands[m] = s.run(work, ['bash', 'build-jets.sh', '--coqc', '-q', m.replace('.', '/') + '.v'], m, 300)
        print('Freshly compiled ' + m, flush=True)
    results, definitions, deps = shared.reports(work,
        [(m, work / 'Coq' / n) for m, n in zip(MODULES, NEW)], 'raw-program', commands)
    if (len(results), len(definitions)) != (23, 4) or not set(ENDPOINTS) <= set(results):
        raise ValueError('wrong complete raw-program declaration inventory')
    if any(deps[n] != s.SIX for n in ENDPOINTS):
        raise ValueError('raw whole-C endpoint assumptions changed')
    tree(work)
    if s.input_map() != before or s.index_hash() != index or s.inputs.fingerprint(work / 'Coq', work) != fingerprint:
        raise ValueError('compile phase changed main/index/private sources')
    record = dict(candidate=str(work), base_candidate=str(base),
        base_receipt_sha256=s.sha(BASE_RECEIPT.read_bytes()), base_input_sha256=prior['candidate_input_sha256'],
        candidate_input_sha256=fingerprint, main_inputs_at_compile=before, staged_patch_sha256=index,
        modules=MODULES, fresh_modules=FRESH, new_sources=NEW, results=results, definitions=definitions,
        endpoints=ENDPOINTS, closed_results=[n for n in results if not deps[n]],
        dependencies={n: sorted(ds) for n, ds in deps.items()}, commands=commands,
        source_sha256={m: s.sha((work / 'Coq' / (m.replace('.', '/') + '.v')).read_bytes()) for m in FRESH},
        object_sha256={m: s.sha((work / 'Coq' / (m.replace('.', '/') + '.vo')).read_bytes()) for m in FRESH},
        tools_sha256={'check.py': s.sha(Path(__file__).read_bytes())},
        raw_data_interpretation=True, whole_c_endpoints=16, all_caller_setup_proved=False,
        canonical_family_source_review_complete=False, recursive_kernel_check=False,
        normal_registration=False, coverage_added=0, full_acceptance=False)
    s.changed({HERE / 'RUN.json': json.dumps(record, indent=2) + '\n',
        **{HERE / (n + '.log'): (work / (n + '.log')).read_text() for n in commands}})
    print('Sixteen whole-C endpoints and shared raw-program transport freshly compiled/reported; kernel phase remains', flush=True)


def kernel(work):
    if (HERE / 'KERNEL-RUN.json').exists():
        raise ValueError('kernel phase already launched; inspect its existing handle/terminal')
    record = json.loads((HERE / 'RUN.json').read_text())
    if record['candidate'] != str(work) or record['tools_sha256'] != {'check.py': s.sha(Path(__file__).read_bytes())}:
        raise ValueError('compile phase candidate/checker differs')
    tree(work)
    for field, suffix in [('source_sha256', '.v'), ('object_sha256', '.vo')]:
        for m, digest in record[field].items():
            if s.sha((work / 'Coq' / (m.replace('.', '/') + suffix)).read_bytes()) != digest:
                raise ValueError('fresh compiled source/object changed between phases')
    before, index = s.input_map(), s.index_hash()
    if index != record['staged_patch_sha256']:
        raise ValueError('original staged patch changed between phases')
    launch = dict(candidate=str(work), command=KERNEL,
        compiled_receipt_sha256=s.sha((HERE / 'RUN.json').read_bytes()),
        candidate_input_sha256=record['candidate_input_sha256'], main_inputs_at_kernel=before,
        staged_patch_sha256=index, recursive_kernel_check=False)
    s.changed({HERE / 'KERNEL-RUN.json': json.dumps(launch, indent=2) + '\n'})
    commands = dict(record['commands'])
    commands['ast'] = s.run(work, ['bash', 'C/check-bitcoin-jets-generation.sh'], 'ast', 180)
    commands['kernel'] = s.run(work, KERNEL, 'kernel', 1800)
    s.kernel.kernel((work / 'kernel.log').read_text(), sorted((work / 'Coq/C/jet_coqchk_axioms.expected').read_text().split()))
    tree(work)
    if (s.input_map() != before or s.index_hash() != index or
        s.inputs.fingerprint(work / 'Coq', work) != record['candidate_input_sha256']):
        raise ValueError('kernel phase changed main/index/private inputs')
    record.update(commands=commands, main_inputs_at_kernel=before,
        kernel_launch_sha256=s.sha((HERE / 'KERNEL-RUN.json').read_bytes()), recursive_kernel_check=True)
    s.changed({HERE / 'CHECKED.json': json.dumps(record, indent=2) + '\n',
        **{HERE / (n + '.log'): (work / (n + '.log')).read_text() for n in ['ast', 'kernel']}})
    print('Sixteen original-C raw-program endpoints recursively kernel-checked; source/admission review remains', flush=True)


if __name__ == '__main__':
    if len(sys.argv) != 3 or sys.argv[1] not in ['compile', 'kernel']:
        raise ValueError('usage: check.py compile|kernel PRIVATE_TREE')
    (compile if sys.argv[1] == 'compile' else kernel)(Path(sys.argv[2]).resolve())
