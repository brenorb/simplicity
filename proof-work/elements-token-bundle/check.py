"""Fresh six-module token proof bundle; no source change or normal admission claim."""
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('legacy_assert_shared', HERE.parent / 'elements-tap-getters/check.py')
shared = importlib.util.module_from_spec(sp)
sp.loader.exec_module(shared)
s = shared.s
MODULES = ['C.jet_elements_token_zero_init', 'C.jet_elements_token_select', 'C.jet_local_alloc_effect', 'C.jet_elements_token_amount_exec', 'C.jet_elements_token_amount_jets', 'C.jet_elements_token_amount_literal']
ROOTS = MODULES
NEW_SOURCES = [m.replace('.', '/') + '.v' for m in MODULES]
ENDPOINTS = [m + '.elements_' + prefix + 'issuance_token_amount' + suffix + '_local_spec'
             for m, suffix in [(MODULES[4], ''), (MODULES[5], '_literal')] for prefix in ['', 'current_']]
BASE_RECEIPT = HERE.parent / 'elements-token-amount-complete/EVIDENCE-REVIEW.json'


def tree(work):
    prior = json.loads(BASE_RECEIPT.read_text())
    base = Path(prior['review']['candidate'])
    if work == base or work == s.REPO or s.REPO in work.parents:
        raise ValueError('use a distinct external proof tree')
    if s.inputs.fingerprint(base / 'Coq', base) != prior['candidate_input_sha256']:
        raise ValueError('completed legacy getter source changed')
    inherited = shared.inventory(base / 'Coq')
    if shared.inventory(work / 'Coq') != inherited:
        raise ValueError('unexpected source/metadata inventory')
    for n in inherited:
        if (work / 'Coq' / n).read_bytes() != (base / 'Coq' / n).read_bytes():
            raise ValueError('inherited source change: ' + n)
    original = s.load('bundle_original_review', BASE_RECEIPT.parent / 'review.py')
    if original.review(base) != prior['review']:
        raise ValueError('original completed proof review differs')
    if (prior['checked_sha256'] != s.sha((BASE_RECEIPT.parent / 'CHECKED.json').read_bytes()) or
        prior['launch_sha256'] != s.sha((BASE_RECEIPT.parent / 'RUN.json').read_bytes())):
        raise ValueError('original checker/launch receipt changed')
    for n, digest in prior['tools_sha256'].items():
        if s.sha((BASE_RECEIPT.parent / n).read_bytes()) != digest:
            raise ValueError('original reviewed proof tool changed')
    for n, row in prior['commands'].items():
        if row['exit_code'] != 0 or row['log_sha256'] != s.sha((BASE_RECEIPT.parent / (n + '.log')).read_bytes()):
            raise ValueError('original source/evidence review terminal log changed')
    for n in NEW_SOURCES:
        s.safe_source((work / 'Coq' / n).read_text(), n)
    return prior, base


def main(work):
    if (HERE / 'RUN.json').exists():
        raise ValueError('checker already launched; inspect its existing handle and receipt')
    prior, base = tree(work)
    before, index = s.input_map(), s.index_hash()
    coq = work / 'Coq'
    fingerprint = s.inputs.fingerprint(coq, work)
    commands = {m: s.run(work, ['bash', 'build-jets.sh', '--coqc', '-q', m.replace('.', '/') + '.v'], m, 300) for m in ROOTS}
    results, definitions, deps = shared.reports(work, [(m, coq / n) for m, n in zip(MODULES, NEW_SOURCES)], 'token-amount', commands)
    if (len(results), len(definitions)) != (36, 31) or any(deps[n] != s.SIX for n in ENDPOINTS):
        raise ValueError('wrong declaration count or whole-C endpoint assumptions')
    record = dict(candidate=str(work), base_candidate=str(base),
        base_receipt_sha256=s.sha(BASE_RECEIPT.read_bytes()), base_input_sha256=prior['candidate_input_sha256'],
        candidate_input_sha256=fingerprint, main_inputs=before, staged_patch_sha256=index,
        modules=MODULES, fresh_modules=ROOTS, new_sources=NEW_SOURCES, results=results, definitions=definitions,
        endpoints=ENDPOINTS, closed_results=[n for n in results if not deps[n]],
        dependencies={n: sorted(ds) for n, ds in deps.items()}, commands=commands,
        source_sha256={m: s.sha((coq / (m.replace('.', '/') + '.v')).read_bytes()) for m in ROOTS},
        object_sha256={m: s.sha((coq / (m.replace('.', '/') + '.vo')).read_bytes()) for m in ROOTS},
        tools_sha256={'check.py': s.sha(Path(__file__).read_bytes())},
        canonical_source_gate_complete=False, normal_registration=False,
        coverage_added=0, recursive_kernel_check=False, full_acceptance=False)
    changes = {HERE / 'RUN.json': json.dumps(record, indent=2) + '\n'}
    for n in [*ROOTS, 'token-amount-assumptions', 'token-amount-contracts']:
        changes[HERE / (n + '.log')] = (work / (n + '.log')).read_text()
    s.changed(changes)
    print('36 results/31 definitions freshly compiled/reported; recursive kernel checking next', flush=True)
    for stem, command, timeout in [
        ('ast', ['bash', 'C/check-elements-jets-generation.sh'], 180),
        ('kernel', ['bash', 'build-jets.sh', '--coqchk', '-silent', '-o', *MODULES], 1800)]:
        print(stem, flush=True)
        commands[stem] = s.run(work, command, stem, timeout)
    s.kernel.kernel((work / 'kernel.log').read_text(), sorted((coq / 'C/jet_coqchk_axioms.expected').read_text().split()))
    tree(work)
    if s.input_map() != before or s.index_hash() != index or s.inputs.fingerprint(coq, work) != fingerprint:
        raise ValueError('main/index/private source drift')
    record.update(commands=commands, recursive_kernel_check=True)
    changes = {HERE / 'CHECKED.json': json.dumps(record, indent=2) + '\n'}
    for n in ['ast', 'kernel']:
        changes[HERE / (n + '.log')] = (work / (n + '.log')).read_text()
    s.changed(changes)
    print('Two original C token-amount jets recursively kernel-checked; source/admission review remains', flush=True)


if __name__ == '__main__':
    main(Path(sys.argv[1]).resolve())
