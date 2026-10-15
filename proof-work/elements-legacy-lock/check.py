"""Scoped actual-C legacy getter verification; no normal admission claim."""
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('legacy_shared_check', HERE.parent / 'elements-tap-getters/check.py')
shared = importlib.util.module_from_spec(sp)
sp.loader.exec_module(shared)
s = shared.s
MODULES = ['C.jet_forWhile_fold', 'C.jet_elements_legacy_lock_spec',
           'C.jet_elements_legacy_lock_exec', 'C.jet_elements_legacy_lock_local']
NEW = [m.replace('.', '/') + '.v' for m in MODULES]
ENDPOINTS = [MODULES[-1] + '.' + n for n in
             ['elements_broken_tx_lock_distance_local_spec', 'elements_broken_tx_lock_duration_local_spec']]
BASE_RECEIPT = HERE.parent / 'elements-lbtc-asset-admission/REVIEW.json'


def tree(work):
    prior = json.loads(BASE_RECEIPT.read_text())
    base = Path(prior['review']['candidate'])
    if work == base or work == s.REPO or s.REPO in work.parents:
        raise ValueError('use a distinct external proof tree')
    if s.inputs.fingerprint(base / 'Coq', base) != prior['candidate_input_sha256']:
        raise ValueError('completed source seed changed')
    inherited = shared.inventory(base / 'Coq')
    if shared.inventory(work / 'Coq') != inherited | set(NEW):
        raise ValueError('unexpected private source/metadata inventory')
    for n in inherited:
        if (work / 'Coq' / n).read_bytes() != (base / 'Coq' / n).read_bytes():
            raise ValueError('inherited source changed: ' + n)
    for n in NEW:
        if (work / 'Coq' / n).read_bytes() != (HERE / 'source' / (Path(n).name + '.source')).read_bytes():
            raise ValueError('private proof/archive mismatch: ' + n)
    return prior, base


def main(work):
    if (HERE / 'RUN.json').exists():
        raise ValueError('checker already launched; inspect its existing handle/receipt')
    prior, base = tree(work)
    before, index = s.input_map(), s.index_hash()
    coq = work / 'Coq'
    fingerprint = s.inputs.fingerprint(coq, work)
    commands = {}
    for m in MODULES:
        commands[m] = s.run(work, ['bash', 'build-jets.sh', '--coqc', '-q', m.replace('.', '/') + '.v'], m, 180)
        print('fresh ' + m, flush=True)
    results, definitions, deps = shared.reports(work,
        [(m, coq / (m.replace('.', '/') + '.v')) for m in MODULES], 'legacy', commands)
    if any(deps[n] != s.SIX for n in ENDPOINTS):
        raise ValueError('whole-C endpoint assumption set differs')
    pure = [n for n, ds in deps.items() if not ds]
    if any(deps['C.jet_forWhile_fold.' + n] for n in ['fold_left_firstn_next', 'for_while_run_fold_list']):
        raise ValueError('generic fold acquired assumptions')
    record = dict(candidate=str(work), base_candidate=str(base),
        base_receipt_sha256=s.sha(BASE_RECEIPT.read_bytes()), base_input_sha256=prior['candidate_input_sha256'],
        candidate_input_sha256=fingerprint, main_inputs=before, staged_patch_sha256=index,
        modules=MODULES, new_sources=NEW, results=results, definitions=definitions,
        endpoints=ENDPOINTS, closed_results=pure, dependencies={n: sorted(ds) for n, ds in deps.items()},
        commands=commands, tools_sha256={'check.py': s.sha(Path(__file__).read_bytes())},
        source_sha256={m: s.sha((coq / (m.replace('.', '/') + '.v')).read_bytes()) for m in MODULES},
        object_sha256={m: s.sha((coq / (m.replace('.', '/') + '.vo')).read_bytes()) for m in MODULES},
        canonical_source_gate_complete=False, normal_registration=False, coverage_added=0,
        recursive_kernel_check=False, full_acceptance=False)
    changes = {HERE / 'RUN.json': json.dumps(record, indent=2) + '\n'}
    for n in list(MODULES) + ['legacy-assumptions', 'legacy-contracts']:
        changes[HERE / (n + '.log')] = (work / (n + '.log')).read_text()
    s.changed(changes)
    print(str(len(results)) + ' results, ' + str(len(definitions)) + ' definitions; recursive kernel checking next', flush=True)
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
    print('Two whole C legacy getters kernel-checked; canonical source gate and admission remain required', flush=True)


if __name__ == '__main__':
    main(Path(sys.argv[1]).resolve())
