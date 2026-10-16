"""Check the token helper's actual pointer selection and amount call, not a whole jet."""
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('token_zero_shared_checker', HERE.parent / 'elements-tap-getters/check.py')
shared = importlib.util.module_from_spec(sp)
sp.loader.exec_module(shared)
s = shared.s
MODULE = 'C.jet_elements_token_select'
NEW = 'C/jet_elements_token_select.v'
BASE_RECEIPT = HERE.parent / 'elements-token-amount/ZERO-INIT-REVIEW.json'


def tree(work):
    r = json.loads(BASE_RECEIPT.read_text())
    base = Path(r['review']['candidate'])
    if work == base or work == s.REPO or s.REPO in work.parents:
        raise ValueError('use a distinct external tree')
    if s.inputs.fingerprint(base / 'Coq', base) != r['candidate_input_sha256']:
        raise ValueError('checked predecessor source changed')
    inventory = shared.inventory(base / 'Coq')
    if shared.inventory(work / 'Coq') != inventory | {NEW}:
        raise ValueError('wrong new source inventory')
    for n in inventory:
        if (work / 'Coq' / n).read_bytes() != (base / 'Coq' / n).read_bytes():
            raise ValueError('inherited source changed: ' + n)
    source = work / 'Coq' / NEW
    if source.read_bytes() != (HERE / 'source/jet_elements_token_select.v.source').read_bytes():
        raise ValueError('archive/private source mismatch')
    s.safe_source(source.read_text(), NEW)
    return r


def main(work):
    if (HERE / 'SELECT-RUN.json').exists():
        raise ValueError('checker already launched; inspect its handle or terminal receipt')
    base = tree(work)
    before, index = s.input_map(), s.index_hash()
    fp = s.inputs.fingerprint(work / 'Coq', work)
    commands = {'fresh': s.run(work, ['bash', 'build-jets.sh', '--coqc', '-q', NEW], 'fresh', 120)}
    results, definitions, deps = shared.reports(work, [(MODULE, work / 'Coq' / NEW)], 'token-select', commands)
    if (len(results), len(definitions)) != (7, 11) or any(not ds <= s.SIX for ds in deps.values()):
        raise ValueError('wrong helper declaration/dependency inventory')
    r = dict(candidate=str(work), base_receipt_sha256=s.sha(BASE_RECEIPT.read_bytes()),
        base_input_sha256=base['candidate_input_sha256'], candidate_input_sha256=fp,
        main_inputs=before, staged_patch_sha256=index, module=MODULE, results=results, definitions=definitions,
        source_sha256=s.sha((work / 'Coq' / NEW).read_bytes()),
        object_sha256=s.sha((work / 'Coq' / NEW).with_suffix('.vo').read_bytes()),
        dependencies={n: sorted(ds) for n, ds in deps.items()}, commands=commands,
        checker_sha256=s.sha(Path(__file__).read_bytes()), recursive_kernel_check=False,
        whole_jet_equivalence=False, coverage_added=0, full_acceptance=False)
    s.changed({HERE / 'SELECT-RUN.json': json.dumps(r, indent=2) + '\n'})
    print('Seven actual token-selection/amount-call results compiled/reported; AST and kernel next', flush=True)
    for n, cmd, timeout in [
        ('ast', ['bash', 'C/check-elements-jets-generation.sh'], 180),
        ('kernel', ['bash', 'build-jets.sh', '--coqchk', '-silent', '-o', MODULE], 1800)]:
        commands[n] = s.run(work, cmd, n, timeout)
    s.kernel.kernel((work / 'kernel.log').read_text(), sorted((work / 'Coq/C/jet_coqchk_axioms.expected').read_text().split()))
    tree(work)
    if before != s.input_map() or index != s.index_hash() or fp != s.inputs.fingerprint(work / 'Coq', work):
        raise ValueError('main/index/private inputs changed')
    r.update(recursive_kernel_check=True, commands=commands)
    changes = {HERE / 'SELECT-CHECKED.json': json.dumps(r, indent=2) + '\n'}
    changes.update({HERE / (n + '.log'): (work / (n + '.log')).read_text() for n in commands})
    s.changed(changes)
    print('Actual token armed branch kernel-checked; allocation/tag boundary and callers remain', flush=True)


if __name__ == '__main__':
    main(Path(sys.argv[1]).resolve())
