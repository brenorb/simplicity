"""Fresh isolated original-C lbtc_asset proof, without registry changes."""
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('lbtc_shared_checker', HERE.parent / 'elements-tap-getters/check.py')
shared = importlib.util.module_from_spec(sp)
sp.loader.exec_module(shared)
s = shared.s
MODULES = ['C.jet_u32_local_init', 'C.jet_elements_lbtc_asset_exec', 'C.jet_elements_lbtc_asset_local']
NEW = [m.replace('.', '/') + '.v' for m in MODULES]
PURE = [MODULES[-1] + '.' + n for n in
        ['lbtc_asset_spec_parametric', 'byte_unsigned_list_inj', 'lbtc_asset_review_le_bytes', 'lbtc_asset_spec_cells']]
ENDPOINT = MODULES[-1] + '.elements_lbtc_asset_local_spec'


def tree(work):
    base_path = HERE.parent / 'elements-tap-getters-admission/REVIEW.json'
    base_review = json.loads(base_path.read_text())
    base, coq = Path(base_review['review']['candidate']), work / 'Coq'
    if work == base or work == s.REPO or s.REPO in work.parents:
        raise ValueError('use a distinct private proof tree')
    if s.inputs.fingerprint(base / 'Coq', base) != base_review['candidate_input_sha256']:
        raise ValueError('completed normal proof seed changed')
    inherited = shared.inventory(base / 'Coq')
    if shared.inventory(coq) != inherited | set(NEW):
        raise ValueError('unexpected source/metadata inventory')
    for n in inherited:
        if (coq / n).read_bytes() != (base / 'Coq' / n).read_bytes():
            raise ValueError('inherited source/metadata/guard changed: ' + n)
    for n in NEW:
        if (coq / n).read_bytes() != (HERE / 'source' / (Path(n).name + '.source')).read_bytes():
            raise ValueError('private/archived proof differs')
    return base_path, base_review, inherited


def main(work):
    if (HERE / 'PREPARATION.json').exists():
        raise ValueError('proof check already recorded; review it instead of overwriting evidence')
    base_path, baseline, inherited = tree(work)
    before, index = s.input_map(), s.index_hash()
    coq = work / 'Coq'
    fingerprint = s.inputs.fingerprint(coq, work)
    commands = {}
    for m in MODULES:
        commands[m] = s.run(work, ['bash', 'build-jets.sh', '--coqc', '-q', m.replace('.', '/') + '.v'], m, 180)
        print('fresh ' + m, flush=True)
    results, definitions, deps = shared.reports(work,
        [(m, coq / (m.replace('.', '/') + '.v')) for m in MODULES], 'lbtc', commands)
    if (len(results), len(definitions)) != (13, 12) or any(deps[n] for n in PURE) or deps[ENDPOINT] != s.SIX:
        raise ValueError('unexpected result/definition/closedness/endpoint assumptions')
    for stem, command, timeout in [
        ('source', [sys.executable, '-B', str(HERE / 'check-source.py'), str(work)], 180),
        ('source-negative', [sys.executable, '-B', str(HERE / 'test-source.py'), str(work)], 180),
        ('ast', ['bash', 'C/check-elements-jets-generation.sh'], 180),
        ('kernel', ['bash', 'build-jets.sh', '--coqchk', '-silent', '-o', *MODULES], 1800)]:
        print(stem, flush=True)
        commands[stem] = s.run(work, command, stem, timeout)
    s.kernel.kernel((work / 'kernel.log').read_text(), sorted((coq / 'C/jet_coqchk_axioms.expected').read_text().split()))
    tree(work)
    if s.input_map() != before or s.index_hash() != index or s.inputs.fingerprint(coq, work) != fingerprint:
        raise ValueError('main/index/private source drift')
    record = dict(candidate=str(work), base_candidate=baseline['review']['candidate'],
        base_review_sha256=s.sha(base_path.read_bytes()), base_input_sha256=baseline['candidate_input_sha256'],
        candidate_input_sha256=fingerprint, main_inputs=before, staged_patch_sha256=index,
        new_sources=NEW, fresh_modules=MODULES, results=results, definitions=definitions,
        endpoint=ENDPOINT, closed_shared_lemmas=PURE, dependencies={n: sorted(ds) for n, ds in deps.items()},
        source_sha256={m: s.sha((coq / (m.replace('.', '/') + '.v')).read_bytes()) for m in MODULES},
        object_sha256={m: s.sha((coq / (m.replace('.', '/') + '.vo')).read_bytes()) for m in MODULES},
        commands=commands, tools_sha256={n: s.sha((HERE / n).read_bytes()) for n in ['check.py', 'check-source.py', 'test-source.py']},
        normal_registration=False, coverage_added=0, full_acceptance=False)
    changes = {HERE / 'PREPARATION.json': json.dumps(record, indent=2) + '\n'}
    for n in ['lbtc-assumptions', 'lbtc-contracts', 'source', 'source-negative', 'ast', 'kernel']:
        changes[HERE / (n + '.log')] = (work / (n + '.log')).read_text()
    s.changed(changes)
    print('Original C lbtc_asset complete call checked; no registry entry or coverage added', flush=True)


if __name__ == '__main__':
    main(Path(sys.argv[1]).resolve())
