"""Fresh shared local-to-BM lifting and concrete application-jet examples."""
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('application_bm_lift_support', HERE.parent / 'elements-tap-getters/check.py')
shared = importlib.util.module_from_spec(sp)
sp.loader.exec_module(shared)
s = shared.s
MODULES = ['C.jet_application_context_lift', 'C.jet_application_context_examples']
NEW_SOURCES = [m.replace('.', '/') + '.v' for m in MODULES]
BASE_RECEIPT = HERE.parent / 'elements-null-data-literal/EVIDENCE-REVIEW.json'
RESULTS = [MODULES[0] + '.application_jet_local_sep_to_bitmachine',
           MODULES[1] + '.elements_input_sequence_bitmachine_spec',
           MODULES[1] + '.bitcoin_script_cmr_bitmachine_spec']
KERNEL_COMMAND = ['bash', '-c', 'ulimit -s 65520; exec bash build-jets.sh --coqchk -silent -o ' + ' '.join(MODULES)]


def tree(work):
    prior = json.loads(BASE_RECEIPT.read_text())
    base = Path(prior['review']['candidate'])
    if work == base or work == s.REPO or s.REPO in work.parents:
        raise ValueError('use a distinct external proof tree')
    if s.inputs.fingerprint(base / 'Coq', base) != prior['candidate_input_sha256']:
        raise ValueError('completed contextual source base changed')
    inherited = shared.inventory(base / 'Coq')
    if shared.inventory(work / 'Coq') != inherited | set(NEW_SOURCES):
        raise ValueError('unexpected source/metadata inventory')
    for n in inherited:
        if (work / 'Coq' / n).read_bytes() != (base / 'Coq' / n).read_bytes():
            raise ValueError('inherited source changed: ' + n)
    for n in NEW_SOURCES:
        p = work / 'Coq' / n
        if p.read_bytes() != (HERE / 'source' / (Path(n).name + '.source')).read_bytes():
            raise ValueError('archive/private source differs')
        s.safe_source(p.read_text(), n)
    return prior, base


def main(work):
    if (HERE / 'RUN.json').exists():
        raise ValueError('checker already launched; inspect existing run')
    prior, base = tree(work)
    before, index = s.input_map(), s.index_hash()
    fp = s.inputs.fingerprint(work / 'Coq', work)
    commands = {m: s.run(work, ['bash', 'build-jets.sh', '--coqc', '-q', m.replace('.', '/') + '.v'], m, 60)
                for m in MODULES}
    results, definitions, deps = shared.reports(work,
        [(m, work / 'Coq' / n) for m, n in zip(MODULES, NEW_SOURCES)], 'application-context-lift', commands)
    if results != RESULTS or definitions or any(deps[n] != s.SIX for n in results):
        raise ValueError('wrong inventory or unexpected new assumptions')
    r = dict(candidate=str(work), base_candidate=str(base), base_receipt_sha256=s.sha(BASE_RECEIPT.read_bytes()),
        base_input_sha256=prior['candidate_input_sha256'], candidate_input_sha256=fp,
        main_inputs=before, staged_patch_sha256=index, modules=MODULES, new_sources=NEW_SOURCES,
        results=results, definitions=definitions, dependencies={n: sorted(ds) for n, ds in deps.items()},
        source_sha256={m: s.sha((work / 'Coq' / n).read_bytes()) for m, n in zip(MODULES, NEW_SOURCES)},
        object_sha256={m: s.sha((work / 'Coq' / n).with_suffix('.vo').read_bytes()) for m, n in zip(MODULES, NEW_SOURCES)},
        commands=commands, tools_sha256={'check.py': s.sha(Path(__file__).read_bytes())},
        shared_lift_proved=True, concrete_jet_examples=2, requires_nonempty_output=True,
        recursive_kernel_check=False, normal_registration=False, coverage_added=0, full_acceptance=False)
    s.changed({HERE / 'RUN.json': json.dumps(r, indent=2) + '\n',
        **{HERE / (n + '.log'): (work / (n + '.log')).read_text() for n in commands}})
    print('Three complete results freshly compiled/reported; recursive kernel check next', flush=True)
    commands['kernel'] = s.run(work, KERNEL_COMMAND, 'kernel', 1800)
    s.kernel.kernel((work / 'kernel.log').read_text(), sorted((work / 'Coq/C/jet_coqchk_axioms.expected').read_text().split()))
    tree(work)
    if s.input_map() != before or s.index_hash() != index or s.inputs.fingerprint(work / 'Coq', work) != fp:
        raise ValueError('main/index/private source drift')
    r.update(commands=commands, recursive_kernel_check=True)
    s.changed({HERE / 'CHECKED.json': json.dumps(r, indent=2) + '\n', HERE / 'kernel.log': (work / 'kernel.log').read_text()})
    print('Shared lift plus two concrete application jets recursively kernel-checked; no added coverage', flush=True)


if __name__ == '__main__':
    main(Path(sys.argv[1]).resolve())
