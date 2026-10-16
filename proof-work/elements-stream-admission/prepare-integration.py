"""Read-only exact source-only plan from accepted main420 to reviewed443.

Does not install or infer a pending audit's result. Both predecessor full
terminals, full443 success and stopped baseline controllers are write gates.
"""
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('normal443_combined_source_plan', HERE / 'accept.py')
a = importlib.util.module_from_spec(sp)
sp.loader.exec_module(a)
g, s = a.g, a.s


def targets():
    names = g.METADATA + g.SCRIPTS + g.parent.NEW_SOURCES + g.NEW_SOURCES + g.parent.GUARDS + g.GUARDS
    if len(names) != 25 or len(set(names)) != 25:
        raise ValueError('wrong exact combined443 source-only target scope')
    for name in names:
        p = Path(name)
        target = g.MAIN / p
        if (p.is_absolute() or '..' in p.parts or p.suffix in {'.vo', '.vos', '.vok', '.glob'} or
            g.MAIN.resolve() not in target.resolve().parents):
            raise ValueError('escaping or non-source combined443 integration target')
    return names


def plan(work):
    if work == s.REPO or s.REPO in work.parents:
        raise ValueError('use the distinct private reviewed443 candidate')
    expected_work = Path(a.old.read(HERE / 'ASSEMBLY.json')['candidate'])
    if work != expected_work or (work / 'Coq').is_symlink():
        raise ValueError('wrong reviewed443 private candidate')
    reviewed = a.reviewed(work)
    g.boundaries()
    selected = targets()
    before, index = s.input_map(), s.index_hash()
    fresh = g.parent.NEW_SOURCES + g.NEW_SOURCES + g.parent.GUARDS + g.GUARDS
    for name in fresh:
        if (g.MAIN / name).exists() or (g.MAIN / name).is_symlink():
            raise ValueError('would overwrite an inherited or untracked source')
    for name in selected:
        p = work / 'Coq' / name
        if not p.is_file() or p.is_symlink():
            raise ValueError('missing or shared source-only integration target')
    after = {'Coq/' + n: s.sha((work / 'Coq' / n).read_bytes()) for n in selected}
    expected = dict(before)
    expected.update(after)
    base = g.parent.BASE_TREE
    if (before != g.parent.baseline_inputs() or
        a.old.planner.input_map(work) != expected or a.old.planner.input_map(base) != before):
        raise ValueError('candidate changes unrelated source/inventory or baseline is not accepted420')
    delta = a.old.source_delta(g.MAIN, work / 'Coq', selected)
    if delta != a.old.source_delta(base / 'Coq', work / 'Coq', selected):
        raise ValueError('combined443 delta does not start at exact checked420')
    if s.input_map() != before or s.index_hash() != index:
        raise ValueError('read-only combined443 planning changed main/index')
    return dict(candidate=str(work), baseline_candidate=str(base), targets=selected,
        before_sha256={'Coq/' + n: before.get('Coq/' + n) for n in selected}, after_sha256=after,
        source_only_delta_sha256=s.sha(delta.encode()), baseline_input_sha256=g.main_fingerprint(before),
        candidate_input_sha256=reviewed['candidate_input_sha256'], staged_patch_sha256=index,
        review_chain_sha256={str(folder.name): s.sha((folder / 'REVIEW.json').read_bytes())
                             for folder in [g.PRED, HERE]},
        actual_main420_acceptance_sha256=s.sha((g.parent.PRED / 'MAIN-ACCEPTANCE.json').read_bytes()),
        coverage_before='420/533', coverage_candidate='443/533', coverage_added=23,
        source_only_targets=25, added_proof_sources=5, added_guard_inputs=9,
        inherited_proof_overwrites=0, compiler_objects_copied=0,
        actual_main420_acceptance_required_before_install=True,
        full_isolated436_acceptance_required_before_install=True,
        full_isolated443_acceptance_required_before_install=True,
        stopped_controllers_required_before_install=True,
        main_installation=False, full_acceptance=False,
        tools_sha256={n: s.sha((HERE / n).read_bytes()) for n in ['accept.py', 'prepare-integration.py']})


if __name__ == '__main__':
    if len(sys.argv) != 3 or sys.argv[1] not in ['check', 'record']:
        raise ValueError('usage: prepare-integration.py check|record PRIVATE_TREE')
    if sys.argv[1] == 'record' and (HERE / 'INSTALLATION-PLAN.json').exists():
        raise ValueError('combined443 source plan already recorded; recheck instead')
    result = plan(Path(sys.argv[2]).resolve())
    if sys.argv[1] == 'record':
        g.write(HERE / 'INSTALLATION-PLAN.json', result)
    print(json.dumps({n: value for n, value in result.items() if n not in ['before_sha256', 'after_sha256']}, indent=2))
