"""Read-only source-only normal436 installation proposal; never installs.

Planning requires completed independent normal review. Real full436 acceptance
and successful actual-main420 acceptance are both later write prerequisites.
"""
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('raw436_source_plan', HERE / 'accept.py')
a = importlib.util.module_from_spec(sp)
sp.loader.exec_module(a)
g, s = a.g, a.s


def targets():
    names = g.METADATA + g.SCRIPTS + g.NEW_SOURCES + g.GUARDS
    if len(names) != 20 or len(set(names)) != 20:
        raise ValueError('wrong normal436 source-only integration scope')
    for name in names:
        p = Path(name)
        target = g.MAIN / p
        if (p.is_absolute() or '..' in p.parts or p.suffix in {'.vo', '.vos', '.vok', '.glob'} or
            g.MAIN.resolve() not in target.resolve().parents):
            raise ValueError('escaping or non-source normal436 integration target')
    return names


def plan(work):
    if work == s.REPO or s.REPO in work.parents or (work / 'Coq').is_symlink():
        raise ValueError('use the distinct private reviewed436 candidate')
    reviewed = a.reviewed(work)
    g.boundaries()
    selected = targets()
    before, index = s.input_map(), s.index_hash()
    for name in g.NEW_SOURCES + g.GUARDS:
        if (g.MAIN / name).exists() or (g.MAIN / name).is_symlink():
            raise ValueError('would overwrite inherited or untracked proof/guard source')
    for name in selected:
        p = work / 'Coq' / name
        if not p.is_file() or p.is_symlink():
            raise ValueError('missing or shared normal436 source target')
    after = {'Coq/' + name: s.sha((work / 'Coq' / name).read_bytes()) for name in selected}
    expected = dict(before)
    expected.update(after)
    if g.parent.planner.input_map(work) != expected or before != g.baseline_inputs():
        raise ValueError('candidate changes unrelated source or inventory')
    delta = g.parent.source_delta(g.MAIN, work / 'Coq', selected)
    if delta != g.parent.source_delta(g.BASE, work / 'Coq', selected):
        raise ValueError('normal436 delta does not start at checked420')
    if s.input_map() != before or s.index_hash() != index:
        raise ValueError('read-only normal436 planning changed main/index')
    return dict(candidate=str(work), baseline_candidate=str(g.BASE_TREE), targets=selected,
        before_sha256={'Coq/' + name: before.get('Coq/' + name) for name in selected},
        after_sha256=after, source_only_delta_sha256=s.sha(delta.encode()),
        baseline_input_sha256=g.main_fingerprint(before),
        candidate_input_sha256=reviewed['candidate_input_sha256'], staged_patch_sha256=index,
        review_sha256=s.sha((HERE / 'REVIEW.json').read_bytes()),
        predecessor_isolated_acceptance_sha256=s.sha((g.PRED / 'ACCEPTANCE.json').read_bytes()),
        coverage_before='420/533', coverage_candidate='436/533', coverage_added=16,
        source_only_targets=20, added_proof_sources=3, added_guard_inputs=6,
        inherited_proof_overwrites=0, compiler_objects_copied=0,
        actual_main420_acceptance_required_before_install=True,
        full_isolated436_acceptance_required_before_install=True,
        stopped_controllers_required_before_install=True,
        main_installation=False, full_acceptance=False,
        tools_sha256={n: s.sha((HERE / n).read_bytes()) for n in ['accept.py', 'prepare-integration.py']})


if __name__ == '__main__':
    if len(sys.argv) != 3 or sys.argv[1] not in ['check', 'record']:
        raise ValueError('usage: prepare-integration.py check|record PRIVATE_TREE')
    if sys.argv[1] == 'record' and (HERE / 'INSTALLATION-PLAN.json').exists():
        raise ValueError('normal436 plan already recorded; recheck instead')
    result = plan(Path(sys.argv[2]).resolve())
    if sys.argv[1] == 'record':
        g.write(HERE / 'INSTALLATION-PLAN.json', result)
    print(json.dumps({n: value for n, value in result.items() if n not in ['before_sha256', 'after_sha256']}, indent=2))
