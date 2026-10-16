"""Read-only combined420 source plan over actual accepted418; never installs.

Completed normal reviews are required for planning. Full combined acceptance
and an exact plan recheck remain required before any later installation.
"""
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('combined420_plan_accept', HERE / 'accept.py')
a = importlib.util.module_from_spec(sp)
sp.loader.exec_module(a)
g, s = a.g, a.s
prior = g.load('combined420_prior_source_delta', a.BASELINE / 'integration.py')
input_map = g.load('combined420_semantic_input_map', a.BASELINE / 'prepare-integration.py').input_map


def targets():
    if g.METADATA + g.SCRIPTS != g.parent.METADATA + g.parent.SCRIPTS:
        raise ValueError('batch metadata/script scopes differ')
    guards = g.parent.GUARDS + g.GUARDS
    sources = g.parent.NEW_SOURCES + g.NEW_SOURCES
    result = g.METADATA + g.SCRIPTS + guards + sources
    if (len(result), len(set(result)), len(guards), len(sources), len(g.REUSED_SOURCES)) != (66, 66, 5, 50, 2):
        raise ValueError('wrong combined420 additive target inventory')
    for n in result:
        p = Path(n)
        if (p.is_absolute() or '..' in p.parts or p.suffix in {'.vo', '.vos', '.vok', '.glob'} or
            g.MAIN.resolve() not in (g.MAIN / n).resolve().parents):
            raise ValueError('escaping or non-source integration target')
    return result


def plan(work):
    if work == s.REPO or s.REPO in work.parents or (work / 'Coq').is_symlink():
        raise ValueError('use a distinct private combined candidate')
    selected = targets()
    if not (HERE / 'REVIEW.json').is_file():
        raise ValueError('completed normal420 review required before planning')
    before, index = s.input_map(), s.index_hash()
    actual = a.baseline()
    chain = a.reviewed(work)
    guards = g.parent.GUARDS + g.GUARDS
    sources = g.parent.NEW_SOURCES + g.NEW_SOURCES
    for n in guards + sources:
        if (g.MAIN / n).exists() or (g.MAIN / n).is_symlink():
            raise ValueError('would overwrite an inherited/untracked source')
    for n in selected:
        p = work / 'Coq' / n
        if not p.is_file() or p.is_symlink():
            raise ValueError('missing/shared source integration target')
    for n in g.REUSED_SOURCES:
        if (g.MAIN / n).read_bytes() != (work / 'Coq' / n).read_bytes():
            raise ValueError('reused source differs from main')
    after = {'Coq/' + n: s.sha((work / 'Coq' / n).read_bytes()) for n in selected}
    expected = dict(before)
    expected.update(after)
    if input_map(work) != expected:
        raise ValueError('candidate changes unrelated semantic source or inventory')
    baseline_tree = Path(json.loads((a.BASELINE / 'INSTALLATION.json').read_text())['candidate'])
    delta = prior.source_delta(g.MAIN, work / 'Coq', selected)
    if delta != prior.source_delta(baseline_tree / 'Coq', work / 'Coq', selected):
        raise ValueError('delta does not start at actual accepted418')
    if s.input_map() != before or s.index_hash() != index:
        raise ValueError('read-only planning changed main/index')
    return dict(candidate=str(work), baseline_candidate=str(baseline_tree), targets=selected,
        before_sha256={'Coq/' + n: before.get('Coq/' + n) for n in selected}, after_sha256=after,
        source_only_delta_sha256=s.sha(delta.encode()), review_chain_sha256=chain,
        baseline_input_sha256=s.inputs.fingerprint(g.MAIN, s.REPO),
        candidate_input_sha256=s.inputs.fingerprint(work / 'Coq', work), staged_patch_sha256=index,
        baseline_main_acceptance_sha256=actual['main_acceptance_sha256'],
        baseline_installation_sha256=actual['installation_sha256'],
        coverage_before='418/533', coverage_candidate='420/533', coverage_added=2,
        source_only_targets=66, byte_identical_reused_sources=g.REUSED_SOURCES,
        inherited_proof_overwrites=0, compiler_objects_copied=0,
        actual_main418_acceptance_required_before_install=True,
        full_combined420_acceptance_required_before_install=True,
        predecessor419_terminal_required=False, main_installation=False, full_acceptance=False,
        tools_sha256={n: s.sha((HERE / n).read_bytes()) for n in ['accept.py', 'prepare-integration.py']})


if __name__ == '__main__':
    if len(sys.argv) != 3 or sys.argv[1] not in ['check', 'record']:
        raise ValueError('usage: prepare-integration.py check|record PRIVATE_TREE')
    work = Path(sys.argv[2]).resolve()
    if sys.argv[1] == 'record' and (HERE / 'INSTALLATION-PLAN.json').exists():
        raise ValueError('plan already recorded; recheck instead')
    result = plan(work)
    if sys.argv[1] == 'record':
        g.write(HERE / 'INSTALLATION-PLAN.json', result)
    print(json.dumps({n: value for n, value in result.items() if n not in ['before_sha256', 'after_sha256']}, indent=2))
