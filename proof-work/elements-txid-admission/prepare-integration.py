"""Read-only exact combined418 source delta over installed415.

This may run during acceptance: it never installs sources, copies objects, or
claims successful terminal acceptance. The eventual installer must separately
require real actual-main415 and combined418 acceptance receipts.
"""
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent


def load(name, path):
    sp = importlib.util.spec_from_file_location(name, path)
    m = importlib.util.module_from_spec(sp)
    sp.loader.exec_module(m)
    return m


a = load('combined418_plan_accept', HERE / 'accept.py')
s = a.s


def input_map(repo):
    result = {}
    for label, suffixes in [('Coq', {'.v', '.c', '.sh', '.py', '.txt', '.tsv', '.expected'}),
                             ('C', {'.c', '.h', '.inc', '.S', '.s'}), ('Haskell', {'.hs'})]:
        root = repo / label
        for p in sorted(root.rglob('*')):
            if p.is_file() and '__pycache__' not in p.parts and (
                p.suffix in suffixes or p.name.startswith('_CoqProject') or p.name == 'clightgen-linux.ini.in'
            ):
                result[label + '/' + str(p.relative_to(root))] = s.sha(p.read_bytes())
    return result


def plan(work):
    before, index = s.input_map(), s.index_hash()
    post = a.baseline()
    chain = a.review_chain(work)
    configs = [load('combined418_plan_' + prefix, HERE.parent / folder / 'admission.py')
               for folder, _, prefix in a.BATCHES]
    paths = configs[0].METADATA + configs[0].SCRIPTS
    guards, sources = [], []
    for config in configs:
        if config.METADATA + config.SCRIPTS != paths:
            raise ValueError('batch metadata/script scopes differ')
        guards += config.GUARDS
        sources += config.NEW_SOURCES
    targets = paths + guards + sources
    if (len(targets), len(set(targets)), len(guards), len(sources)) != (22, 22, 4, 7):
        raise ValueError('wrong aggregate additive target inventory')
    main = a.g.MAIN
    for n in targets:
        p = Path(n)
        if p.is_absolute() or '..' in p.parts or p.suffix in {'.vo', '.vos', '.vok', '.glob'}:
            raise ValueError('escaping or non-source target')
        if main.resolve() not in (main / n).resolve().parents:
            raise ValueError('target escapes main checkout')
    if any((main / n).exists() for n in guards + sources):
        raise ValueError('additive source would overwrite an existing main file')
    baseline = json.loads((a.BASELINE / 'INSTALLATION.json').read_text())
    expected = dict(before)
    after_hashes = {'Coq/' + n: s.sha((work / 'Coq' / n).read_bytes()) for n in targets}
    expected.update(after_hashes)
    if input_map(work) != expected or input_map(s.REPO) != before:
        raise ValueError('candidate changes unrelated semantic source or inventory')
    old_tree = Path(baseline['candidate'])
    delta = post.source_delta(main, work / 'Coq', targets)
    if delta != post.source_delta(old_tree / 'Coq', work / 'Coq', targets):
        raise ValueError('delta does not start from the accepted415 source')
    if s.input_map() != before or s.index_hash() != index:
        raise ValueError('read-only planning changed main/index')
    return dict(candidate=str(work), baseline_candidate=str(old_tree), targets=targets,
        before_sha256={'Coq/' + n: before.get('Coq/' + n) for n in targets}, after_sha256=after_hashes,
        source_only_delta_sha256=s.sha(delta.encode()), review_chain_sha256=chain,
        baseline_input_sha256=s.inputs.fingerprint(main, s.REPO),
        candidate_input_sha256=s.inputs.fingerprint(work / 'Coq', work),
        staged_patch_sha256=index, coverage_before='415/533', coverage_candidate='418/533',
        coverage_added=3, source_only_targets=22, inherited_proof_overwrites=0,
        compiler_objects_copied=0, main_inputs_unchanged=True, original_staging_preserved=True,
        actual_main415_acceptance_required_before_install=True,
        combined418_acceptance_required_before_install=True,
        main_installation=False, full_acceptance=False,
        tools_sha256={n: s.sha((HERE / n).read_bytes()) for n in ['accept.py', 'prepare-integration.py']})


if __name__ == '__main__':
    if (HERE / 'INSTALLATION-PLAN.json').exists():
        raise ValueError('plan already recorded; recheck it without overwriting historical evidence')
    result = plan(Path(sys.argv[1]).resolve())
    s.changed({HERE / 'INSTALLATION-PLAN.json': json.dumps(result, indent=2) + '\n'})
    print(json.dumps({k: v for k, v in result.items() if k not in ['before_sha256', 'after_sha256']}, indent=2))
