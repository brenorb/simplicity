"""Review and optionally import the independently checked SHA startup batch.

Run install only after main's in-flight acceptance has terminated. This is a
supporting-proof import, not a normal coverage/registry replacement.
"""
import argparse
import json
from pathlib import Path
import re
import subprocess
import sys
import importlib.util

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('startup_review_stage', HERE / 'stage.py')
stage = importlib.util.module_from_spec(spec); spec.loader.exec_module(stage)
normal = stage.load('startup_review_deps', HERE.parent / 'scalar-multiply-integration/review-normal.py')
kernel = stage.load('startup_review_kernel', HERE.parent / 'scalar-mul/review.py')


def review(candidate):
    meta = json.loads((candidate / 'ASSEMBLY.json').read_text())
    receipt = json.loads((candidate / 'REVIEW.json').read_text())
    if (not meta['namespace_only_transport'] or not meta['main_inputs_untouched']
            or Path(meta['candidate']).resolve() != candidate.resolve() or meta['shared_commit'] != stage.COMMIT
            or receipt['candidate'] != str(candidate) or receipt['source_commit'] != stage.COMMIT
            or receipt['new_modules'] != 13 or receipt['results'] != 146
            or receipt['normal_registry_admission'] or receipt['coverage_added']):
        raise ValueError('startup batch identity/scope drift')
    for field, stem in [('assumption_check', 'assumptions'), ('contract_check', 'contracts'), ('kernel_check', 'kernel')]:
        if receipt[field]['exit_code'] or receipt[field]['output_sha256'] != stage.patch.sha((candidate / (stem + '.out')).read_bytes()):
            raise ValueError('nonterminal/changed startup evidence')
        if (candidate / (stem + '.err')).read_bytes(): raise ValueError('startup diagnostics')
    if set(receipt['builds']) != set(meta['compile_order']): raise ValueError('compile inventory drift')
    for name, evidence in receipt['builds'].items():
        if (evidence['exit_code'] or evidence['output_sha256'] != stage.patch.sha((candidate / ('compile-' + name + '.out')).read_bytes())
                or (candidate / ('compile-' + name + '.err')).read_bytes()):
            raise ValueError('fresh compile evidence drift')
    changes = {}
    results = []
    definitions = []
    for entry in meta['modules']:
        name = entry['name']
        if name in ['jet_clight_forward', 'jet_sha_initial_globals']:
            original = (stage.REPO / 'proof-work/sha-support' / (name + '.v.source')).read_text()
        else:
            if name not in stage.NAMES: raise ValueError('unreviewed startup module')
            original = subprocess.check_output(['git', 'show', stage.COMMIT + ':Coq/startup/proofs/' + name + '.v'], cwd=stage.REPO).decode()
        transported = original.replace('JetStartupReview.', 'C.').replace('JetStartup.', 'C.')
        if stage.patch.sha(original.encode()) != entry['source_sha256'] or stage.patch.sha(transported.encode()) != entry['sha256']:
            raise ValueError('non-namespace source change')
        if (candidate / entry['path']).read_text() != transported or not (candidate / entry['path']).with_suffix('.vo').is_file():
            raise ValueError('checked source/object missing or changed')
        code = stage.scanner.code_only(transported)
        if re.search(r'\b(?:admit|Admitted|Axiom|Parameter|Conjecture|vm_cast_no_check|native_cast_no_check)\b', code):
            raise ValueError('proof bypass')
        actual = re.findall(r'^(?:Theorem|Lemma|Corollary)\s+(\w+)', code, re.M)
        if actual != entry['results']: raise ValueError('source result inventory drift')
        results += ['C.' + name + '.' + n for n in actual]
        definitions += ['C.' + name + '.' + n for n in re.findall(r'^(?:Definition|Fixpoint|Inductive)\s+(\w+)', code, re.M)]
        target = stage.REPO / entry['path']
        if target.exists() and target.read_text() != transported: raise ValueError('main source collision')
        changes[target] = transported
    if len(changes) != 13 or len(results) != 146: raise ValueError('duplicate/incomplete startup sources')
    for path, value in meta['inherited_sha256'].items():
        if stage.patch.sha((stage.REPO / path).read_bytes()) != value or stage.patch.sha((candidate / path).read_bytes()) != value:
            raise ValueError('inherited/main startup dependency drift')
    deps = normal.assumptions((candidate / 'assumptions.out').read_text())
    if {n: sorted(ds) for n, ds in deps.items()} != receipt['assumptions'] or set(deps) != set(results):
        raise ValueError('startup dependency inventory drift')
    text = (candidate / 'contracts.out').read_text()
    if '...' in text or re.findall(r'(?m)^SHA_STARTUP_(TYPE|DEF) (\S+)$', text) != [('TYPE', n) for n in results] + [('DEF', n) for n in definitions]:
        raise ValueError('incomplete/truncated startup deep records')
    kernel.kernel((candidate / 'kernel.out').read_text(),
                  sorted((stage.REPO / 'Coq/C/jet_coqchk_axioms.expected').read_text().split()))
    return {'candidate': str(candidate), 'modules': 13, 'results': 146, 'definitions': len(definitions),
            'closed_results': sum(not ds for ds in deps.values()), 'namespace_only_change': True,
            'fresh_kernel_exit_code': 0, 'source_commit': stage.COMMIT, 'coverage_added': 0,
            'normal_registry_admission': False, 'main_installation': False}, changes


def install(candidate):
    result, changes = review(candidate)
    # Import no accepted metadata and no existing proof. Existing staging stays
    # byte-identical, as does every inherited source checked above.
    before = stage.patch.sha(subprocess.check_output(['git', 'diff', '--cached', '--binary'], cwd=stage.REPO))
    stage.patch.patch_files({p: text for p, text in changes.items() if not p.exists()})
    if stage.patch.sha(subprocess.check_output(['git', 'diff', '--cached', '--binary'], cwd=stage.REPO)) != before:
        raise ValueError('startup import changed the existing index')
    for p, text in changes.items():
        if p.read_text() != text: raise ValueError('startup import drift')
    result.update(main_installation=True, preexisting_staged_patch_sha256=before)
    return result


if __name__ == '__main__':
    cli = argparse.ArgumentParser(); cli.add_argument('--candidate', type=Path, required=True)
    cli.add_argument('--install', action='store_true'); args = cli.parse_args()
    candidate = args.candidate.resolve()
    print(json.dumps(install(candidate) if args.install else review(candidate)[0], indent=2))
