"""Review the transaction-builder closure without replacing main's C program.

Reuse only hash-pinned objects from the already checked environment unit;
compile every newly introduced module and kernel-check the entire closure.
Source installation uses apply_patch and never changes the normal registry.
"""
import argparse
import contextlib
import importlib.util
import io
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
REPO = HERE.parent.parent


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


BASE = HERE.parent / 'bitcoin-tapenv-integration'
old_post = load('tx_old_post', BASE / 'post-check.py')
gate = load('tx_review', BASE / 'review.py')
stage = gate.stage
stage.ROOTS = ['jet_bitcoin_env_tx_raw']
sha = stage.patch.sha
inputs = load('tx_inputs', REPO / 'Coq/jet-audit-inputs.py')
ALLOWED = {
    'ClassicalDedekindReals.sig_forall_dec',
    'ClassicalDedekindReals.sig_not_dec', 'Classical_Prop.classic',
    'FunctionalExtensionality.functional_extensionality_dep',
    'Events.external_functions_sem', 'Events.inline_assembly_sem',
}
BOUNDARIES = [
    'memcpy_model', 'readable raw structures, buffers and address bounds',
    'SHA dispatch/counter startup premises for the distinct environment unit',
    'CompCert successful malloc semantics; allocation failure not covered',
    'raw-environment projection retains tap-path length <=128',
    'raw txid bytes are copied, not calculated or validated',
    'no original-program caller-to-jet composition or new coverage',
]


def index_hash():
    return sha(subprocess.check_output(['git', 'diff', '--cached', '--binary'], cwd=REPO))


def prepare():
    old_post.check()
    prior = json.loads((BASE / 'REVIEW.json').read_text())
    prior_work = Path(prior['candidate'])
    with contextlib.redirect_stdout(io.StringIO()) as out:
        stage.stage()
    work = Path(json.loads(out.getvalue())['candidate'])
    meta = json.loads((work / 'ASSEMBLY.json').read_text())
    reused = {}
    for entry in meta['modules']:
        relative = 'Coq/C/' + entry['name'] + '.vo'
        if relative not in prior['evidence_sha256']:
            continue
        source = prior_work / relative
        target_source = work / relative.replace('.vo', '.v')
        if (sha(source.read_bytes()) != prior['evidence_sha256'][relative]
                or source.with_suffix('.v').read_bytes() != target_source.read_bytes()):
            raise ValueError('checked object/source drift: ' + relative)
        # Match checked source/object timestamps so make sees the pinned prefix.
        stamp = source.with_suffix('.v').stat()
        os.utime(target_source, ns=(stamp.st_atime_ns, stamp.st_mtime_ns))
        for suffix in ['.vo', '.vos', '.vok', '.glob']:
            artifact = source.with_suffix(suffix)
            if artifact.exists():
                shutil.copy2(artifact, target_source.with_suffix(suffix))
        reused[relative] = prior['evidence_sha256'][relative]
    meta.update(reused_checked_objects=reused,
                baseline_input_sha256=inputs.fingerprint(REPO / 'Coq', REPO),
                preexisting_staged_patch_sha256=index_hash(),
                scope='Actual mallocTransaction execution and twelve canonical raw-data cached hashes; supporting derived-program proof only.')
    stage.patch.patch_files({work / 'ASSEMBLY.json': json.dumps(meta, indent=2) + '\n'})
    print(json.dumps({'candidate': str(work), 'closure_modules': len(meta['modules']),
                      'reused_checked_objects': len(reused),
                      'new_sources': [e['origin'] for e in meta['modules']
                                      if not (REPO / e['origin']).exists()]}, indent=2))


def check(work):
    meta = json.loads((work / 'ASSEMBLY.json').read_text())
    for path, value in meta['reused_checked_objects'].items():
        if sha((work / path).read_bytes()) != value:
            raise ValueError('reused object drift')
    gate.audit.check(work)
    receipt = json.loads((work / 'REVIEW.json').read_text())
    for name, deps in receipt['expected_dependencies'].items():
        if not set(deps) <= ALLOWED:
            raise ValueError('unexpected theorem assumptions: ' + name)
    prior = json.loads((BASE / 'REVIEW.json').read_text())
    for name, deps in receipt['expected_dependencies'].items():
        if name in prior['expected_dependencies'] and deps != prior['expected_dependencies'][name]:
            raise ValueError('inherited theorem assumptions changed: ' + name)
    receipt['explicit_boundaries'] = BOUNDARIES
    receipt['evidence_sha256'] = {
        path: sha((work / path).read_bytes())
        for path in ['assumptions.v', 'contracts.v', 'assumptions.log', 'contracts.log',
                     'kernel.log', 'regenerated.v'] +
                    ['Coq/C/' + e['name'] + '.vo' for e in meta['modules'] if meta['affected'][e['name']]]
    }
    stage.patch.patch_files({work / 'REVIEW.json': json.dumps(receipt, indent=2) + '\n'})
    review(work)


def review(work):
    result, files = gate.review(work)
    meta = json.loads((work / 'ASSEMBLY.json').read_text())
    receipt = json.loads((work / 'REVIEW.json').read_text())
    if meta['roots'] != stage.ROOTS or receipt['explicit_boundaries'] != BOUNDARIES:
        raise ValueError('transaction scope drift')
    for path, value in receipt['evidence_sha256'].items():
        if sha((work / path).read_bytes()) != value:
            raise ValueError('transaction artifact drift: ' + path)
    if any(not set(ds) <= ALLOWED for ds in receipt['expected_dependencies'].values()):
        raise ValueError('assumption whitelist drift')
    return result, files


def preservation(work, installed=False):
    _, files = review(work)
    meta = json.loads((work / 'ASSEMBLY.json').read_text())
    additions = {p.resolve() for p in files if p.relative_to(REPO).as_posix() in meta['new_paths']}
    if installed:
        for path, text in files.items():
            if path.read_text() != text:
                raise ValueError('installed source drift')
    original = Path.rglob
    def rglob(self, pattern):
        found = original(self, pattern)
        return (p for p in found if p.resolve() not in additions) if self.resolve() == (REPO / 'Coq').resolve() else found
    with patch.object(Path, 'rglob', rglob):
        fingerprint = inputs.fingerprint(REPO / 'Coq', REPO)
    if fingerprint != meta['baseline_input_sha256'] or index_hash() != meta['preexisting_staged_patch_sha256']:
        raise ValueError('baseline/index changed beyond exact reviewed additions')
    return {'only_checked_additive_delta': True, 'index_preserved': True,
            'coverage': '364/533', 'current_whole_worktree_full_acceptance': False,
            'current_input_sha256': inputs.fingerprint(REPO / 'Coq', REPO)}


def install(work):
    result, files = review(work)
    meta = json.loads((work / 'ASSEMBLY.json').read_text())
    meta['new_paths'] = sorted(str(p.relative_to(REPO)) for p in files if not p.exists())
    stage.patch.patch_files({work / 'ASSEMBLY.json': json.dumps(meta, indent=2) + '\n'})
    preservation(work)
    installed = gate.install(work)
    installed.update(preservation(work, installed=True))
    receipt = json.loads((work / 'REVIEW.json').read_text())
    stage.patch.patch_files({HERE / 'ASSEMBLY.json': json.dumps(meta, indent=2) + '\n',
                            HERE / 'REVIEW.json': json.dumps(receipt, indent=2) + '\n',
                            HERE / 'INSTALLATION.json': json.dumps(installed, indent=2) + '\n'})
    print(json.dumps(installed, indent=2))


if __name__ == '__main__':
    cli = argparse.ArgumentParser()
    cli.add_argument('mode', choices=['prepare', 'check', 'install', 'post-check'])
    cli.add_argument('--candidate', type=Path)
    args = cli.parse_args()
    if args.mode == 'prepare':
        prepare()
    elif args.mode == 'post-check':
        work = Path(json.loads((HERE / 'ASSEMBLY.json').read_text())['candidate'])
        print(json.dumps(preservation(work, installed=True), indent=2))
    else:
        if args.candidate is None:
            cli.error('--candidate is required')
        (check if args.mode == 'check' else install)(args.candidate.resolve())
