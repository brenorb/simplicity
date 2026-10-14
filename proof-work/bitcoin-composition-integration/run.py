"""Bounded five-file composition/free integration, using checked audit code.

The prior transaction batch stays immutable. Its hash-pinned derived-program
objects may be reused, but the new closure is built and kernel checked again.
No normal C namespace, coverage row, or existing source is replaced.
"""
import argparse
import contextlib
import io
import json
from pathlib import Path
import sys
from types import SimpleNamespace

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
REPO = HERE.parent.parent
PRIOR = HERE.parent / 'bitcoin-transaction-integration'

import importlib.util


def load(name):
    spec = importlib.util.spec_from_file_location(name, PRIOR / 'run.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


previous = load('composition_previous')
current = load('composition_current')
NAMES = [
    'jet_bitcoin_env_build', 'jet_bitcoin_env_free',
    'jet_bitcoin_env_txenv', 'jet_bitcoin_env_txenv_link',
    'jet_bitcoin_env_lifecycle',
]
PATHS = sorted('Coq/bitcoin-env/C/' + name + '.v' for name in NAMES)
ROOTS = ['jet_bitcoin_env_build', 'jet_bitcoin_env_lifecycle']
SCOPE = 'Actual build_txEnv and canonical sigAllHash, three-builder composition, and defined free semantics; supporting distinct-program verification only.'


def check_previous():
    work = Path(json.loads((PRIOR / 'ASSEMBLY.json').read_text())['candidate'])
    previous.preservation(work, installed=True)


current.HERE = HERE
current.BASE = PRIOR
current.old_post = SimpleNamespace(check=check_previous)
current.stage.ROOTS = ROOTS
current.BOUNDARIES = [
    'memcpy_model on construction; frees use defined CompCert EF_free',
    'readable raw structures/buffers and address bounds',
    'writable 56-byte aligned txEnv destination',
    'SHA dispatch/counter/tag startup premises for the distinct environment unit',
    'CompCert successful malloc semantics; allocation failure not covered',
    'Bitcoin represented environment requires nonempty inputs; tap-path length <=128',
    'raw txid bytes copied, not calculated or validated',
    'raw_buffer_at requires valid non-null data blocks even for empty buffers',
    'no original-program caller-to-jet composition, startup establishment, ready-jet sweep or new coverage',
]
original_review = current.review
original_run = current.gate.audit.run


def audit_run(work, command, stem, timeout):
    # Keep the full recursive check, but retain progress instead of a silent log.
    if stem == 'kernel':
        command = [arg for arg in command if arg != '-silent']
    result = original_run(work, command, stem, timeout)
    if stem == 'assumptions':
        deps = current.gate.audit.normal.assumptions((work / 'assumptions.log').read_text())
        if any(not set(ds) <= current.ALLOWED for ds in deps.values()):
            raise ValueError('unexpected assumptions; stopped before expensive kernel check')
    return result


current.gate.audit.run = audit_run


def review(work):
    result, files = original_review(work)
    meta = json.loads((work / 'ASSEMBLY.json').read_text())
    if meta['composition_new_paths'] != PATHS or meta['scope'] != SCOPE:
        raise ValueError('composition batch scope drift')
    if meta['planned_new_paths'] not in [PATHS, []]:
        raise ValueError('unexpected planned composition delta')
    if 'new_paths' in meta and meta['new_paths'] != meta['planned_new_paths']:
        raise ValueError('unexpected composition installation delta')
    compiled = set()
    for line in (work / 'build.log').read_text().splitlines():
        if line.startswith('COQC C/') and line.endswith('.v'):
            compiled.add(line.removeprefix('COQC C/').removesuffix('.v'))
    if not set(NAMES) <= compiled:
        raise ValueError('new composition modules were not freshly compiled')
    receipt = json.loads((work / 'REVIEW.json').read_text())
    if receipt['kernel']['command'] != ['bash', 'build-jets.sh', '--coqchk', '-o'] + ['C.' + n for n in ROOTS]:
        raise ValueError('kernel command does not check the complete selected closure')
    prior = json.loads((PRIOR / 'REVIEW.json').read_text())
    for name, deps in receipt['expected_dependencies'].items():
        if name in prior['expected_dependencies'] and deps != prior['expected_dependencies'][name]:
            raise ValueError('inherited transaction assumptions changed')
    return result, files


current.review = review
sha = current.sha


def prepare():
    with contextlib.redirect_stdout(io.StringIO()) as out:
        current.prepare()
    summary = json.loads(out.getvalue())
    work = Path(summary['candidate'])
    planned = sorted(summary['new_sources'])
    if planned != PATHS and not (planned == [] and (HERE / 'INSTALLATION.json').exists()):
        raise ValueError('closure contains additions beyond the five reviewed sources')
    meta = json.loads((work / 'ASSEMBLY.json').read_text())
    meta.update(scope=SCOPE, composition_new_paths=PATHS, planned_new_paths=planned)
    current.stage.patch.patch_files({work / 'ASSEMBLY.json': json.dumps(meta, indent=2) + '\n'})
    print(json.dumps(summary, indent=2))


if __name__ == '__main__':
    cli = argparse.ArgumentParser()
    cli.add_argument('mode', choices=['prepare', 'check', 'install', 'post-check'])
    cli.add_argument('--candidate', type=Path)
    args = cli.parse_args()
    if args.mode == 'prepare':
        prepare()
    elif args.mode == 'post-check':
        work = Path(json.loads((HERE / 'ASSEMBLY.json').read_text())['candidate'])
        print(json.dumps(current.preservation(work, installed=True), indent=2))
    else:
        if args.candidate is None:
            cli.error('--candidate is required')
        (current.check if args.mode == 'check' else current.install)(args.candidate.resolve())
