"""Read-only guard for internal scalar public-entry evidence, not acceptance."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True


def review(archive, work):
    m = json.loads((archive / 'manifest.json').read_text())
    src = (work / m['file']).read_bytes()
    if (src != (archive / (m['file'] + '.source')).read_bytes()
            or hashlib.sha256(src).hexdigest() != m['sha256']):
        raise ValueError('changed actual source')
    text = src.decode()
    if (re.findall(r'^(?:Lemma|Theorem)\s+(\w+)', text, re.M) != m['results']
            or re.findall(r'^(?:Local )?Definition\s+(\w+)', text, re.M) != m['definitions']):
        raise ValueError('changed declarations')
    if re.search(r'\b(?:admit|Admitted|Axiom|Parameter|vm_cast_no_check)\b', text):
        raise ValueError('unpermitted construct')
    if len(m['results']) != 7 or len(m['definitions']) != 2:
        raise ValueError('unexpected scope')
    for driver in ['scalar_public_entry_assumptions.v', 'scalar_public_entry_contracts.v']:
        if (work / driver).read_bytes() != (archive / (driver + '.source')).read_bytes():
            raise ValueError('changed driver')
    required = {'scalar-public-entry-assumptions.out',
                'scalar-public-entry-contracts.out', 'scalar-public-entry-kernel.log'}
    if set(m['output_hashes']) != required:
        raise ValueError('missing/extra outputs')
    for name, digest in m['output_hashes'].items():
        if hashlib.sha256((work / name).read_bytes()).hexdigest() != digest:
            raise ValueError('changed reviewed output')
    for name in ['scalar-public-entry-assumptions.err', 'scalar-public-entry-contracts.err']:
        if (work / name).read_bytes():
            raise ValueError('nonempty diagnostics')
    contracts = (work / 'scalar-public-entry-contracts.out').read_text()
    types, separator, _ = contracts.partition('scalar_public_env =\n')
    if (not separator or '...' in contracts
            or re.findall(r'^(\w+)\n\s+:', types, re.M) != m['results']):
        raise ValueError('missing/duplicate/reordered/truncated types')
    defs = m['definitions']
    if re.findall(r'^([\w.]+) =', contracts, re.M) != defs:
        raise ValueError('changed definition inventory')
    spec = importlib.util.spec_from_file_location(
        'strict_assumptions', archive.parent / 'gej-predicate/review-preliminary.py')
    parser = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(parser)
    wanted = {m['module'] + '.' + n for n in m['results']}
    actual = parser.assumptions(work / 'scalar-public-entry-assumptions.out', wanted)
    classical = {'ClassicalDedekindReals.sig_forall_dec', 'ClassicalDedekindReals.sig_not_dec',
                 'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'}
    execution = classical | {'Events.external_functions_sem', 'Events.inline_assembly_sem'}
    closed = {'scalar_zero_public_entry', 'scalar_public_blocks', 'scalar_public_src_temp'}
    expected = {m['module'] + '.' + n:
                set() if n in closed else execution if n == 'exec_scalar_public_copy' else classical
                for n in m['results']}
    pinned = {m['module'] + '.' + n: set(a) for n, a in m['expected_dependencies'].items()}
    if actual != expected or pinned != expected:
        raise ValueError('changed exact per-result dependencies')
    kernel = (work / 'scalar-public-entry-kernel.log').read_text()
    for label in ['Constants/Inductives relying on type-in-type: <none>',
                  'Constants/Inductives relying on unsafe (co)fixpoints: <none>',
                  'Inductives whose positivity is assumed: <none>']:
        if kernel.count(label) != 1:
            raise ValueError('missing/nonempty unsafe category')
    for check in ['compilation', 'contracts', 'assumptions', 'kernel']:
        if m[check]['exit_code'] != 0 or m[check]['status'] != 'terminal':
            raise ValueError('check not terminal-successful')
    if m['full_acceptance'] or m['public_coverage_added'] != 0:
        raise ValueError('internal result mislabeled as acceptance')
    return {'results': 7, 'closed': 3, 'classical_only': 3, 'execution': 1,
            'types': 7, 'definitions': 2, 'kernel_terminal_exit_code': 0,
            'actual_source_and_outputs_match': True,
            'full_acceptance': False, 'public_coverage_added': 0}


if __name__ == '__main__':
    cli = argparse.ArgumentParser()
    cli.add_argument('--work', type=Path, required=True)
    args = cli.parse_args()
    print(json.dumps(review(Path(__file__).resolve().parent, args.work), indent=2))
