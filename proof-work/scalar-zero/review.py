"""Read-only guard for complete scalar-zero proof evidence, not acceptance."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
CLOSED = {
    'scalar_public_read_symbols', 'scalar_public_zero_symbols', 'scalar_zero_foot_block',
    'scalar_public_rest_eq', 'canonical_scalar_zero_encoded', 'scalar_locals_not_foot',
    'scalar_alloc_fresh', 'scalar_alloc_freeable', 'scalar_zero_public_body',
}
CLASSICAL_ONLY = {'scalar_alloc_lframe', 'scalar_alloc_source_fields'}


def review(archive, work):
    m = json.loads((archive / 'manifest.json').read_text())
    results, definitions = [], []
    for entry in m['modules']:
        src = (work / entry['file']).read_bytes()
        if (src != (archive / (entry['file'] + '.source')).read_bytes()
                or hashlib.sha256(src).hexdigest() != entry['sha256']):
            raise ValueError('changed actual source')
        text = src.decode()
        if (re.findall(r'^(?:Lemma|Theorem)\s+(\w+)', text, re.M) != entry['results']
                or re.findall(r'^(?:Local )?Definition\s+(\w+)', text, re.M) != entry['definitions']):
            raise ValueError('changed declarations')
        if re.search(r'\b(?:admit|Admitted|Axiom|Parameter|vm_cast_no_check)\b', text):
            raise ValueError('unpermitted construct')
        results.extend((entry['module'], n) for n in entry['results'])
        definitions.extend(entry['definitions'])
    if (len(m['modules']) != 5 or len(results) != 18 or len(set(results)) != 18
            or definitions != ['scalar_public_read_stmt', 'scalar_public_zero_stmt', 'scalar_public_rest']):
        raise ValueError('unexpected scope')
    for driver in ['scalar_zero_public_assumptions.v', 'scalar_zero_public_contracts.v']:
        if (work / driver).read_bytes() != (archive / (driver + '.source')).read_bytes():
            raise ValueError('changed driver')
    required = {'scalar-zero-public-assumptions.out', 'scalar-zero-public-contracts.out',
                'scalar-zero-public-kernel.log'}
    if set(m['output_hashes']) != required:
        raise ValueError('missing/extra output')
    for name, digest in m['output_hashes'].items():
        if hashlib.sha256((work / name).read_bytes()).hexdigest() != digest:
            raise ValueError('changed reviewed output')
    for name in ['scalar-zero-public-assumptions.err', 'scalar-zero-public-contracts.err']:
        if (work / name).read_bytes():
            raise ValueError('nonempty diagnostics')
    contracts = (work / 'scalar-zero-public-contracts.out').read_text()
    types, separator, _ = contracts.partition('scalar_public_read_stmt =\n')
    if (not separator or '...' in contracts
            or re.findall(r'^(\w+)\n\s+:', types, re.M) != [n for _, n in results]
            or re.findall(r'^([\w.]+) =', contracts, re.M) != definitions):
        raise ValueError('changed/truncated contract inventory')
    spec = importlib.util.spec_from_file_location(
        'strict_assumptions', archive.parent / 'gej-predicate/review-preliminary.py')
    parser = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(parser)
    actual = parser.assumptions(work / 'scalar-zero-public-assumptions.out',
                                {mod + '.' + n for mod, n in results})
    classical = {'ClassicalDedekindReals.sig_forall_dec', 'ClassicalDedekindReals.sig_not_dec',
                 'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'}
    execution = classical | {'Events.external_functions_sem', 'Events.inline_assembly_sem'}
    expected = {mod + '.' + n: set() if n in CLOSED else classical if n in CLASSICAL_ONLY
                else execution for mod, n in results}
    if actual != expected:
        raise ValueError('changed exact per-result dependencies')
    kernel = (work / 'scalar-zero-public-kernel.log').read_text()
    for label in ['Constants/Inductives relying on type-in-type: <none>',
                  'Constants/Inductives relying on unsafe (co)fixpoints: <none>',
                  'Inductives whose positivity is assumed: <none>']:
        if kernel.count(label) != 1:
            raise ValueError('missing/nonempty unsafe category')
    for check in ['compilation', 'contracts', 'assumptions', 'kernel']:
        if m[check]['exit_code'] != 0 or m[check]['status'] != 'terminal':
            raise ValueError('check not terminal-successful')
    if m['full_acceptance'] or m['public_coverage_added'] != 0:
        raise ValueError('pre-integration evidence mislabeled as acceptance')
    return {'results': 18, 'closed': 9, 'classical_only': 2, 'execution': 7,
            'types': 18, 'definitions': 3, 'kernel_terminal_exit_code': 0,
            'actual_source_and_outputs_match': True,
            'full_acceptance': False, 'public_coverage_added': 0}


if __name__ == '__main__':
    cli = argparse.ArgumentParser()
    cli.add_argument('--work', type=Path, required=True)
    args = cli.parse_args()
    print(json.dumps(review(Path(__file__).resolve().parent, args.work), indent=2))
