"""Strict internal scalar-negate helper evidence guard, not public acceptance."""
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
    if (len(m['modules']) != 5 or len(results) != 22 or definitions !=
            ["scalar_negate_run","scalar_negate_tree","scalar_negate_state","scalar_negate_limbs","scalar_negate_mask","scalar_negate_delta0","scalar_negate_low0","scalar_negate_high0","scalar_negate_low1","scalar_negate_high1","scalar_negate_low2","scalar_negate_high2","scalar_negate_low3","scalar_negate_raw","scalar_negate_raw_value","scalar_negate_output_value"]):
        raise ValueError('unexpected scope')
    for driver in ['scalar_negate_assumptions.v', 'scalar_negate_contracts.v']:
        if (work / driver).read_bytes() != (archive / (driver + '.source')).read_bytes():
            raise ValueError('changed driver')
    required = {'scalar-negate-assumptions.out', 'scalar-negate-contracts.out', 'scalar-negate-kernel.log'}
    if set(m['output_hashes']) != required:
        raise ValueError('missing/extra output')
    for name, digest in m['output_hashes'].items():
        if hashlib.sha256((work / name).read_bytes()).hexdigest() != digest:
            raise ValueError('changed reviewed output')
    for name in ['scalar-negate-assumptions.err', 'scalar-negate-contracts.err']:
        if (work / name).read_bytes():
            raise ValueError('nonempty diagnostics')
    contracts = (work / 'scalar-negate-contracts.out').read_text()
    types, separator, _ = contracts.partition('scalar_negate_run =\n')
    expected_defs = ["scalar_negate_run","scalar_negate_state","scalar_negate_limbs","scalar_negate_mask","scalar_negate_delta0","scalar_negate_low0","scalar_negate_high0","scalar_negate_low1","scalar_negate_high1","scalar_negate_low2","scalar_negate_high2","scalar_negate_low3","scalar_negate_raw","scalar_negate_raw_value","scalar_negate_output_value"]
    if (not separator or '...' in contracts
            or re.findall(r'^(\w+)\n\s+:', types, re.M) != [n for _, n in results]
            or re.findall(r'^([\w.]+) =', contracts, re.M) != expected_defs
            or m['contract_definitions'] != expected_defs):
        raise ValueError('changed/truncated contract inventory')
    spec = importlib.util.spec_from_file_location(
        'strict_assumptions', archive.parent / 'gej-predicate/review-preliminary.py')
    parser = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(parser)
    actual = parser.assumptions(work / 'scalar-negate-assumptions.out', {mod + '.' + n for mod, n in results})
    classical = {'ClassicalDedekindReals.sig_forall_dec', 'ClassicalDedekindReals.sig_not_dec',
                 'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'}
    execution = classical | {'Events.external_functions_sem', 'Events.inline_assembly_sem'}
    storage = {'scalar_negate_final_storage', 'scalar_negate_output_scalar_at',
               'scalar_writer_initial_rep_from_negate'}
    expected = {mod + '.' + n: classical if n in storage else
                execution if n.startswith('eval_') else set() for mod, n in results}
    if actual != expected:
        raise ValueError('changed exact per-result dependencies')
    kernel = (work / 'scalar-negate-kernel.log').read_text()
    for label in ['Constants/Inductives relying on type-in-type: <none>',
                  'Constants/Inductives relying on unsafe (co)fixpoints: <none>',
                  'Inductives whose positivity is assumed: <none>']:
        if kernel.count(label) != 1:
            raise ValueError('missing/nonempty unsafe category')
    for check in ['compilation', 'contracts', 'assumptions', 'kernel']:
        if m[check]['exit_code'] != 0 or m[check]['status'] != 'terminal':
            raise ValueError('check not terminal-successful')
    if m['full_acceptance'] or m['public_coverage_added'] != 0:
        raise ValueError('internal evidence mislabeled as public acceptance')
    return {'results': 22, 'closed': 17, 'classical_only': 3, 'execution': 2,
            'types': 22, 'definitions': 15, 'kernel_terminal_exit_code': 0,
            'actual_source_and_outputs_match': True,
            'full_acceptance': False, 'public_coverage_added': 0}


if __name__ == '__main__':
    cli = argparse.ArgumentParser()
    cli.add_argument('--work', type=Path, required=True)
    args = cli.parse_args()
    print(json.dumps(review(Path(__file__).resolve().parent, args.work), indent=2))
