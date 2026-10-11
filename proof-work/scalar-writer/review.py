"""Strict internal whole scalar writer evidence guard, not public acceptance."""
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
            ['scalar_writer_initial_regs', 'scalar_writer_run', 'scalar_writer_tree', 'scalar_writer_result',
             'scalar_write_evok', 'scalar_write_inv', 'scalar_write_ext', 'scalar_writer_event', 'scalar_writer_bytes']):
        raise ValueError('unexpected scope')
    for driver in ['scalar_writer_assumptions.v', 'scalar_writer_contracts.v']:
        if (work / driver).read_bytes() != (archive / (driver + '.source')).read_bytes():
            raise ValueError('changed driver')
    required = {'scalar-writer-assumptions.out', 'scalar-writer-contracts.out', 'scalar-writer-kernel.log'}
    if set(m['output_hashes']) != required:
        raise ValueError('missing/extra output')
    for name, digest in m['output_hashes'].items():
        if hashlib.sha256((work / name).read_bytes()).hexdigest() != digest:
            raise ValueError('changed reviewed output')
    for name in ['scalar-writer-assumptions.err', 'scalar-writer-contracts.err']:
        if (work / name).read_bytes():
            raise ValueError('nonempty diagnostics')
    contracts = (work / 'scalar-writer-contracts.out').read_text()
    types, separator, _ = contracts.partition('scalar_writer_initial_regs =\n')
    expected_defs = ['scalar_writer_initial_regs', 'scalar_writer_run', 'scalar_writer_result',
                     'jet_secp_scalar_writer_exec.scalar_write_evok', 'jet_secp_scalar_writer_exec.scalar_write_inv',
                     'jet_secp_scalar_writer_exec.scalar_write_ext', 'scalar_writer_event', 'scalar_writer_bytes']
    if (not separator or '...' in contracts
            or re.findall(r'^(\w+)\n\s+:', types, re.M) != [n for _, n in results]
            or re.findall(r'^([\w.]+) =', contracts, re.M) != expected_defs
            or m['contract_definitions'] != expected_defs):
        raise ValueError('changed/truncated contract inventory')
    spec = importlib.util.spec_from_file_location(
        'strict_assumptions', archive.parent / 'gej-predicate/review-preliminary.py')
    parser = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(parser)
    actual = parser.assumptions(work / 'scalar-writer-assumptions.out', {mod + '.' + n for mod, n in results})
    classical = {'ClassicalDedekindReals.sig_forall_dec', 'ClassicalDedekindReals.sig_not_dec',
                 'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'}
    execution = classical | {'Events.external_functions_sem', 'Events.inline_assembly_sem'}
    storage = {'scalar_reader_storage_for_serializer', 'scalar_writer_initial_rep_from_storage',
               'scalar_writer_initial_rep_from_reader'}
    expected = {mod + '.' + n: classical if n in storage else
                execution if n.startswith('eval_') else set() for mod, n in results}
    if actual != expected:
        raise ValueError('changed exact per-result dependencies')
    kernel = (work / 'scalar-writer-kernel.log').read_text()
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
            'types': 22, 'definitions': 8, 'kernel_terminal_exit_code': 0,
            'actual_source_and_outputs_match': True,
            'full_acceptance': False, 'public_coverage_added': 0}


if __name__ == '__main__':
    cli = argparse.ArgumentParser()
    cli.add_argument('--work', type=Path, required=True)
    args = cli.parse_args()
    print(json.dumps(review(Path(__file__).resolve().parent, args.work), indent=2))
