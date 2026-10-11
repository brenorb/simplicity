"""Strict complete public local scalar-negate proof; not integrated full acceptance."""
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
    if (len(m['modules']) != 5 or len(results) != 11 or definitions != ["scalar_negate_inplace_stmt","scalar_negate_rest","scalar_negate_temps"]):
        raise ValueError('unexpected scope')
    for driver in ['scalar_negate_public_assumptions.v', 'scalar_negate_public_contracts.v']:
        if (work / driver).read_bytes() != (archive / (driver + '.source')).read_bytes():
            raise ValueError('changed driver')
    required = {'scalar-negate-public-assumptions.out', 'scalar-negate-public-contracts.out', 'scalar-negate-public-kernel.log', 'scalar-negate-public-literal.json'}
    if set(m['output_hashes']) != required:
        raise ValueError('missing/extra output')
    for name, digest in m['output_hashes'].items():
        if hashlib.sha256((work / name).read_bytes()).hexdigest() != digest:
            raise ValueError('changed reviewed output')
    for name in ['scalar-negate-public-assumptions.err', 'scalar-negate-public-contracts.err']:
        if (work / name).read_bytes():
            raise ValueError('nonempty diagnostics')
    contracts = (work / 'scalar-negate-public-contracts.out').read_text()
    types, separator, _ = contracts.partition('scalar_negate_inplace_stmt =\n')
    expected_defs = ["scalar_negate_inplace_stmt","scalar_negate_rest","scalar_negate_temps","jet_secp_normalize_local.secp_jet_local_spec"]
    if (not separator or '...' in contracts
            or re.findall(r'^(\w+)\n\s+:', types, re.M) != [n for _, n in results]
            or re.findall(r'^([\w.]+) =', contracts, re.M) != expected_defs
            or m['contract_definitions'] != expected_defs):
        raise ValueError('changed/truncated contract inventory')
    spec = importlib.util.spec_from_file_location(
        'strict_assumptions', archive.parent / 'gej-predicate/review-preliminary.py')
    parser = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(parser)
    actual = parser.assumptions(work / 'scalar-negate-public-assumptions.out', {mod + '.' + n for mod, n in results})
    classical = {'ClassicalDedekindReals.sig_forall_dec', 'ClassicalDedekindReals.sig_not_dec',
                 'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'}
    execution = classical | {'Events.external_functions_sem', 'Events.inline_assembly_sem'}
    functional = {'FunctionalExtensionality.functional_extensionality_dep'}
    exec_names = {'eval_scalar_read_negate_write_canonical', 'exec_scalar_negate_inplace',
                  'exec_scalar_negate_rest_canonical', 'eval_secp_scalar_negate_canonical',
                  'scalar_negate_local_spec'}
    expected = {mod + '.' + n: functional if n == 'scalar_negate_normalize_identity' else
                execution if n in exec_names else set() for mod, n in results}
    if actual != expected:
        raise ValueError('changed exact per-result dependencies')
    literal = json.loads((work / 'scalar-negate-public-literal.json').read_text())
    if (literal['literal_scalar_ports'] != 6 or not literal['scalar_negate_literal_structure']
            or not literal['recursive_dependency_gate'] or not literal['complete_literal_public_contract']
            or literal['public_coverage_added'] != 0):
        raise ValueError('incorrect literal scope receipt')
    gate_spec = importlib.util.spec_from_file_location('scalar_negate_gate', archive / 'check-literal.py')
    gate = importlib.util.module_from_spec(gate_spec)
    gate_spec.loader.exec_module(gate)
    fresh = gate.check(Path(m['repository']), work, Path(m['original_dependencies']),
                       Path(m['dependency_candidate']) / 'Coq')
    if fresh != literal:
        raise ValueError('literal gate did not reproduce')
    kernel = (work / 'scalar-negate-public-kernel.log').read_text()
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
    return {'results': 11, 'closed': 5, 'functional_extensionality_only': 1, 'execution': 5,
            'types': 11, 'definitions': 4, 'kernel_terminal_exit_code': 0,
            'actual_source_and_outputs_match': True,
            'full_acceptance': False, 'public_coverage_added': 0}


if __name__ == '__main__':
    cli = argparse.ArgumentParser()
    cli.add_argument('--work', type=Path, required=True)
    args = cli.parse_args()
    print(json.dumps(review(Path(__file__).resolve().parent, args.work), indent=2))
