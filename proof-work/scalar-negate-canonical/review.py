"""Strict literal scalar-negate helper contract, not public acceptance."""
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
    if (len(m['modules']) != 3 or len(results) != 14 or definitions != ["canonical_scalar_normalize512","canonical_scalar_multiply","canonical_scalar_negate_factor","canonical_scalar_negate"]):
        raise ValueError('unexpected scope')
    for driver in ['scalar_negate_canonical_assumptions.v', 'scalar_negate_canonical_contracts.v']:
        if (work / driver).read_bytes() != (archive / (driver + '.source')).read_bytes():
            raise ValueError('changed driver')
    required = {'scalar-negate-canonical-assumptions.out', 'scalar-negate-canonical-contracts.out', 'scalar-negate-canonical-kernel.log', 'scalar-negate-canonical-literal.json'}
    if set(m['output_hashes']) != required:
        raise ValueError('missing/extra output')
    for name, digest in m['output_hashes'].items():
        if hashlib.sha256((work / name).read_bytes()).hexdigest() != digest:
            raise ValueError('changed reviewed output')
    for name in ['scalar-negate-canonical-assumptions.err', 'scalar-negate-canonical-contracts.err']:
        if (work / name).read_bytes():
            raise ValueError('nonempty diagnostics')
    contracts = (work / 'scalar-negate-canonical-contracts.out').read_text()
    types, separator, _ = contracts.partition('canonical_scalar_normalize512 =\n')
    expected_defs = ["canonical_scalar_normalize512","canonical_scalar_multiply","canonical_scalar_negate_factor","canonical_scalar_negate"]
    if (not separator or '...' in contracts
            or re.findall(r'^(\w+)\n\s+:', types, re.M) != [n for _, n in results]
            or re.findall(r'^([\w.]+) =', contracts, re.M) != expected_defs
            or m['contract_definitions'] != expected_defs):
        raise ValueError('changed/truncated contract inventory')
    spec = importlib.util.spec_from_file_location(
        'strict_assumptions', archive.parent / 'gej-predicate/review-preliminary.py')
    parser = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(parser)
    actual = parser.assumptions(work / 'scalar-negate-canonical-assumptions.out', {mod + '.' + n for mod, n in results})
    classical = {'ClassicalDedekindReals.sig_forall_dec', 'ClassicalDedekindReals.sig_not_dec',
                 'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'}
    execution = classical | {'Events.external_functions_sem', 'Events.inline_assembly_sem'}
    functional = {'FunctionalExtensionality.functional_extensionality_dep'}
    fun_names = {'canonical_scalar_normalize512_numeric', 'canonical_scalar_negate_numeric',
                 'canonical_scalar_negate_normalize_value', 'scalar_negate_output_canonical'}
    expected = {mod + '.' + n: functional if n in fun_names else
                execution if n == 'eval_scalar_negate_canonical_owned' else set() for mod, n in results}
    if actual != expected:
        raise ValueError('changed exact per-result dependencies')
    literal = json.loads((work / 'scalar-negate-canonical-literal.json').read_text())
    if (literal['literal_scalar_ports'] != 6 or not literal['scalar_negate_literal_structure']
            or not literal['recursive_dependency_gate'] or literal['complete_literal_public_contract']
            or literal['public_coverage_added'] != 0):
        raise ValueError('incorrect literal scope receipt')
    gate_spec = importlib.util.spec_from_file_location('scalar_negate_gate', archive / 'check-literal.py')
    gate = importlib.util.module_from_spec(gate_spec)
    gate_spec.loader.exec_module(gate)
    fresh = gate.check(Path(m['repository']), work, Path(m['original_dependencies']),
                       Path(m['dependency_candidate']) / 'Coq')
    if fresh != literal:
        raise ValueError('literal gate did not reproduce')
    kernel = (work / 'scalar-negate-canonical-kernel.log').read_text()
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
    return {'results': 14, 'closed': 9, 'functional_extensionality_only': 4, 'execution': 1,
            'types': 14, 'definitions': 4, 'kernel_terminal_exit_code': 0,
            'actual_source_and_outputs_match': True,
            'full_acceptance': False, 'public_coverage_added': 0}


if __name__ == '__main__':
    cli = argparse.ArgumentParser()
    cli.add_argument('--work', type=Path, required=True)
    args = cli.parse_args()
    print(json.dumps(review(Path(__file__).resolve().parent, args.work), indent=2))
