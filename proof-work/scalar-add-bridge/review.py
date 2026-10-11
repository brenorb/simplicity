"""Strict helper-to-literal scalar-add bridge guard; not public acceptance."""
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
        definitions.extend((entry['module'], n) for n in entry['definitions'])
    if len(m['modules']) != 4 or len(results) != 8 or len(definitions) != 1:
        raise ValueError('unexpected scope')
    for driver in ['scalar_add_bridge_assumptions.v', 'scalar_add_bridge_contracts.v']:
        if (work / driver).read_bytes() != (archive / (driver + '.source')).read_bytes():
            raise ValueError('changed driver')
    required = {'bridge-assumptions.out', 'bridge-contracts.out', 'bridge-kernel.log'}
    if set(m['output_hashes']) != required:
        raise ValueError('missing/extra output')
    for name, digest in m['output_hashes'].items():
        if hashlib.sha256((work / name).read_bytes()).hexdigest() != digest:
            raise ValueError('changed reviewed output')
    for name in ['bridge-assumptions.err', 'bridge-contracts.err']:
        if (work / name).read_bytes():
            raise ValueError('nonempty diagnostics')
    contracts = (work / 'bridge-contracts.out').read_text()
    markers = list(re.finditer(r'(?m)^SCALAR_(TYPE|DEF) (\S+)\n', contracts))
    expected = [('TYPE', mod + '.' + n) for mod, n in results]
    expected += [('DEF', mod + '.' + n) for mod, n in definitions if not n.endswith('_tree')]
    if ('...' in contracts or [(x[1], x[2]) for x in markers] != expected
            or m['contract_definitions'] != [n for _, n in definitions if not n.endswith('_tree')]):
        raise ValueError('changed/truncated contract inventory')
    for i, marker in enumerate(markers):
        body = contracts[marker.end():markers[i+1].start() if i+1 < len(markers) else len(contracts)]
        name = marker[2].rsplit('.', 1)[1]
        header = r'^' + re.escape(name) + (r'\n\s+:' if marker[1] == 'TYPE' else r' =')
        if not re.search(header, body):
            raise ValueError('marker without expected printed declaration')
    spec = importlib.util.spec_from_file_location(
        'strict_assumptions', archive.parent / 'gej-predicate/review-preliminary.py')
    parser = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(parser)
    actual = parser.assumptions(work / 'bridge-assumptions.out', {mod + '.' + n for mod, n in results})
    classical = {'ClassicalDedekindReals.sig_forall_dec', 'ClassicalDedekindReals.sig_not_dec',
                 'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'}
    execution = classical | {'Events.external_functions_sem', 'Events.inline_assembly_sem'}
    extensional = {'FunctionalExtensionality.functional_extensionality_dep'}
    expected_deps = {mod + '.' + n: classical if n in {'scalar_add_output_scalar_at', 'scalar_writer_initial_rep_from_add'} else
                     extensional if n in {'canonical_scalar_add_numeric', 'canonical_scalar_add_normalize_value'} else
                     execution if n.startswith('eval_') else set() for mod, n in results}
    if actual != expected_deps:
        raise ValueError('changed exact per-result dependencies')
    kernel = (work / 'bridge-kernel.log').read_text()
    for label in ['Constants/Inductives relying on type-in-type: <none>',
                  'Constants/Inductives relying on unsafe (co)fixpoints: <none>',
                  'Inductives whose positivity is assumed: <none>']:
        if kernel.count(label) != 1:
            raise ValueError('missing/nonempty unsafe category')
    if kernel.count('CONTEXT SUMMARY') != 1 or kernel.count('* Axioms:') != 1:
        raise ValueError('missing/duplicate kernel context')
    axiom_text = kernel.split('* Axioms:', 1)[1].split('* Constants/Inductives', 1)[0]
    inherited = (Path(m['dependency_candidate']) / 'Coq/C/jet_coqchk_axioms.expected').read_text().splitlines()
    if sorted(axiom_text.split()) != sorted(inherited):
        raise ValueError('kernel context differs from inherited allowlist')
    for check in ['compilation', 'contracts', 'assumptions', 'kernel']:
        if m[check]['exit_code'] != 0 or m[check]['status'] != 'terminal':
            raise ValueError('check not terminal-successful')
    if m['full_acceptance'] or m['public_coverage_added'] != 0:
        raise ValueError('internal evidence mislabeled as public acceptance')
    helper_spec = importlib.util.spec_from_file_location('scalar_add_helper_review', archive.parent / 'scalar-add/review.py')
    helper = importlib.util.module_from_spec(helper_spec)
    helper_spec.loader.exec_module(helper)
    helper.review(archive.parent / 'scalar-add', work)
    gate_spec = importlib.util.spec_from_file_location('scalar_add_literal_review', archive / 'check-literal.py')
    gate = importlib.util.module_from_spec(gate_spec)
    gate_spec.loader.exec_module(gate)
    repo = archive.parent.parent
    if gate.check(repo, work, Path(m['dependency_candidate']) / 'Coq') != json.loads((archive / 'LITERAL-REVIEW.json').read_text()):
        raise ValueError('literal source correspondence evidence changed')
    return {'results': 8, 'closed': 3, 'functional_extensionality_only': 2, 'classical_only': 2, 'execution': 1,
            'types': 8, 'definitions': 1, 'kernel_terminal_exit_code': 0,
            'actual_source_and_outputs_match': True, 'exact_kernel_context_inherited': True,
            'full_acceptance': False, 'public_coverage_added': 0}


if __name__ == '__main__':
    cli = argparse.ArgumentParser()
    cli.add_argument('--work', type=Path, required=True)
    args = cli.parse_args()
    print(json.dumps(review(Path(__file__).resolve().parent, args.work), indent=2))
