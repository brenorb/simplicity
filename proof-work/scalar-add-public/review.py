"""Strict scalar-add public proof evidence guard; not full acceptance."""
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
    if len(m['modules']) != 8 or len(results) != 19 or len(definitions) != 6:
        raise ValueError('unexpected scope')
    for driver in ['scalar_add_public_assumptions.v', 'scalar_add_public_contracts.v']:
        if (work / driver).read_bytes() != (archive / (driver + '.source')).read_bytes():
            raise ValueError('changed driver')
    required = {'public-assumptions.out', 'public-contracts.out', 'public-kernel.log'}
    if set(m['output_hashes']) != required:
        raise ValueError('missing/extra output')
    for name, digest in m['output_hashes'].items():
        if hashlib.sha256((work / name).read_bytes()).hexdigest() != digest:
            raise ValueError('changed reviewed output')
    for name in ['public-assumptions.err', 'public-contracts.err']:
        if (work / name).read_bytes():
            raise ValueError('nonempty diagnostics')
    contracts = (work / 'public-contracts.out').read_text()
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
    actual = parser.assumptions(work / 'public-assumptions.out', {mod + '.' + n for mod, n in results})
    classical = {'ClassicalDedekindReals.sig_forall_dec', 'ClassicalDedekindReals.sig_not_dec',
                 'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'}
    execution = classical | {'Events.external_functions_sem', 'Events.inline_assembly_sem'}
    closed = {'scalar_writer_outs_word', 'scalar_add_foot_blocks', 'scalar_add_body_eq',
              'scalar_add_helper_symbols', 'scalar_add_public_entry', 'scalar_add_public_blocks',
              'scalar_add_alloc_facts'}
    expected_deps = {mod + '.' + n: set() if n in closed else classical
                     if n == 'scalar_add_free_locals' else execution for mod, n in results}
    if actual != expected_deps:
        raise ValueError('changed exact per-result dependencies')
    kernel = (work / 'public-kernel.log').read_text()
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
        raise ValueError('isolated proof mislabeled as full acceptance')
    prior_spec = importlib.util.spec_from_file_location('scalar_add_verified_readers',
        archive.parent / 'scalar-add-readers/review.py')
    prior = importlib.util.module_from_spec(prior_spec)
    prior_spec.loader.exec_module(prior)
    prior.review(archive.parent / 'scalar-add-readers', work)
    literal_spec = importlib.util.spec_from_file_location('scalar_add_public_literal', archive / 'check-literal.py')
    literal = importlib.util.module_from_spec(literal_spec)
    literal_spec.loader.exec_module(literal)
    got = literal.check(archive.parent.parent, work, Path(m['dependency_candidate']) / 'Coq')
    if got != json.loads((archive / 'LITERAL-REVIEW.json').read_text()):
        raise ValueError('literal/public dependency evidence drift')
    return {'results': 19, 'closed': 7, 'classical_only': 1, 'execution': 11,
            'types': 19, 'definitions': 6, 'kernel_terminal_exit_code': 0,
            'actual_source_and_outputs_match': True, 'exact_kernel_context_inherited': True,
            'complete_literal_public_local_contract': True,
            'full_acceptance': False, 'public_coverage_added': 0}



if __name__ == '__main__':
    cli = argparse.ArgumentParser()
    cli.add_argument('--work', type=Path, required=True)
    args = cli.parse_args()
    print(json.dumps(review(Path(__file__).resolve().parent, args.work), indent=2))

