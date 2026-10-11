"""Pinned internal C setter evidence; never labels it public acceptance."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True


def review(archive, work):
    manifest = json.loads((archive / 'manifest.json').read_text())
    wanted, types, definitions = set(), [], []
    for entry in manifest['modules']:
        source = (work / entry['file']).read_bytes()
        if (hashlib.sha256(source).hexdigest() != entry['sha256']
                or source != (archive / entry['source']).read_bytes()):
            raise ValueError('changed actual source: ' + entry['file'])
        text = source.decode()
        names = re.findall(r'^(?:Lemma|Theorem)\s+(\w+)', text, re.M)
        defs = re.findall(r'^(?:Definition|Fixpoint)\s+(\w+)', text, re.M)
        if names != entry['results'] or defs != entry['definitions']:
            raise ValueError('changed declaration inventory')
        if re.search(r'\b(?:admit|Admitted|Axiom|Parameter|vm_cast_no_check)\b', text):
            raise ValueError('unpermitted proof construct')
        wanted.update(entry['module'] + '.' + n for n in names)
        types.extend(names)
        definitions.extend(defs)
    if len(manifest['modules']) != 4 or len(wanted) != 30 or len(definitions) != 20:
        raise ValueError('unexpected evidence scope')
    for driver in ['scalar_set_assumptions.v', 'scalar_set_contracts.v', 'scalar_set_trees.v']:
        if (work / driver).read_bytes() != (archive / (driver + '.source')).read_bytes():
            raise ValueError('changed driver: ' + driver)
    for filename, digest in manifest['output_hashes'].items():
        if hashlib.sha256((work / filename).read_bytes()).hexdigest() != digest:
            raise ValueError('changed reviewed output: ' + filename)
    for filename in ['scalar-set-assumptions.err', 'scalar-set-contracts.err', 'scalar-set-trees.err']:
        if (work / filename).read_bytes():
            raise ValueError('nonempty diagnostics: ' + filename)
    contracts = (work / 'scalar-set-contracts.out').read_text()
    trees = (work / 'scalar-set-trees.out').read_text()
    if '...' in contracts or '...' in trees:
        raise ValueError('truncated printing')
    type_section, separator, _ = contracts.partition('scalar_bind =\n')
    if not separator or re.findall(r'^(\w+)\n\s+:', type_section, re.M) != types:
        raise ValueError('missing/duplicate/reordered types')
    if re.findall(r'^(\w+) =', contracts, re.M) != [n for n in definitions if not n.endswith('_tree')]:
        raise ValueError('changed non-tree definition inventory')
    if re.findall(r'^(\w+) =', trees, re.M) != ['scalar_set_raw_tree', 'scalar_set_owned_tree']:
        raise ValueError('changed computed-tree inventory')
    spec = importlib.util.spec_from_file_location(
        'strict_assumptions', archive.parent / 'gej-predicate/review-preliminary.py')
    parser = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(parser)
    actual = parser.assumptions(work / 'scalar-set-assumptions.out', wanted)
    classical = {'ClassicalDedekindReals.sig_forall_dec', 'ClassicalDedekindReals.sig_not_dec',
                 'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'}
    execution = classical | {'Events.external_functions_sem', 'Events.inline_assembly_sem'}
    expected = {name: set() for name in wanted}
    prefix = 'OriginalC.jet_secp_scalar_set_owned.'
    expected[prefix + 'eval_scalar_set_b32_owned'] = execution
    expected[prefix + 'eval_scalar_set_b32_bytes_owned'] = execution
    expected[prefix + 'scalar_set_owned_loads'] = classical
    if actual != expected or sum(not a for a in actual.values()) != 27:
        raise ValueError('changed per-result dependencies')
    kernel = (work / 'scalar-set-kernel.log').read_text()
    for text in ['Constants/Inductives relying on type-in-type: <none>',
                 'Constants/Inductives relying on unsafe (co)fixpoints: <none>',
                 'Inductives whose positivity is assumed: <none>']:
        if kernel.count(text) != 1:
            raise ValueError('nonempty/missing unsafe category')
    if manifest['kernel']['exit_code'] != 0 or manifest['kernel']['status'] != 'terminal':
        raise ValueError('kernel run not terminal-successful')
    if manifest['full_acceptance'] or manifest['public_coverage_added'] != 0:
        raise ValueError('internal results mislabeled as public acceptance')
    return {'modules': 4, 'results': 30, 'closed': 27, 'types': 30,
            'non_tree_definitions': 18, 'diagnostic_computed_trees': 2,
            'actual_source_and_pinned_outputs_match': True,
            'kernel_terminal_exit_code': 0, 'full_acceptance': False, 'public_coverage_added': 0}


if __name__ == '__main__':
    cli = argparse.ArgumentParser()
    cli.add_argument('--work', type=Path, required=True)
    args = cli.parse_args()
    print(json.dumps(review(Path(__file__).resolve().parent, args.work), indent=2))
