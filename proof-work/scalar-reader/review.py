"""Review pinned internal reader evidence, never public-jet acceptance."""
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
    wanted, types, definitions, trees = set(), [], [], []
    for entry in manifest['modules']:
        source = (work / entry['file']).read_bytes()
        if (hashlib.sha256(source).hexdigest() != entry['sha256']
                or source != (archive / entry['source']).read_bytes()):
            raise ValueError('changed actual source: ' + entry['file'])
        text = source.decode()
        names = re.findall(r'^(?:Lemma|Theorem)\s+(\w+)', text, re.M)
        defs = re.findall(r'^(?:Local )?(?:Definition|Fixpoint)\s+(\w+)', text, re.M)
        if names != entry['results'] or defs != entry['definitions']:
            raise ValueError('changed declaration inventory')
        if re.search(r'\b(?:admit|Admitted|Axiom|Parameter|vm_cast_no_check)\b', text):
            raise ValueError('unpermitted proof construct')
        wanted.update(entry['module'] + '.' + n for n in names)
        types.extend(names)
        for name in defs:
            if name.endswith('_tree'):
                trees.append(name)
            else:
                definitions.append(entry['module'].removeprefix('OriginalC.') + '.' + name
                                   if name.startswith('rd_') else name)
    if len(manifest['modules']) != 6 or len(wanted) != 31 or len(definitions) != 23:
        raise ValueError('unexpected evidence scope')
    if trees != ['scalar_reader_tree', 'scalar_reader_set_tree']:
        raise ValueError('unexpected tree scope')
    for driver in ['scalar_reader_assumptions.v', 'scalar_reader_contracts.v', 'scalar_reader_trees.v']:
        if (work / driver).read_bytes() != (archive / (driver + '.source')).read_bytes():
            raise ValueError('changed driver: ' + driver)
    required = {'scalar-reader-assumptions.out', 'scalar-reader-contracts.out',
                'scalar-reader-trees.out', 'scalar-reader-kernel.log'}
    if set(manifest['output_hashes']) != required:
        raise ValueError('missing/extra evidence hashes')
    for filename, digest in manifest['output_hashes'].items():
        if hashlib.sha256((work / filename).read_bytes()).hexdigest() != digest:
            raise ValueError('changed reviewed output: ' + filename)
    for filename in ['scalar-reader-assumptions.err', 'scalar-reader-contracts.err', 'scalar-reader-trees.err']:
        if (work / filename).read_bytes():
            raise ValueError('nonempty diagnostics: ' + filename)
    contracts = (work / 'scalar-reader-contracts.out').read_text()
    tree_text = (work / 'scalar-reader-trees.out').read_text()
    if '...' in contracts or '...' in tree_text:
        raise ValueError('truncated printing')
    type_section, separator, _ = contracts.partition('scalar_reader_table =\n')
    if not separator or re.findall(r'^(\w+)\n\s+:', type_section, re.M) != types:
        raise ValueError('missing/duplicate/reordered types')
    if re.findall(r'^([\w.]+) =', contracts, re.M) != definitions:
        raise ValueError('changed non-tree definition inventory')
    if re.findall(r'^([\w.]+) =', tree_text, re.M) != trees:
        raise ValueError('changed computed-tree inventory')
    spec = importlib.util.spec_from_file_location(
        'strict_assumptions', archive.parent / 'gej-predicate/review-preliminary.py')
    parser = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(parser)
    actual = parser.assumptions(work / 'scalar-reader-assumptions.out', wanted)
    classical = {'ClassicalDedekindReals.sig_forall_dec', 'ClassicalDedekindReals.sig_not_dec',
                 'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'}
    execution = classical | {'Events.external_functions_sem', 'Events.inline_assembly_sem'}
    expected = {name: set() for name in wanted}
    for module, names in {
        'jet_secp_pure_oracle_frame': ['separated_external_not_foot', 'pure_frame_external'],
        'jet_secp_shift64_frame': ['invA_append_nonwrite'],
        'jet_secp_scalar_reader_value': ['scalar_reader_set_loads'],
    }.items():
        for name in names:
            expected['OriginalC.' + module + '.' + name] = classical
    for module, names in {
        'jet_secp_pure_oracle_frame': ['pure_oracle_frame_lift'],
        'jet_secp_shift64_frame': ['shift64_frame_oracle'],
        'jet_secp_scalar_reader_run': ['scalar_reader_entries', 'exec_scalar_reader_first'],
        'jet_secp_scalar_reader_set': ['eval_scalar_reader_set', 'exec_scalar_reader_second'],
        'jet_secp_scalar_reader_body': ['exec_scalar_reader_body', 'exec_scalar_reader_body_numeric'],
    }.items():
        for name in names:
            expected['OriginalC.' + module + '.' + name] = execution
    if actual != expected or sum(not a for a in actual.values()) != 19:
        raise ValueError('changed per-result dependencies')
    kernel = (work / 'scalar-reader-kernel.log').read_text()
    for text in ['Constants/Inductives relying on type-in-type: <none>',
                 'Constants/Inductives relying on unsafe (co)fixpoints: <none>',
                 'Inductives whose positivity is assumed: <none>']:
        if kernel.count(text) != 1:
            raise ValueError('nonempty/missing unsafe category')
    if manifest['kernel']['exit_code'] != 0 or manifest['kernel']['status'] != 'terminal':
        raise ValueError('kernel run not terminal-successful')
    if manifest['full_acceptance'] or manifest['public_coverage_added'] != 0:
        raise ValueError('internal results mislabeled as public acceptance')
    return {'modules': 6, 'results': 31, 'closed': 19, 'types': 31,
            'non_tree_definitions': 23, 'diagnostic_computed_trees': 2,
            'actual_source_and_pinned_outputs_match': True,
            'kernel_terminal_exit_code': 0, 'full_acceptance': False, 'public_coverage_added': 0}


if __name__ == '__main__':
    cli = argparse.ArgumentParser()
    cli.add_argument('--work', type=Path, required=True)
    args = cli.parse_args()
    print(json.dumps(review(Path(__file__).resolve().parent, args.work), indent=2))
