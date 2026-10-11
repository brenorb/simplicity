"""Recheck pinned evidence for an internal scalar helper, not acceptance."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def review(archive, work):
    manifest = json.loads((archive / 'manifest.json').read_text())
    actual_source = (work / manifest['file']).read_bytes()
    if (hashlib.sha256(actual_source).hexdigest() != manifest['source_sha256']
            or actual_source != (archive / manifest['source']).read_bytes()):
        raise ValueError('changed proof source')
    text = actual_source.decode()
    if re.findall(r'^(?:Lemma|Theorem)\s+(\w+)', text, re.M) != manifest['results']:
        raise ValueError('changed result inventory')
    if re.findall(r'^Definition\s+(\w+)', text, re.M) != manifest['definitions']:
        raise ValueError('changed definition inventory')
    if len(manifest['results']) != 20 or len(manifest['definitions']) != 17:
        raise ValueError('unexpected scope')
    if re.search(r'\b(?:admit|Admitted|Axiom|Parameter|vm_cast_no_check)\b', text):
        raise ValueError('unpermitted proof source construct')
    for driver in ['scalar_reduce_review.v', 'scalar_reduce_assumptions.v']:
        if (work / driver).read_bytes() != (archive / (driver + '.source')).read_bytes():
            raise ValueError('changed review driver: ' + driver)
    for filename, expected in manifest['output_hashes'].items():
        if digest(work / filename) != expected:
            raise ValueError('changed reviewed output: ' + filename)
    for filename in ['scalar-reduce-review.err', 'scalar-reduce-assumptions.err']:
        if (work / filename).read_bytes():
            raise ValueError('nonempty diagnostics: ' + filename)
    printed = (work / 'scalar-reduce-review.out').read_text()
    if '...' in printed:
        raise ValueError('truncated print')
    types = re.findall(r'^(\w+)\n\s+:', printed, re.M)
    definitions = re.findall(r'^(\w+) =', printed, re.M)
    if types != manifest['results'] or definitions != manifest['definitions']:
        raise ValueError('missing/duplicate/reordered contracts')
    spec = importlib.util.spec_from_file_location(
        'strict_assumptions', archive.parent / 'gej-predicate/review-preliminary.py')
    parser = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(parser)
    prefix = manifest['module'] + '.'
    wanted = {prefix + n for n in manifest['results']}
    actual = parser.assumptions(work / 'scalar-reduce-assumptions.out', wanted)
    classical = {'ClassicalDedekindReals.sig_forall_dec', 'ClassicalDedekindReals.sig_not_dec',
                 'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'}
    execution = classical | {'Events.external_functions_sem', 'Events.inline_assembly_sem'}
    expected = {name: set() for name in wanted}
    expected[prefix + 'scalar_reduce_output_loads'] = classical
    expected[prefix + 'eval_scalar_reduce_numeric'] = execution
    if actual != expected or sum(not a for a in actual.values()) != 18:
        raise ValueError('changed per-result dependencies')
    kernel = (work / 'scalar-reduce-kernel.log').read_text()
    unsafe = ['Constants/Inductives relying on type-in-type: <none>',
              'Constants/Inductives relying on unsafe (co)fixpoints: <none>',
              'Inductives whose positivity is assumed: <none>']
    if any(kernel.count(s) != 1 for s in unsafe):
        raise ValueError('missing/nonempty unsafe kernel category')
    if manifest['full_acceptance'] or manifest['public_coverage_added'] != 0:
        raise ValueError('internal evidence mislabeled as public acceptance')
    return {'results': 20, 'closed': 18, 'types': 20, 'definitions': 17,
            'source_and_pinned_outputs_match': True, 'kernel_session': 56508,
            'kernel_terminal_exit_code': manifest['kernel']['exit_code'],
            'full_acceptance': False, 'public_coverage_added': 0}


if __name__ == '__main__':
    cli = argparse.ArgumentParser()
    cli.add_argument('--work', type=Path, required=True)
    args = cli.parse_args()
    print(json.dumps(review(Path(__file__).resolve().parent, args.work), indent=2))
