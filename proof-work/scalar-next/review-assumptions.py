"""Read-only audit of actual scalar helper sources and dependency reports.

This is not a canonical source certificate or public scalar equivalence.
"""
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
    wanted = set()
    for entry in manifest['modules']:
        source = (work / entry['file']).read_bytes()
        if (hashlib.sha256(source).hexdigest() != entry['sha256']
                or (archive / entry['path']).read_bytes() != source):
            raise ValueError('source hash mismatch: ' + entry['file'])
        names = re.findall(r'^(?:Lemma|Theorem)\s+(\w+)', source.decode(), re.M)
        if names != entry['results']:
            raise ValueError('declaration inventory mismatch: ' + entry['file'])
        wanted.update('OriginalC.' + entry['file'][:-2] + '.' + name for name in names)
    if len(manifest['modules']) != 23 or len(wanted) != 86:
        raise ValueError('unexpected helper inventory')
    if (work / 'assumptions-review.err').read_text():
        raise ValueError('nonempty compiler diagnostics')
    spec = importlib.util.spec_from_file_location(
        'strict_parser', archive.parent / 'gej-predicate/review-preliminary.py')
    parser = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(parser)
    actual = parser.assumptions(work / 'assumptions-review.out', wanted)
    inherited = {'ClassicalDedekindReals.sig_forall_dec', 'ClassicalDedekindReals.sig_not_dec',
                 'Classical_Prop.classic', 'Events.external_functions_sem',
                 'Events.inline_assembly_sem', 'FunctionalExtensionality.functional_extensionality_dep'}
    if set().union(*actual.values()) != inherited or sum(not v for v in actual.values()) != 57:
        raise ValueError('unexpected complete dependency inventory')
    module = 'OriginalC.jet_secp_scalar_overflow_numeric.'
    if actual[module + 'scalar_overflow_matches_bound']:
        raise ValueError('numeric flag bound is not closed')
    if actual[module + 'eval_scalar_overflow_numeric'] != inherited:
        raise ValueError('unexpected new Clight theorem assumptions')
    prior = json.loads((archive / 'ASSUMPTION-REVIEW.json').read_text())
    normalized = {name: sorted(axioms) for name, axioms in sorted(actual.items())}
    if normalized != prior['assumptions']:
        raise ValueError('per-result sets changed since review')
    for name, digest in prior['log_hashes'].items():
        if hashlib.sha256((work / name).read_bytes()).hexdigest() != digest:
            raise ValueError('reviewed log changed: ' + name)
    return {'results': len(actual), 'closed': sum(not v for v in actual.values()),
            'axiom_union': sorted(inherited), 'actual_per_result_sets_match': True,
            'actual_source_hashes_match': 23, 'full_acceptance': False,
            'public_coverage_added': 0}


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--archive', type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument('--work', type=Path, required=True)
    args = parser.parse_args()
    print(json.dumps(review(args.archive, args.work), indent=2))
