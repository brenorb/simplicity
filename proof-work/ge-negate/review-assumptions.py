"""Read-only review of compiled affine helper sources and actual axiom reports.

Not a public jet contract, source fidelity or full acceptance certificate.
Uses the existing tested strict marker/assumption parser.
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
    for item in manifest['files']:
        archived = (archive / item['path']).read_bytes()
        materialized = (work / item['materialized_name']).read_bytes()
        if archived != materialized or hashlib.sha256(archived).hexdigest() != item['sha256']:
            raise ValueError('source hash mismatch: ' + item['path'])
        actual = re.findall(r'^(?:Lemma|Theorem)\s+(\w+)', archived.decode(), re.M)
        if actual != item['results']:
            raise ValueError('source declaration inventory mismatch: ' + item['path'])
        wanted.update('C.' + item['materialized_name'][:-2] + '.' + name for name in actual)
    if len(wanted) != 39 or len(manifest['files']) != 12:
        raise ValueError('unexpected helper inventory size')
    if (work / 'assumptions-review.err').read_text():
        raise ValueError('nonempty assumption diagnostics')
    spec = importlib.util.spec_from_file_location(
        'strict_assumption_parser', archive.parent / 'gej-predicate/review-preliminary.py')
    parser = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(parser)
    actual = parser.assumptions(work / 'assumptions-review.out', wanted)
    final = 'C.jet_secp_affine_negate_call.eval_affine_negate_point_output'
    expected_final = {
        'ClassicalDedekindReals.sig_forall_dec',
        'ClassicalDedekindReals.sig_not_dec',
        'Classical_Prop.classic',
        'Events.external_functions_sem',
        'Events.inline_assembly_sem',
        'FunctionalExtensionality.functional_extensionality_dep',
    }
    if actual[final] != expected_final:
        raise ValueError('unexpected final helper assumption set')
    if set().union(*actual.values()) != expected_final:
        raise ValueError('unexpected complete helper assumption union')
    if sum(not dependencies for dependencies in actual.values()) != 22:
        raise ValueError('unexpected closed-result inventory')
    return {
        'results': len(actual),
        'closed': sum(not dependencies for dependencies in actual.values()),
        'axiom_union': sorted(set().union(*actual.values())),
        'output_sha256': hashlib.sha256((work / 'assumptions-review.out').read_bytes()).hexdigest(),
        'assumptions': {name: sorted(dependencies) for name, dependencies in sorted(actual.items())},
        'full_acceptance': False,
        'public_coverage_added': 0,
    }


if __name__ == '__main__':
    args = argparse.ArgumentParser()
    args.add_argument('--archive', type=Path, default=Path(__file__).resolve().parent)
    args.add_argument('--work', type=Path, required=True)
    options = args.parse_args()
    print(json.dumps(review(options.archive, options.work), indent=2))
