"""Corrupt public square receipts, reports and boundaries in memory only."""
import copy
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
archive = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('square_public_test', archive / 'review.py')
review = importlib.util.module_from_spec(spec); spec.loader.exec_module(review)
manifest = json.loads((archive / 'manifest.json').read_text()); work = Path(manifest['scratch'])
results = [entry['module'] + '.' + name for entry in manifest['modules'] for name in entry['results']]
definitions = [entry['module'] + '.' + name for entry in manifest['modules'] for name in entry['definitions']]
expected = [('TYPE', name) for name in results] + [('DEF', name) for name in definitions + review.CRITICAL]
report = (work / 'square_public_contracts.out').read_text(); review.contracts(report, expected)
count = 0


def rejected(action):
    global count
    try:
        action()
    except ValueError:
        count += 1
    else:
        raise AssertionError('corrupted public evidence accepted')


for bad in [report + '...', report.replace('SQUARE_PUBLIC_TYPE ' + results[0], 'SQUARE_PUBLIC_TYPE wrong'),
            report + 'SQUARE_PUBLIC_DEF unexpected\n', report.replace('SQUARE_PUBLIC_TYPE ' + results[0], '', 1)]:
    rejected(lambda bad=bad: review.contracts(bad, expected))
entry = manifest['modules'][0]; source = (archive / (entry['file'] + '.source')).read_text()
review.inventory(source, entry)
for bad in [source.replace('Lemma canonical_scalar_square_step', 'Lemma wrong', 1),
            source + '\nDefinition unexpected := 0.\n']:
    rejected(lambda bad=bad: review.inventory(bad, entry))
normal = review.load('square_public_dep_test', archive.parent / 'scalar-multiply-integration/review-normal.py')
assumptions = (work / 'square_public_assumptions.out').read_text()
assert normal.assumptions(assumptions) == review.expected_dependencies(results)
for bad in [assumptions + 'JET_ASSUMPTIONS pending\n',
            assumptions + 'JET_ASSUMPTIONS ' + results[0] + '\nClosed under the global context\n',
            'Axioms:\nnew_axiom : True\n' + assumptions,
            assumptions.replace('Events.external_functions_sem\n', 'new_axiom\n', 1)]:
    rejected(lambda bad=bad: normal.assumptions(bad))
valid = json.loads((archive / 'REVIEW.json').read_text()); review.terminal(valid)
for key, value in [('public_jet_equivalence', False), ('actual_public_entry_copy_calls_return_free', False),
                   ('full_acceptance', True), ('checkout_coverage_added', 1), ('root', 'wrong')]:
    bad = copy.deepcopy(valid); bad[key] = value
    rejected(lambda bad=bad: review.terminal(bad))
for key in ['build', 'assumptions', 'contracts', 'kernel']:
    bad = copy.deepcopy(valid); bad[key]['exit_code'] = None
    rejected(lambda bad=bad: review.terminal(bad))

scanner = review.load('square_public_boundary_scanner', Path(manifest['dependency_coq']) / 'scan-jet-proofs.py')
root = scanner.code_only((work / 'jet_secp_scalar_square_local.v').read_text())
canonical = scanner.code_only((work / 'jet_secp_canonical_scalar_square.v').read_text())
haskell = (archive.parent.parent / 'Haskell/Core/Simplicity/Programs/LibSecp256k1.hs').read_text()
review.boundary(root, canonical, haskell)
for bad_root, bad_canonical, bad_haskell in [
        (root.replace('f_simplicity_scalar_square', 'f_simplicity_scalar_negate'), canonical, haskell),
        (root.replace('  secp_jet_local_spec', '  True -> secp_jet_local_spec', 1), canonical, haskell),
        (root.replace('(@canonical_scalar_square Alg.CoreFunSem)', '(@canonical_scalar_normalize Alg.CoreFunSem)'), canonical, haskell),
        (root, canonical.replace('iden &&& iden', 'iden &&& unit', 1), haskell),
        (root, canonical, haskell.replace('scalar_square = iden &&& iden >>> scalar_multiply', 'scalar_square = iden')),
        (root, canonical, haskell.replace('mkLib Sha256.Lib{..} = lib', 'different = lib')),
        (root, canonical, haskell + '\n  , scalar_square = iden &&& iden >>> scalar_multiply\n')]:
    rejected(lambda r=bad_root, c=bad_canonical, h=bad_haskell: review.boundary(r, c, h))
print(f'public square review: positive fixtures and {count} corruption fixtures passed; no inputs changed')
