"""Corrupt helper evidence in memory, never mutate frozen proof/audit inputs."""
import copy
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
archive = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('lambda_test', archive / 'review.py')
review = importlib.util.module_from_spec(spec); spec.loader.exec_module(review)
manifest = json.loads((archive / 'manifest.json').read_text())
receipt = json.loads((archive / 'REVIEW.json').read_text())
count = 0


def rejected(action):
    global count
    try:
        action()
    except ValueError:
        count += 1
    else:
        raise AssertionError('corrupted lambda evidence accepted')


for group in ['global', 'literal']:
    work = Path(manifest['scratch'][group]); entries = [e for e in manifest['modules'] if e['group'] == group]
    rs = [e['module'] + '.' + n for e in entries for n in e['results']]
    ds = [e['module'] + '.' + n for e in entries for n in e['definitions']]
    expected = [('TYPE', n) for n in rs] + [('DEF', n) for n in ds]
    prefix = 'LAMBDA_' + group.upper(); report = (work / ('lambda_' + group + '_contracts.out')).read_text()
    review.contracts(report, expected, prefix)
    for bad in [report + '...', report.replace(prefix + '_TYPE ' + rs[0], prefix + '_TYPE wrong', 1),
                report + prefix + '_DEF unexpected\n', report.replace(prefix + '_TYPE ' + rs[0], '', 1)]:
        rejected(lambda bad=bad: review.contracts(bad, expected, prefix))
    for kind in ['build', 'assumptions', 'contracts', 'kernel']:
        bad = copy.deepcopy(receipt); bad[group][kind]['exit_code'] = None
        rejected(lambda bad=bad: review.terminal(bad))
review.terminal(receipt)
for key, value in [('public_jet_equivalence', True), ('full_acceptance', True), ('checkout_coverage_added', 1),
                   ('actual_init_mem_implies_readonly_rep', False), ('literal_specification_retained', False)]:
    bad = copy.deepcopy(receipt); bad[key] = value
    rejected(lambda bad=bad: review.terminal(bad))
repo = archive.parent.parent
source = (archive / 'jet_secp_canonical_scalar_lambda.v.source').read_text()
global_source = (archive / 'jet_secp_scalar_lambda_global.v.source').read_text()
program = (repo / 'Haskell/Core/Simplicity/Programs/LibSecp256k1.hs').read_text()
specification = (repo / 'Haskell/Core/Simplicity/LibSecp256k1/Spec.hs').read_text()
review.literal_source(source, global_source, program, specification)
for bad in [source.replace('Alg.scribe canonical_lambda_word', 'Alg.iden'),
            source.replace('(unit >>> @canonical_scalar_lambda term) &&& iden',
                           'iden &&& (unit >>> @canonical_scalar_lambda term)'),
            source.replace('>>> @canonical_scalar_multiply term.', '>>> Alg.iden.')]:
    rejected(lambda bad=bad: review.literal_source(bad, global_source, program, specification))
rejected(lambda: review.literal_source(source, global_source.replace('3771808036315599690', '3771808036315599691'),
                                       program, specification))
rejected(lambda: review.literal_source(source, global_source, program,
                                       specification.replace('lambda = 0x5363ad4c', 'lambda = 0x5363ad4d')))
all_results = [e['module'] + '.' + n for e in manifest['modules'] for n in e['results']]
rejected(lambda: review.expected_dependencies(all_results[:-1]))
print(f'lambda helper review: positive fixtures and {count} corruption fixtures passed; no inputs changed')
