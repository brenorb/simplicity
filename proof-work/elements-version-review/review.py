"""Review the independently checked selected Elements Version milestone."""
import importlib.util
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
ARCHIVE = Path(__file__).resolve().parent
REPO = ARCHIVE.parent.parent


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec); spec.loader.exec_module(module)
    return module


normal = load('elements_version_reports', ARCHIVE.parent / 'scalar-multiply-integration/review-normal.py')
common = load('elements_version_kernel', ARCHIVE.parent / 'scalar-mul/review.py')


def terminal(receipt):
    for field in ['build', 'assumptions', 'contracts', 'kernel', 'AST_regeneration',
                  'selected_semantics', 'source_mutations']:
        if receipt[field]['exit_code'] != 0:
            raise ValueError('nonterminal/failed Version evidence: ' + field)
    if (not receipt['AST_regeneration']['byte_identical']
            or not receipt['selected_semantics']['only_selected_clause_reviewed']
            or not receipt['selected_semantics']['other_30_semantics_not_claimed']
            or receipt['normal_registration'] or receipt['full_acceptance']
            or receipt['checkout_coverage_added']):
        raise ValueError('milestone scope/AST boundary changed')


def contracts(text, wanted):
    if '...' in text or re.findall(r'(?m)^ELEMENTS_VERSION_(TYPE|DEF) (\S+)$', text) != wanted:
        raise ValueError('truncated/missing/duplicate/reordered Version records')


def review():
    sourcing = json.loads((ARCHIVE / 'SOURCING.json').read_text())
    receipt = json.loads((ARCHIVE / 'REVIEW.json').read_text()); terminal(receipt)
    work, base = Path(sourcing['candidate']), Path(sourcing['baseline_coq'])
    stage = load('elements_version_frozen_sources', ARCHIVE / 'stage-version.py')
    if stage.stage(work, verify=True) != sourcing:
        raise ValueError('committed source/closure provenance drift')
    for path, value in receipt['evidence_sha256'].items():
        if normal.sha(work / path) != value:
            raise ValueError('source/object/driver/report/log drift: ' + path)
    for kind in ['assumptions', 'contracts']:
        if (work / ('version_' + kind + '.err')).read_bytes():
            raise ValueError('compiler diagnostics')
    results = [e['module'] + '.' + n for e in sourcing['modules'] for n in e['results']]
    wanted_deps = {k: set(v) for k, v in receipt['expected_dependencies'].items()}
    parsed = normal.assumptions((work / 'version_assumptions.out').read_text())
    if (parsed != wanted_deps or set(parsed) != set(results) or len(parsed) != 34
            or sum(not ds for ds in parsed.values()) != 16):
        raise ValueError('exact result/dependency inventory changed')
    # Only the four classical parameters and two existing semantics parameters occur.
    inherited_six = normal.INHERITED - {'Events.external_functions_properties', 'Events.inline_assembly_properties'}
    if any(ds - inherited_six for ds in parsed.values()):
        raise ValueError('new Version dependency')
    contracts((work / 'version_contracts.out').read_text(),
              [('TYPE', n) for n in results] + [('DEF', n) for n in receipt['contracts']['definitions']])
    common.kernel((work / 'version_kernel.log').read_text(),
                  sorted((base / 'C/jet_coqchk_axioms.expected').read_text().split()))
    actual_ast = work / 'Coq/C/jets_elements.v'
    generated = Path(receipt['AST_regeneration']['generated_file'])
    if (actual_ast.read_bytes() != generated.read_bytes()
            or normal.sha(generated) != receipt['AST_regeneration']['generated_sha256']):
        raise ValueError('original-program AST comparison drift')
    source = load('elements_version_selected_correspondence', ARCHIVE / 'check-version-source.py')
    source.check(REPO, work / 'Coq')
    return {'modules': 13, 'results': 34, 'closed_results': 16, 'records': 38,
            'selected_primitive': 'Elements.Version', 'root_kernel_checked': True,
            'original_AST_regeneration_matches': True, 'other_30_semantics_reviewed': False,
            'normal_registration': False, 'full_acceptance': False, 'checkout_coverage_added': 0}


if __name__ == '__main__':
    print(json.dumps(review(), indent=2))

