"""Review complete public square equivalence; never registers/accepts main."""
import importlib.util
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
ARCHIVE = Path(__file__).resolve().parent
REPO = ARCHIVE.parent.parent
ROOT = 'SqLitC.jet_secp_scalar_square_local.scalar_square_literal_local_spec'
CRITICAL = ['C.jet_secp_normalize_local.secp_jet_local_spec',
            'C.jet_secp_canonical_scalar_negate.canonical_scalar_multiply']
EXECUTION = {
    'SqLitC.jet_secp_scalar_square_literal_owned.eval_scalar_square_literal_owned',
    'SqLitC.jet_secp_scalar_square_from_reader.eval_scalar_square_from_normalized_scalar',
    'SqLitC.jet_secp_scalar_square_call_chain.eval_scalar_read_square_write_canonical',
    'SqLitC.jet_secp_scalar_square_rest.exec_scalar_square_inplace',
    'SqLitC.jet_secp_scalar_square_rest.exec_scalar_square_rest_canonical',
    'SqLitC.jet_secp_scalar_square_lifecycle.eval_secp_scalar_square_canonical', ROOT,
}
NUMERIC = 'SqLitC.jet_secp_canonical_scalar_square.canonical_scalar_square_normalized_value'


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec); spec.loader.exec_module(module)
    return module


parent = load('square_public_function_review', ARCHIVE.parent / 'scalar-square-function/review.py')
digest, inventory = parent.digest, parent.inventory


def terminal(receipt):
    for name in ['build', 'assumptions', 'contracts', 'kernel']:
        if receipt[name]['exit_code'] != 0:
            raise ValueError('failed/nonterminal verification')
    if (receipt['root'] != ROOT or not receipt['public_jet_equivalence']
            or not receipt['actual_public_entry_copy_calls_return_free']):
        raise ValueError('complete literal public boundary missing')
    if receipt['full_acceptance'] or receipt['checkout_coverage_added'] != 0:
        raise ValueError('scratch proof is not registry/main acceptance')


def contracts(text, expected):
    if '...' in text or re.findall(r'(?m)^SQUARE_PUBLIC_(TYPE|DEF) (\S+)$', text) != expected:
        raise ValueError('truncated/missing/duplicate/reordered contract report')


def boundary(root, canonical, haskell):
    statement = re.search(r'Theorem scalar_square_literal_local_spec\s*:\s*(.*?)\.\s*Proof\.', root, re.S)
    want = 'secp_jet_local_spec f_simplicity_scalar_square (Word 8) (Word 8) (@canonical_scalar_square Alg.CoreFunSem)'
    if not statement or re.sub(r'\s+', '', statement[1]) != re.sub(r'\s+', '', want):
        raise ValueError('wrong/weakened public function, type, target or added premise')
    definition = re.search(r'Definition canonical_scalar_square\s*(.*?)\.\s*Lemma', canonical, re.S)
    want_def = '{term : Alg.Core.Algebra} : term (Word 8) (Word 8) := iden &&& iden >>> @canonical_scalar_multiply term'
    if not definition or re.sub(r'\s+', '', definition[1]) != re.sub(r'\s+', '', want_def):
        raise ValueError('literal duplicate-input multiplication term changed')
    parts = haskell.split('mkLib Sha256.Lib{..} = lib')
    if len(parts) != 2:
        raise ValueError('canonical Haskell mkLib boundary changed')
    if [line.strip() for line in parts[1].splitlines() if re.match(r'\s*, scalar_square\s*=', line)] != [
            ', scalar_square = iden &&& iden >>> scalar_multiply']:
        raise ValueError('canonical Haskell square field changed')


def expected_dependencies(results):
    if not EXECUTION | {NUMERIC} <= set(results):
        raise ValueError('missing execution/numeric result')
    return {name: parent.body.CLASSICAL | parent.body.SEMANTICS if name in EXECUTION else
            {'FunctionalExtensionality.functional_extensionality_dep'} if name == NUMERIC else set()
            for name in results}


def review():
    if not parent.review()['actual_r_equals_a_equals_b']:
        raise ValueError('shared-input function prerequisite changed')
    manifest = json.loads((ARCHIVE / 'manifest.json').read_text())
    receipt = json.loads((ARCHIVE / 'REVIEW.json').read_text()); terminal(receipt)
    work, base = Path(manifest['scratch']), Path(manifest['dependency_coq'])
    scanner = load('square_public_scanner', base / 'scan-jet-proofs.py')
    results, definitions = [], []
    for entry in manifest['modules']:
        path = ARCHIVE / (entry['file'] + '.source')
        if digest(path) != entry['sha256'] or path.read_bytes() != (work / entry['file']).read_bytes():
            raise ValueError('archive/compiled source drift')
        source = path.read_text(); inventory(source, entry)
        if re.search(r'\b(?:Axiom|Parameter|Admitted|admit)\b', scanner.code_only(source)):
            raise ValueError('assumed/skipped proof')
        results += [entry['module'] + '.' + name for name in entry['results']]
        definitions += [entry['module'] + '.' + name for name in entry['definitions']]
    if (len(manifest['modules']), len(results), len(definitions)) != (7, 16, 4):
        raise ValueError('unexpected public closure')
    for name, value in receipt['evidence_sha256'].items():
        if digest(work / name) != value:
            raise ValueError('source/compiled/driver/log drift: ' + name)
    for name in ['square_public_assumptions.v', 'square_public_contracts.v']:
        if (ARCHIVE / (name + '.source')).read_bytes() != (work / name).read_bytes():
            raise ValueError('driver drift')
    if any((work / name).read_bytes() for name in ['square_public_assumptions.err', 'square_public_contracts.err']):
        raise ValueError('compiler diagnostics')
    normal = load('square_public_dependencies', ARCHIVE.parent / 'scalar-multiply-integration/review-normal.py')
    checked = normal.assumptions((work / 'square_public_assumptions.out').read_text())
    if checked != expected_dependencies(results) or sum(not ds for ds in checked.values()) != 8:
        raise ValueError('exact dependency sets changed')
    contracts((work / 'square_public_contracts.out').read_text(),
              [('TYPE', name) for name in results] + [('DEF', name) for name in definitions + CRITICAL])
    boundary(scanner.code_only((work / 'jet_secp_scalar_square_local.v').read_text()),
             scanner.code_only((work / 'jet_secp_canonical_scalar_square.v').read_text()),
             (REPO / 'Haskell/Core/Simplicity/Programs/LibSecp256k1.hs').read_text())
    common = load('square_public_kernel', ARCHIVE.parent / 'scalar-mul/review.py')
    common.kernel((work / 'square_public_kernel.log').read_text(),
                  sorted((base / 'C/jet_coqchk_axioms.expected').read_text().split()))
    audit = load('square_public_inputs', base / 'jet-audit-inputs.py')
    if audit.fingerprint(base, REPO) != manifest['dependency_fingerprint']:
        raise ValueError('immutable dependency fingerprint changed')
    return {'root': ROOT, 'modules': 7, 'results': 16, 'closed_results': 8, 'definitions': 4,
            'explicit_critical_definitions': CRITICAL, 'public_jet_equivalence': True,
            'literal_duplicate_input_multiply_term': True, 'actual_public_entry_copy_calls_return_free': True,
            'exact_dependencies_and_kernel_context_match': True,
            'contract_report_bytes': (work / 'square_public_contracts.out').stat().st_size,
            'full_acceptance': False, 'checkout_coverage_added': 0}


if __name__ == '__main__':
    print(json.dumps(review(), indent=2))
