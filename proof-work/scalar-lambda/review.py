"""Review original global/literal adapters; this is not public jet acceptance."""
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


shared = load('lambda_shared', ARCHIVE.parent / 'scalar-square-alias/review.py')
digest, inventory = shared.digest, shared.inventory
REPRESENTATION = {
    'LambdaC.jet_secp_scalar_lambda_global.scalar_lambda_global_initializes',
    'LambdaC.jet_secp_scalar_lambda_global.scalar_lambda_global_readonly_initial',
    'LambdaC.jet_secp_scalar_lambda_global.scalar_lambda_global_unchanged',
    'LambdaC.jet_secp_scalar_lambda_region.scalar_lambda_borrowed_region',
    'LambdaC.jet_secp_scalar_lambda_region.scalar_lambda_global_allocated',
}
EXTENSIONAL = {
    'LamSpecC.jet_secp_canonical_scalar_lambda.canonical_scalar_multiply_lambda_numeric',
    'LamSpecC.jet_secp_canonical_scalar_lambda.canonical_scalar_multiply_lambda_c_order',
}


def expected_dependencies(results):
    if not REPRESENTATION | EXTENSIONAL <= set(results):
        raise ValueError('required global/literal bridges missing')
    return {n: shared.CLASSICAL if n in REPRESENTATION else
            {'FunctionalExtensionality.functional_extensionality_dep'} if n in EXTENSIONAL else set()
            for n in results}


def contracts(text, expected, prefix):
    if '...' in text or re.findall(r'(?m)^' + prefix + r'_(TYPE|DEF) (\S+)$', text) != expected:
        raise ValueError('truncated/missing/duplicate/reordered report')


def terminal(receipt):
    for group in ['global', 'literal']:
        for name in ['build', 'assumptions', 'contracts', 'kernel']:
            if receipt[group][name]['exit_code'] != 0:
                raise ValueError('failed/nonterminal verification')
    if receipt['public_jet_equivalence'] or receipt['full_acceptance'] or receipt['checkout_coverage_added']:
        raise ValueError('helpers are not public lambda acceptance')
    if not receipt['actual_init_mem_implies_readonly_rep'] or not receipt['literal_specification_retained']:
        raise ValueError('original global/literal boundary missing')


def literal_source(source, global_source, program, specification):
    compact = lambda s: re.sub(r'\s+', '', s)
    if 'scalar_lambda=scribe256LibSecp256k1.lambda' not in compact(program):
        raise ValueError('pinned scalar_lambda source changed')
    if 'scalar_multiply_lambda=(unit>>>scalar_lambda)&&&iden>>>scalar_multiply' not in compact(program):
        raise ValueError('pinned multiply_lambda structure changed')
    match = re.search(r'(?m)^lambda\s*=\s*0x([0-9a-fA-F]+)\s*$', specification)
    value = re.search(r'Definition canonical_lambda_value\s*:\s*Z\s*:=\s*(\d+)\s*\.', global_source)
    if not match or not value or int(match[1], 16) != int(value[1]):
        raise ValueError('literal lambda value mismatch')
    required = [
        'Definition canonical_lambda_word : Ty.tySem (Word 8) := @fromZ (WordToZ 8) canonical_lambda_value.',
        'Definition canonical_scalar_lambda {term : Alg.Core.Algebra} : term Ty.Unit (Word 8) := Alg.scribe canonical_lambda_word.',
        'Definition canonical_scalar_multiply_lambda {term : Alg.Core.Algebra} : term (Word 8) (Word 8) := (unit >>> @canonical_scalar_lambda term) &&& iden >>> @canonical_scalar_multiply term.',
    ]
    if any(compact(s) not in compact(source) for s in required):
        raise ValueError('literal term replaced/reordered')


def review():
    manifest = json.loads((ARCHIVE / 'manifest.json').read_text())
    receipt = json.loads((ARCHIVE / 'REVIEW.json').read_text()); terminal(receipt)
    base = Path(manifest['dependency_coq'])
    load('lambda_borrowed_parent', ARCHIVE.parent / 'scalar-mul-borrowed-function/review.py').review()
    scanner = load('lambda_scanner', base / 'scan-jet-proofs.py')
    results, definitions = [], []
    grouped = {'global': ([], []), 'literal': ([], [])}
    for entry in manifest['modules']:
        work = Path(manifest['scratch'][entry['group']]); path = ARCHIVE / (entry['file'] + '.source')
        if digest(path) != entry['sha256'] or path.read_bytes() != (work / entry['file']).read_bytes():
            raise ValueError('archived/compiled source drift')
        source = path.read_text(); inventory(source, entry)
        if re.search(r'\b(?:Axiom|Parameter|Admitted|admit)\b', scanner.code_only(source)):
            raise ValueError('assumed/skipped proof')
        rs = [entry['module'] + '.' + n for n in entry['results']]
        ds = [entry['module'] + '.' + n for n in entry['definitions']]
        results += rs; definitions += ds
        grouped[entry['group']][0].extend(rs); grouped[entry['group']][1].extend(ds)
    if (len(manifest['modules']), len(results), len(definitions)) != (3, 20, 8):
        raise ValueError('unexpected lambda helper closure')
    literal_source((ARCHIVE / 'jet_secp_canonical_scalar_lambda.v.source').read_text(),
                   (ARCHIVE / 'jet_secp_scalar_lambda_global.v.source').read_text(),
                   (REPO / 'Haskell/Core/Simplicity/Programs/LibSecp256k1.hs').read_text(),
                   (REPO / 'Haskell/Core/Simplicity/LibSecp256k1/Spec.hs').read_text())
    normal = load('lambda_deps', ARCHIVE.parent / 'scalar-multiply-integration/review-normal.py')
    common = load('lambda_kernel', ARCHIVE.parent / 'scalar-mul/review.py')
    expected = expected_dependencies(results)
    deps = {}
    for group in ['global', 'literal']:
        work = Path(manifest['scratch'][group]); stem = 'lambda_' + group
        for name, value in receipt[group]['evidence_sha256'].items():
            if digest(work / name) != value:
                raise ValueError('source/object/driver/report/log drift: ' + name)
        for name in [stem + '_assumptions.v', stem + '_contracts.v']:
            if (ARCHIVE / (name + '.source')).read_bytes() != (work / name).read_bytes():
                raise ValueError('driver drift')
        if any((work / (stem + '_' + n + '.err')).read_bytes() for n in ['assumptions', 'contracts']):
            raise ValueError('compiler diagnostics')
        rs, ds = grouped[group]
        parsed = normal.assumptions((work / (stem + '_assumptions.out')).read_text())
        if parsed != {n: expected[n] for n in rs}:
            raise ValueError('exact per-result dependencies changed')
        deps.update(parsed)
        contracts((work / (stem + '_contracts.out')).read_text(),
                  [('TYPE', n) for n in rs] + [('DEF', n) for n in ds], 'LAMBDA_' + group.upper())
        common.kernel((work / (stem + '_kernel.log')).read_text(),
                      sorted((base / 'C/jet_coqchk_axioms.expected').read_text().split()))
    audit = load('lambda_inputs', base / 'jet-audit-inputs.py')
    if audit.fingerprint(base, REPO) != manifest['dependency_fingerprint']:
        raise ValueError('immutable base drift')
    return {'modules': 3, 'results': 20, 'closed_results': sum(not ds for ds in deps.values()),
            'definitions': 8, 'actual_init_mem_implies_readonly_rep': True,
            'literal_specification_retained': True, 'c_operand_order_bridge': True,
            'public_jet_equivalence': False, 'full_acceptance': False, 'checkout_coverage_added': 0}


if __name__ == '__main__':
    print(json.dumps(review(), indent=2))
