"""Canonical Elements issuanceRangeProofsHash loop, proof-view boundary and C."""
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent


def load(name, path):
    sp = importlib.util.spec_from_file_location(name, path)
    m = importlib.util.module_from_spec(sp)
    sp.loader.exec_module(m)
    return m


stream = load('elements_issuance_proofs_component_source', HERE.parent / 'elements-stream-source/check-source.py')
compact, extract = stream.compact, stream.extract


def check(repo):
    repo = Path(repo)
    result = stream.check(repo)
    parser = load('elements_issuance_proofs_parser', repo / 'Coq/check-secp-predicates-specification.py')
    model = load('elements_issuance_proofs_fixed_model', HERE / 'source-model.py').MODEL
    paths, cache = set(), {}

    def read(name):
        path = repo / name
        paths.add(path)
        if path not in cache:
            cache[path] = (re.sub(r'/\*.*?\*/|//[^\n]*', ' ', path.read_text(), flags=re.S)
                           if path.suffix == '.c' else parser.read_code(path))
        return cache[path]

    def equal(actual, expected, label):
        if compact(actual) != compact(expected):
            raise ValueError('Elements issuance range-proofs selected source differs: ' + label)

    def line(path, name, expected):
        found = re.findall(r'(?m)^\s*' + re.escape(name) + r'\s*=([^\n]*)$', read(path))
        if len(found) != 1:
            raise ValueError('missing/ambiguous Elements issuance range-proofs clause: ' + name)
        equal(found[0], expected, path + ':' + name)

    for path, kind, name, expected in model['declarations']:
        equal(extract(read(path), kind, name), expected, path + ':' + name)
    for path, start, stop, expected in model['blocks']:
        code = read(path)
        if code.count(start) != 1 or code.count(stop) != 1:
            raise ValueError('missing/ambiguous Elements issuance range-proofs composition block')
        equal(code.split(start, 1)[1].split(stop, 1)[0], expected, path + ':' + start)
    catalog = 'Haskell/Simplicity/Elements/Jets.hs'
    wrapper = 'Haskell/Simplicity/Elements/Programs/SigHash/Lib.hs'
    line(catalog, 'specificationSigHash IssuanceRangeProofsHash', 'SigHash.issuanceRangeProofsHash')
    line(wrapper, 'issuanceRangeProofsHash', 'SigHash.issuanceRangeProofsHash SigHash.lib')
    if compact('IssuanceRangeProofsHash :: SigHashJet () Word256') not in compact(read(catalog)):
        raise ValueError('Elements issuance range-proofs catalog type differs')
    c = read('C/elements/elementsJets.c')
    found = re.findall(r'\bbool\s+simplicity_issuance_range_proofs_hash\s*'
        r'\(frameItem\* dst, frameItem src, const txEnv\* env\)\s*\{([^{}]*)\}', c, re.S)
    if len(found) != 1:
        raise ValueError('missing/ambiguous complete original Elements issuance range-proofs getter')
    equal(found[0], '(void) src; writeHash(dst, &env->tx->issuanceRangeProofsHash); return true;', 'C getter')
    result['source_sha256'].update({str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(paths)})
    result.update(selected_jets=['Elements.IssuanceRangeProofsHash'],
        selected_primitives=['Elements.IssuanceAssetProof', 'Elements.IssuanceTokenProof'],
        canonical_issuance_proofs_source_review_complete=True, literal_two_primitive_body_reviewed=True,
        generic_body_bridge_source_reviewed=True, whole_contracts_reviewed=True, original_c_getters=1,
        caller_cached_hashes_established=False, formal_host_library_equivalence=False,
        kernel_checked_by_this_tool=False, normal_registration=False, coverage_added=0)
    return result


if __name__ == '__main__':
    print(json.dumps(check(Path(sys.argv[1]).resolve()), indent=2))
