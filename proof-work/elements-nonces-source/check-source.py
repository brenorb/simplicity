"""Selected canonical nonce serializer, indexed primitive, hash loop and C.

This source-fidelity check is separate from kernel/execution evidence and does
not establish the transaction builder's cached hash or host-library behavior.
"""
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


previous = load('nonces_inherited_source', HERE.parent / 'elements-outpoints-source/check-source.py')
compact, extract = previous.compact, previous.extract


def check(repo):
    repo = Path(repo)
    result = previous.check(repo)
    parser = load('nonces_parser', repo / 'Coq/check-secp-predicates-specification.py')
    model = load('nonces_fixed_model', HERE / 'source-model.py').MODEL
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
            raise ValueError('Elements nonce selected source differs: ' + label)

    def require(path, fragment):
        if compact(fragment) not in compact(read(path)):
            raise ValueError('Elements nonce binding/carrier differs: ' + path + ':' + fragment)

    def line(path, name, expected):
        found = re.findall(r'(?m)^\s*' + re.escape(name) + r'\s*=([^\n]*)$', read(path))
        if len(found) != 1:
            raise ValueError('missing/ambiguous Elements nonce clause: ' + name)
        equal(found[0], expected, path + ':' + name)

    for path, kind, name, expected in model['declarations']:
        equal(extract(read(path), kind, name), expected, path + ':' + name)
    for path, start, stop, expected in model['blocks']:
        code = read(path)
        if code.count(start) != 1 or code.count(stop) != 1:
            raise ValueError('missing/ambiguous Elements nonce block: ' + start)
        equal(code.split(start, 1)[1].split(stop, 1)[0], expected, path + ':' + start)
    prim = 'Haskell/Elements/Simplicity/Elements/Primitive.hs'
    catalog = 'Haskell/Simplicity/Elements/Jets.hs'
    for path, name, expected in [
        (catalog, 'specificationSigHash OutputNoncesHash', 'SigHash.outputNoncesHash'),
        ('Haskell/Simplicity/Elements/Programs/SigHash/Lib.hs', 'outputNoncesHash',
         'SigHash.outputNoncesHash SigHash.lib'),
        ('Haskell/Core/Simplicity/Programs/Elements/Lib.hs', 'nonceHash',
         'Elements.nonceHash Elements.libAssert'),
        (prim, 'primName OutputNonce', '"outputNonce"'),
        (prim, 'interpret OutputNonce', 'return . (atOutput $ encodeNonce . txoNonce)'),
        (prim, 'encodeNonce', 'cast . fmap (((toBit *** (toWord256 . toInteger)) +++ encodeHash) . nonce)'),
    ]:
        line(path, name, expected)
    for path, fragment in [
        (catalog, 'OutputNoncesHash :: SigHashJet () Word256'),
        (prim, 'OutputNonce :: Prim Word32 (S (S (Conf Word256)))'),
        ('Haskell/Elements/Simplicity/Elements/DataTypes.hs',
         'newtype Nonce = Nonce { nonce :: Either (Bool, Word256) Hash256 } deriving Show'),
        ('Haskell/Elements/Simplicity/Elements/DataTypes.hs', ', txoNonce :: Maybe Nonce'),
        ('Coq/C/jet_elements_prim.v', '| OutputNonce : prim Word32 (S (S (Conf Word256)))'),
    ]:
        require(path, fragment)
    found = re.findall(r'\bbool\s+simplicity_output_nonces_hash\s*'
        r'\(frameItem\* dst, frameItem src, const txEnv\* env\)\s*\{([^{}]*)\}',
        read('C/elements/elementsJets.c'), re.S)
    if len(found) != 1:
        raise ValueError('missing/ambiguous original C nonce getter')
    equal(found[0], '(void) src; writeHash(dst, &env->tx->outputNoncesHash); return true;', 'C getter')
    result['source_sha256'].update({str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(paths)})
    result.update(selected_jets=['Elements.OutputNoncesHash'], selected_primitives=['Elements.OutputNonce'],
        canonical_nonces_source_review_complete=True, whole_contracts_reviewed=True, original_c_getters=1,
        literal_nonce_serializer_reviewed=True, shared_tagged_absorber_reviewed=True,
        native_word256_payload=True, outer_and_inner_absence_distinct=True,
        caller_cached_hashes_established=False, formal_host_library_equivalence=False,
        kernel_checked_by_this_tool=False, normal_registration=False, coverage_added=0)
    return result


if __name__ == '__main__':
    print(json.dumps(check(Path(sys.argv[1]).resolve()), indent=2))
