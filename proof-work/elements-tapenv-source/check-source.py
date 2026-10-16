"""Elements tapEnvHash program/C correspondence with the native key boundary."""
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


leaf = load('elements_tapenv_leaf_source', HERE.parent / 'elements-tapleaf-source/check-source.py')
compact, extract = leaf.compact, leaf.extract


def check(repo):
    repo = Path(repo)
    result = leaf.check(repo)
    parser = load('elements_tapenv_parser', repo / 'Coq/check-secp-predicates-specification.py')
    model = load('elements_tapenv_fixed_model', HERE / 'source-model.py').MODEL
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
            raise ValueError('Elements tapenv selected source differs: ' + label)

    def require(path, fragment):
        if compact(fragment) not in compact(read(path)):
            raise ValueError('Elements tapenv binding/carrier differs: ' + path + ':' + fragment)

    def line(path, name, expected):
        found = re.findall(r'(?m)^\s*' + re.escape(name) + r'\s*=([^\n]*)$', read(path))
        if len(found) != 1:
            raise ValueError('missing/ambiguous Elements tapenv clause: ' + name)
        equal(found[0], expected, path + ':' + name)

    for path, kind, name, expected in model['declarations']:
        equal(extract(read(path), kind, name), expected, path + ':' + name)
    for path, start, stop, expected in model['blocks']:
        code = read(path)
        if code.count(start) != 1 or code.count(stop) != 1:
            raise ValueError('missing/ambiguous Elements tapenv block: ' + start)
        equal(code.split(start, 1)[1].split(stop, 1)[0], expected, path + ':' + start)

    catalog = 'Haskell/Simplicity/Elements/Jets.hs'
    wrapper = 'Haskell/Simplicity/Elements/Programs/SigHash/Lib.hs'
    prim = 'Haskell/Elements/Simplicity/Elements/Primitive.hs'
    native = 'Haskell/Core/Simplicity/LibSecp256k1/Schnorr.hs'
    spec = 'Haskell/Core/Simplicity/LibSecp256k1/Spec.hs'
    for path, name, expected in [
        (catalog, 'specificationSigHash TapEnvHash', 'SigHash.tapEnvHash'),
        (wrapper, 'tapEnvHash', 'SigHash.tapEnvHash SigHash.lib'),
        (prim, 'primName InternalKey', '"internalKey"'),
        (prim, 'interpret InternalKey', 'element . return . encodeKey . tapInternalKey $ envTap env'),
        (prim, 'encodeKey (Schnorr.PubKey x)', 'toWord256 . toInteger $ x'),
    ]:
        line(path, name, expected)
    for path, fragment in [
        (catalog, 'TapEnvHash :: SigHashJet () Word256'),
        (prim, 'InternalKey :: Prim () PubKey'),
        (prim, 'import qualified Simplicity.LibSecp256k1.Schnorr as Schnorr'),
        (prim, 'import qualified Simplicity.LibSecp256k1.Spec as Schnorr'),
        (native, 'data PubKey = PubKey Word256'), (native, 'import Simplicity.Word'),
        (spec, 'import Simplicity.LibSecp256k1.Schnorr'),
        ('Haskell/Core/Simplicity/Ty/LibSecp256k1.hs', 'type PubKey = Word256'),
        ('Haskell/Core/Simplicity/Programs/LibSecp256k1.hs', 'import Simplicity.Ty.LibSecp256k1'),
        ('Haskell/Elements/Simplicity/Elements/DataTypes.hs', 'import Simplicity.LibSecp256k1.Schnorr'),
        ('Coq/C/jet_elements_prim.v', '| InternalKey : prim Unit Word256'),
    ]:
        require(path, fragment)
    if re.search(r'\b(?:data|newtype|type)\s+PubKey\b', read(spec)):
        raise ValueError('Spec shadows the imported native-word PubKey')
    c = read('C/elements/elementsJets.c')
    found = re.findall(r'\bbool\s+simplicity_tap_env_hash\s*'
        r'\(frameItem\* dst, frameItem src, const txEnv\* env\)\s*\{([^{}]*)\}', c, re.S)
    if len(found) != 1:
        raise ValueError('missing/ambiguous complete original Elements tapenv getter')
    equal(found[0], '(void) src; writeHash(dst, &env->taproot->tapEnvHash); return true;', 'C getter')
    result['source_sha256'].update({str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(paths)})
    result.update(selected_jets=['Elements.TapEnvHash'],
        selected_primitives=['Elements.TapleafVersion', 'Elements.ScriptCMR', 'Elements.Tappath', 'Elements.InternalKey'],
        canonical_tapenv_source_review_complete=True, native_word_internal_key=True,
        field_or_point_validity_not_assumed=True, whole_contracts_reviewed=True, original_c_getters=1,
        caller_cached_hashes_established=False, formal_host_library_equivalence=False,
        kernel_checked_by_this_tool=False, normal_registration=False, coverage_added=0)
    return result


if __name__ == '__main__':
    print(json.dumps(check(Path(sys.argv[1]).resolve()), indent=2))
