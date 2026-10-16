"""Canonical Elements tapleaf tag/program/primitive/C source correspondence.

No host SHA/Haskell library proof or caller-cache construction is claimed.
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


stream = load('elements_tapleaf_stream_source', HERE.parent / 'elements-stream-source/check-source.py')
compact, extract = stream.compact, stream.extract


def check(repo):
    repo = Path(repo)
    result = stream.check(repo)
    parser = load('elements_tapleaf_parser', repo / 'Coq/check-secp-predicates-specification.py')
    model = load('elements_tapleaf_fixed_model', HERE / 'source-model.py').MODEL
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
            raise ValueError('Elements tapleaf selected source differs: ' + label)

    def require(path, fragment):
        if compact(fragment) not in compact(read(path)):
            raise ValueError('Elements tapleaf binding/carrier differs: ' + path + ':' + fragment)

    def line(path, name, expected):
        found = re.findall(r'(?m)^\s*' + re.escape(name) + r'\s*=([^\n]*)$', read(path))
        if len(found) != 1:
            raise ValueError('missing/ambiguous Elements tapleaf clause: ' + name)
        equal(found[0], expected, path + ':' + name)

    for path, kind, name, expected in model['declarations']:
        equal(extract(read(path), kind, name), expected, path + ':' + name)
    for path, start, stop, expected in model['blocks']:
        code = read(path)
        if code.count(start) != 1 or code.count(stop) != 1:
            raise ValueError('missing/ambiguous Elements tapleaf block: ' + start)
        equal(code.split(start, 1)[1].split(stop, 1)[0], expected, path + ':' + start)

    catalog = 'Haskell/Simplicity/Elements/Jets.hs'
    wrapper = 'Haskell/Simplicity/Elements/Programs/SigHash/Lib.hs'
    prim = 'Haskell/Elements/Simplicity/Elements/Primitive.hs'
    digest = 'Haskell/Core/Simplicity/Digest.hs'
    for path, name, expected in [
        (catalog, 'specificationSigHash TapleafHash', 'SigHash.tapleafHash'),
        (wrapper, 'tapleafHash', 'SigHash.tapleafHash SigHash.lib'),
        (prim, 'primName TapleafVersion', '"tapleafVersion"'),
        (prim, 'primName ScriptCMR', '"scriptCMR"'),
        (prim, 'element', 'const'),
        (prim, 'interpret TapleafVersion', 'element . return . toWord8 . toInteger . tapleafVersion $ envTap env'),
        (prim, 'interpret ScriptCMR', 'element . return . encodeHash . tapScriptCMR $ envTap env'),
        (digest, 'noTagIv', 'IV sha256Incremental'),
        (digest, 'bsHash', 'bslHash . BSL.fromStrict'),
        (digest, 'bslHash', 'ivHash . IV . pushChunks sha256Incremental . padSHA1'),
        (digest, 'compress (IV state) (h1, h2)',
         'IV $ state `pushChunk` BSS.fromShort (hash256 h1) `pushChunk` BSS.fromShort (hash256 h2)'),
    ]:
        line(path, name, expected)
    for path, fragment in [
        (catalog, 'TapleafHash :: SigHashJet () Word256'),
        (prim, 'TapleafVersion :: Prim () Word8'), (prim, 'ScriptCMR :: Prim () Word256'),
        (digest, 'import qualified Data.ByteString.Char8 as BSC'),
        (digest, 'import Simplicity.Digest.Pure.SHA'),
        ('Coq/C/jet_elements_prim.v', '| TapleafVersion : prim Unit Word8'),
        ('Coq/C/jet_elements_prim.v', '| ScriptCMR : prim Unit Word256'),
    ]:
        require(path, fragment)
    c = read('C/elements/elementsJets.c')
    found = re.findall(r'\bbool\s+simplicity_tapleaf_hash\s*'
        r'\(frameItem\* dst, frameItem src, const txEnv\* env\)\s*\{([^{}]*)\}', c, re.S)
    if len(found) != 1:
        raise ValueError('missing/ambiguous complete original Elements tapleaf getter')
    equal(found[0], '(void) src; writeHash(dst, &env->taproot->tapLeafHash); return true;', 'C getter')
    result['source_sha256'].update({str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(paths)})
    result.update(selected_jets=['Elements.TapleafHash'],
        selected_primitives=['Elements.TapleafVersion', 'Elements.ScriptCMR'],
        canonical_tapleaf_source_review_complete=True, tagged_midstate_literal=True,
        whole_contracts_reviewed=True, original_c_getters=1,
        selected_sha_tag_helpers_reviewed=True, caller_cached_hashes_established=False,
        formal_host_library_equivalence=False, kernel_checked_by_this_tool=False,
        normal_registration=False, coverage_added=0)
    return result


if __name__ == '__main__':
    print(json.dumps(check(Path(sys.argv[1]).resolve()), indent=2))
