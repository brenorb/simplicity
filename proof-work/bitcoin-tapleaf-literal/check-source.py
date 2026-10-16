"""Selected canonical TapLeaf source correspondence, not host-library proof.

The fixed reviewed model includes full typed Coq declarations and complete
Haskell program/helper blocks. Source snapshots alone are not acceptance.
The independent formal checker supplies execution/kernel/type evidence.
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


def extract(code, kind, name):
    head = r'\b(?:Definition|Fixpoint|Let|Record)\s+' if kind == 'declaration' else r'\b(?:Lemma|Theorem)\s+'
    end = r'.*?\.\s*(?=\n|$)' if kind == 'declaration' else r'.*?(?=\bProof\.)'
    matches = re.findall(head + re.escape(name) + r"(?![\w'])" + end, code, re.S)
    if len(matches) != 1:
        raise ValueError('missing/ambiguous tapleaf declaration: ' + name)
    return matches[0]


def check(repo):
    repo = Path(repo)
    coq = repo / 'Coq'
    # Reuse the reviewed literal traversal and four-limb unsigned hash decoder;
    # do not substitute unbounded integers for the actual Haskell Word256 fold.
    shared = load('tapleaf_shared_hash_decode', HERE.parent / 'elements-hash-literal/check-source.py')
    result = shared.check(repo, coq, coq / 'C/jet_haskell_hash_word.v', coq / 'C/jet_elements_hash_literal.v')
    parser = load('tapleaf_selected_parser', coq / 'check-secp-predicates-specification.py')
    model = json.loads((HERE / 'source-model.json').read_text())
    paths = set()

    def read(name):
        path = repo / name
        paths.add(path)
        if path.suffix == '.c':
            return re.sub(r'/\*.*?\*/|//[^\n]*', ' ', path.read_text(), flags=re.S)
        return parser.read_code(path)

    def equal(actual, expected, label):
        if parser.compact(actual) != parser.compact(expected):
            raise ValueError('tapleaf selected source differs: ' + label)

    def line(path, name, expected):
        found = re.findall(r'(?m)^\s*' + re.escape(name) + r'\s*=([^\n]*)$', read(path))
        if len(found) != 1:
            raise ValueError('missing/ambiguous tapleaf source clause: ' + name)
        equal(found[0], expected, name)

    for path, kind, name, expected in model['declarations']:
        equal(extract(read(path), kind, name), expected, path + ':' + name)
    for path, start, stop, expected in model['blocks']:
        code = read(path)
        if code.count(start) != 1 or code.count(stop) != 1:
            raise ValueError('missing/ambiguous tapleaf source block: ' + start)
        equal(code.split(start, 1)[1].split(stop, 1)[0], expected, path + ':' + start)

    catalog = 'Haskell/Simplicity/Bitcoin/Jets.hs'
    sig = 'Haskell/Simplicity/Bitcoin/Programs/SigHash.hs'
    sha = 'Haskell/Core/Simplicity/Programs/Sha256.hs'
    primitive = 'Haskell/Bitcoin/Simplicity/Bitcoin/Primitive.hs'
    digest = 'Haskell/Core/Simplicity/Digest.hs'
    for path, name, expected in [
        (catalog, 'specificationSigHash TapleafHash', 'SigHash.tapleafHash'),
        ('Haskell/Simplicity/Bitcoin/Programs/SigHash/Lib.hs', 'tapleafHash', 'SigHash.tapleafHash SigHash.lib'),
        (sig, 'lib', 'mkLib Sha256.lib Sha256.libAssert Transaction.lib'),
        (sha, 'libAssert', 'mkLibAssert lib'),
        (primitive, 'primPrefix', '"Bitcoin"'),
        (primitive, 'primName TapleafVersion', '"tapleafVersion"'),
        (primitive, 'primName ScriptCMR', '"scriptCMR"'),
        (primitive, 'element', 'const'),
        (primitive, 'interpret TapleafVersion', 'element . return . toWord8 . toInteger . tapleafVersion $ envTap env'),
        (primitive, 'interpret ScriptCMR', 'element . return . toWord256 . integerHash256 . tapScriptCMR $ envTap env'),
        (digest, 'noTagIv', 'IV sha256Incremental'),
        (digest, 'bsHash', 'bslHash . BSL.fromStrict'),
        (digest, 'bslHash', 'ivHash . IV . pushChunks sha256Incremental . padSHA1'),
        (digest, 'compress (IV state) (h1, h2)', 'IV $ state `pushChunk` BSS.fromShort (hash256 h1) `pushChunk` BSS.fromShort (hash256 h2)')]:
        line(path, name, expected)
    for path, fragment in [
        (catalog, 'TapleafHash :: SigHashJet () Word256'),
        (catalog, 'import qualified Simplicity.Bitcoin.Programs.SigHash.Lib as SigHash'),
        (sig, 'import qualified Simplicity.Programs.Sha256 as Sha256'),
        (primitive, 'TapleafVersion :: Prim () Word8'),
        (primitive, 'ScriptCMR :: Prim () Word256'),
        ('Haskell/Bitcoin/Simplicity/Bitcoin/DataTypes.hs', 'data TapEnv = TapEnv { tapleafVersion :: Word8'),
        ('Haskell/Bitcoin/Simplicity/Bitcoin/DataTypes.hs', ', tapScriptCMR :: Hash256'),
        (digest, 'import qualified Data.ByteString.Char8 as BSC'),
        (digest, 'import Simplicity.Digest.Pure.SHA'),
        ('Coq/Simplicity/Primitive/Bitcoin.v', '| ScriptCMR => fun _ => Some (from_hash256 (envScriptCMR e))'),
        ('Coq/C/jet_bitcoin_full_prim.v', 'Definition env := ext_environment.')]:
        parser.require(read(path), fragment, 'tapleaf binding/carrier')

    c = read('C/bitcoin/bitcoinJets.c')
    found = re.findall(r'\bbool\s+simplicity_bitcoin_tapleaf_hash\s*\([^)]*\)\s*\{([^{}]*)\}', c, re.S)
    if len(found) != 1:
        raise ValueError('missing/ambiguous C tapleaf getter')
    equal(found[0], '(void) src; writeHash(dst, &env->taproot->tapLeafHash); return true;', 'complete C getter')
    identity = load('tapleaf_primitive_identity', coq / 'check-bitcoin-primitive-identity.py')
    if identity.check(coq / 'C/jet_bitcoin_ext_prim.v', repo / primitive,
                      coq / 'Simplicity/Primitive/Bitcoin.v') != 8:
        raise ValueError('Bitcoin primitive identity inventory differs')
    result['source_sha256'].update({str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(paths)})
    result.update(selected_jets=['Bitcoin.TapleafHash'], selected_primitives=['Bitcoin.TapleafVersion', 'Bitcoin.ScriptCMR'],
        canonical_tapleaf_source_review_complete=True, whole_contracts_reviewed=True,
        selected_sha_helpers_reviewed=True, tagged_midstate_literal=True,
        caller_environment_construction_proved=False, formal_host_library_equivalence=False,
        normal_registration=False, coverage_added=0)
    return result


if __name__ == '__main__':
    print(json.dumps(check(Path(sys.argv[1]).resolve()), indent=2))
