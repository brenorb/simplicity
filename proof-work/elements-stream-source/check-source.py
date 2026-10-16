"""Selected Elements hash-word program/primitive/whole-C source fidelity.

The actual formal endpoint, dependency and kernel evidence is separate. This
guard does not verify host Haskell/lens/crypto libraries or C cache builders.
"""
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
JETS = [
    ('output_scripts_hash', 'outputScriptsHash', 'OutputScriptHash', 'tx->outputScriptsHash'),
    ('output_range_proofs_hash', 'outputRangeProofsHash', 'OutputRangeProof', 'tx->outputRangeProofsHash'),
    ('output_surjection_proofs_hash', 'outputSurjectionProofsHash', 'OutputSurjectionProof', 'tx->outputSurjectionProofsHash'),
    ('input_scripts_hash', 'inputScriptsHash', 'InputScriptHash', 'tx->inputScriptsHash'),
    ('input_sequences_hash', 'inputSequencesHash', 'InputSequence', 'tx->inputSequencesHash'),
    ('input_script_sigs_hash', 'inputScriptSigsHash', 'InputScriptSigHash', 'tx->inputScriptSigsHash'),
    ('tappath_hash', 'tappathHash', 'Tappath', 'taproot->tappathHash'),
]
PRIMITIVES = {
    'OutputScriptHash': 'return . (atOutput $ encodeHash . bslHash . txoScript)',
    'OutputRangeProof': 'return . (atOutput $ encodeHash . bslHash . view (to txoAmount.under amount.prf_))',
    'OutputSurjectionProof': 'return . (atOutput $ encodeHash . bslHash . view (to txoAsset.under asset.prf_))',
    'InputScriptHash': 'return . (atInput $ encodeHash . bslHash . utxoScript . sigTxiTxo)',
    'InputSequence': 'return . (atInput $ toWord32 . toInteger . sigTxiSequence)',
    'InputScriptSigHash': 'return . (atInput $ encodeHash . bslHash . sigTxiScriptSig)',
    'Tappath': 'return . cast . fmap encodeHash . listToMaybe . flip drop (tappath (envTap env)) . fromInteger . fromWord8',
}


def load(name, path):
    sp = importlib.util.spec_from_file_location(name, path)
    m = importlib.util.module_from_spec(sp)
    sp.loader.exec_module(m)
    return m


def compact(text):
    # Ignore layout outside strings, not whitespace inside primitive names/tags.
    parts = re.split(r'("(?:\\.|[^"\\])*")', text)
    return ''.join(part if part.startswith('"') else re.sub(r'\s+', '', part) for part in parts)


def extract(code, kind, name):
    if kind == 'declaration':
        pattern = r'\b(?:Definition|Fixpoint|Let|Record)\s+' + re.escape(name) + r"(?![\w']).*?\.\s*(?=\n|$)"
    elif kind == 'statement':
        pattern = r'\b(?:Lemma|Theorem)\s+' + re.escape(name) + r"(?![\w']).*?(?=\bProof\.)"
    else:
        raise ValueError('unknown Elements stream declaration kind')
    found = re.findall(pattern, code, re.S)
    if len(found) != 1:
        raise ValueError('missing/ambiguous Elements stream declaration: ' + name)
    return found[0]


def check(repo):
    repo = Path(repo)
    coq = repo / 'Coq'
    # Reuse the checked native-word/four-limb hash decoder, script/digest
    # correspondence and confidential proof-view boundary. Do not assume
    # arbitrary words are valid field elements or points: these jets do not
    # serialize the confidential point at all; they read its proof bytes.
    inherited = load('elements_stream_proof_view_source', HERE.parent / 'elements-issuance-proof/check-source.py')
    result = inherited.check(repo, coq, coq / 'C/jet_elements_issuance_proof_literal.v')
    p = load('elements_stream_source_parser', coq / 'check-secp-predicates-specification.py')
    model = load('elements_stream_fixed_model', HERE / 'source-model.py').MODEL
    paths, cache = set(), {}

    def read(name):
        path = repo / name
        paths.add(path)
        if path not in cache:
            cache[path] = (re.sub(r'/\*.*?\*/|//[^\n]*', ' ', path.read_text(), flags=re.S)
                           if path.suffix == '.c' else p.read_code(path))
        return cache[path]

    def equal(actual, expected, label):
        if compact(actual) != compact(expected):
            raise ValueError('Elements stream selected source differs: ' + label)

    def require(path, fragment):
        if compact(fragment) not in compact(read(path)):
            raise ValueError('Elements stream binding/carrier differs: ' + path + ':' + fragment)

    def line(path, name, expected):
        found = re.findall(r'(?m)^\s*' + re.escape(name) + r'\s*=([^\n]*)$', read(path))
        if len(found) != 1:
            raise ValueError('missing/ambiguous Elements stream clause: ' + name)
        equal(found[0], expected, path + ':' + name)

    for path, kind, name, expected in model['declarations']:
        equal(extract(read(path), kind, name), expected, path + ':' + name)
    for path, start, stop, expected in model['blocks']:
        code = read(path)
        if code.count(start) != 1 or code.count(stop) != 1:
            raise ValueError('missing/ambiguous Elements stream boundary: ' + start)
        equal(code.split(start, 1)[1].split(stop, 1)[0], expected, path + ':' + start)

    catalog = 'Haskell/Simplicity/Elements/Jets.hs'
    wrapper = 'Haskell/Simplicity/Elements/Programs/SigHash/Lib.hs'
    sig = 'Haskell/Simplicity/Elements/Programs/SigHash.hs'
    prim = 'Haskell/Elements/Simplicity/Elements/Primitive.hs'
    data = 'Haskell/Elements/Simplicity/Elements/DataTypes.hs'
    sha = 'Haskell/Core/Simplicity/Programs/Sha256.hs'
    port = 'Coq/C/jet_elements_prim.v'
    for suffix, selector, primitive, field in JETS:
        constructor = selector[0].upper() + selector[1:]
        line(catalog, 'specificationSigHash ' + constructor, 'SigHash.' + selector)
        line(wrapper, selector, 'SigHash.' + selector + ' SigHash.lib')
        require(catalog, constructor + ' :: SigHashJet () Word256')
        line(prim, 'interpret ' + primitive, PRIMITIVES[primitive])
        line(prim, 'primName ' + primitive, '"' + primitive[0].lower() + primitive[1:] + '"')
        input_ty = 'Word8' if primitive == 'Tappath' else 'Word32'
        output_ty = 'Word32' if primitive == 'InputSequence' else 'Word256'
        require(prim, primitive + ' :: Prim ' + input_ty + ' (S ' + output_ty + ')')
        require(port, '| ' + primitive + ' : prim ' + input_ty + ' (S ' + output_ty + ')')
        found = re.findall(r'\bbool\s+simplicity_' + suffix +
            r'\s*\(frameItem\* dst, frameItem src, const txEnv\* env\)\s*\{([^{}]*)\}',
            read('C/elements/elementsJets.c'), re.S)
        if len(found) != 1:
            raise ValueError('missing/ambiguous complete original Elements C getter: ' + suffix)
        equal(found[0], '(void) src; writeHash(dst, &env->' + field + '); return true;', suffix)

    for path, name, expected in [
        (sig, 'lib', 'mkLib Sha256.lib Sha256.libAssert Transaction.lib'),
        (sha, 'libAssert', 'mkLibAssert lib'),
        (prim, 'primPrefix', '"Elements"'),
        (prim, 'tx', 'envTx env'),
        (prim, 'lookupInput', '(sigTxIn tx !?) . fromIntegral'),
        (prim, 'lookupOutput', '(sigTxOut tx !?) . fromIntegral'),
        (prim, 'cast (Just x)', 'Right x'), (prim, 'cast Nothing', 'Left ()'),
        (prim, 'atInput f', 'cast . fmap f . lookupInput . fromInteger . fromWord32'),
        (prim, 'atOutput f', 'cast . fmap f . lookupOutput . fromInteger . fromWord32'),
        (prim, 'encodeHash', 'toWord256 . integerHash256'),
        (data, 'prf_ f (Confidential pt prf)', 'Confidential pt <$> f prf'),
        (data, 'prf_ f (Explicit x)', 'pure (Explicit x)'),
    ]:
        line(path, name, expected)
    for path, fragment in [
        (catalog, 'import qualified Simplicity.Elements.Programs.SigHash.Lib as SigHash'),
        (wrapper, 'import qualified Simplicity.Elements.Programs.SigHash as SigHash'),
        (sig, 'import qualified Simplicity.Programs.Sha256 as Sha256'),
        (sig, 'import Simplicity.Elements.Primitive'),
        (prim, 'import Data.Vector as Vector ((!?), length)'),
        (prim, 'import Lens.Family2 (to, view, under)'),
        (data, 'type Script = BSL.ByteString'),
        (data, 'type RangeProof = BSL.ByteString'), (data, 'type SurjectionProof = BSL.ByteString'),
        (data, 'data Confidential prf a = Explicit a | Confidential Point prf deriving Show'),
        (data, 'newtype AssetWith prf = Asset (Confidential prf Hash256) deriving Show'),
        (data, 'newtype AmountWith prf = Amount (Confidential prf Value) deriving Show'),
        (data, 'type AssetWithWitness = AssetWith SurjectionProof'),
        (data, 'type AmountWithWitness = AmountWith RangeProof'),
        (data, 'asset = adapter to fro where to (Asset x) = x fro x = (Asset x)'),
        (data, 'amount = adapter to fro where to (Amount x) = x fro x = (Amount x)'),
        (data, 'data UTXO = UTXO { utxoAsset :: Asset , utxoAmount :: Amount , utxoScript :: Script } deriving Show'),
        (data, 'data SigTxInput = SigTxInput { sigTxiPegin :: Maybe Hash256 , sigTxiPreviousOutpoint :: Outpoint , sigTxiTxo :: UTXO , sigTxiSequence :: Word32 , sigTxiIssuance :: Maybe Issuance , sigTxiAnnex :: Maybe BSL.ByteString , sigTxiScriptSig :: Script } deriving Show'),
        (data, 'data TxOutput = TxOutput { txoAsset :: AssetWithWitness , txoAmount :: AmountWithWitness , txoNonce :: Maybe Nonce , txoScript :: Script } deriving Show'),
        (data, 'data SigTx = SigTx { sigTxVersion :: Word32 , sigTxIn :: Vector SigTxInput , sigTxOut :: Vector TxOutput , sigTxLock :: Lock } deriving Show'),
        (data, 'data TapEnv = TapEnv { tapleafVersion :: Word8 , tapInternalKey :: PubKey , tappath :: [Hash256] , tapScriptCMR :: Hash256 } deriving Show'),
        ('Coq/C/jet_elements_words_hash_program.v', 'Module EFP := PrimitiveElements.Primitive.'),
        ('Coq/C/jet_elements_words_hash_program.v', 'Notation elements_hash_alg := (EFP.Theory.PrimitivePrimSem option_Monad_Zero).'),
        ('Coq/C/jet_elements_prim.v', 'Definition primName : string := "Elements".'),
    ]:
        require(path, fragment)
    result['source_sha256'].update({str(path): hashlib.sha256(path.read_bytes()).hexdigest() for path in sorted(paths)})
    result.update(selected_jets=['Elements.' + s[0].upper() + s[1:] for _, s, _, _ in JETS],
        selected_primitives=['Elements.' + p for p in PRIMITIVES],
        canonical_stream_source_review_complete=True, whole_contracts_reviewed=True,
        original_c_getters=7, environment_generic_reader_proof=True,
        proof_bytes_not_point_serialization=True,
        caller_cached_hashes_established=False, formal_host_lens_equivalence=False,
        formal_host_crypto_equivalence=False, formal_host_library_equivalence=False,
        kernel_checked_by_this_tool=False, normal_registration=False, coverage_added=0)
    return result


if __name__ == '__main__':
    print(json.dumps(check(Path(sys.argv[1]).resolve()), indent=2))
