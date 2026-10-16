"""Selected canonical source fidelity for sixteen original-C hash getters.

This is a regression guard around a reviewed source correspondence, not a
formal proof of the Haskell runtime, its libraries, or C caller construction.
Execution, complete contracts, dependencies and kernel checking are separate.
"""
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent

# C suffix, canonical Haskell selector, actual complete getter's hash field.
JETS = [
    ('output_values_hash', 'outputValuesHash', 'tx->outputValuesHash'),
    ('output_scripts_hash', 'outputScriptsHash', 'tx->outputScriptsHash'),
    ('input_values_hash', 'inputValuesHash', 'tx->inputValuesHash'),
    ('input_scripts_hash', 'inputScriptsHash', 'tx->inputScriptsHash'),
    ('input_sequences_hash', 'inputSequencesHash', 'tx->inputSequencesHash'),
    ('input_script_sigs_hash', 'inputScriptSigsHash', 'tx->inputScriptSigsHash'),
    ('tappath_hash', 'tappathHash', 'taproot->tappathHash'),
    ('tapleaf_hash', 'tapleafHash', 'taproot->tapLeafHash'),
    ('outputs_hash', 'outputsHash', 'tx->outputsHash'),
    ('input_utxos_hash', 'inputUtxosHash', 'tx->inputUTXOsHash'),
    ('tap_env_hash', 'tapEnvHash', 'taproot->tapEnvHash'),
    ('input_outpoints_hash', 'inputOutpointsHash', 'tx->inputOutpointsHash'),
    ('input_annexes_hash', 'inputAnnexesHash', 'tx->inputAnnexesHash'),
    ('inputs_hash', 'inputsHash', 'tx->inputsHash'),
    ('tx_hash', 'txHash', 'tx->txHash'),
    ('sig_all_hash', 'sigAllHash', 'sigAllHash'),
]
PRIMITIVE_CLAUSES = {
    'Version': 'element . return . toWord32 . toInteger $ sigTxVersion tx',
    'LockTime': 'element . return . toWord32 . toInteger $ sigTxLock tx',
    'CurrentIndex': 'element . return . toWord32 . toInteger $ ix',
    'InputPrevOutpoint': 'return . (atInput $ encodeOutpoint . sigTxiPreviousOutpoint)',
    'InputValue': 'return . (atInput $ toWord64 . toInteger . sigTxiValue)',
    'InputScriptHash': 'return . (atInput $ encodeHash . bslHash . sigTxiScript)',
    'InputSequence': 'return . (atInput $ toWord32 . toInteger . sigTxiSequence)',
    'InputAnnexHash': 'return . (atInput $ cast . fmap (encodeHash . bslHash) . sigTxiAnnex)',
    'InputScriptSigHash': 'return . (atInput $ encodeHash . bslHash . sigTxiScriptSig)',
    'OutputValue': 'return . (atOutput $ toWord64 . fromIntegral . txoValue)',
    'OutputScriptHash': 'return . (atOutput $ encodeHash . bslHash . txoScript)',
    'TapleafVersion': 'element . return . toWord8 . toInteger . tapleafVersion $ envTap env',
    'Tappath': 'return . cast . fmap encodeHash . listToMaybe . flip drop (tappath (envTap env)) . fromInteger . fromWord8',
    'InternalKey': 'element . return . encodeKey . tapInternalKey $ envTap env',
    'ScriptCMR': 'element . return . toWord256 . integerHash256 . tapScriptCMR $ envTap env',
}
PRIMITIVE_TYPES = {
    'Version': '() Word32', 'LockTime': '() Word32', 'CurrentIndex': '() Word32',
    'InputPrevOutpoint': 'Word32 (S (Word256,Word32))',
    'InputValue': 'Word32 (S Word64)', 'InputScriptHash': 'Word32 (S Word256)',
    'InputSequence': 'Word32 (S Word32)', 'InputAnnexHash': 'Word32 (S (S Word256))',
    'InputScriptSigHash': 'Word32 (S Word256)', 'OutputValue': 'Word32 (S Word64)',
    'OutputScriptHash': 'Word32 (S Word256)', 'TapleafVersion': '() Word8',
    'Tappath': 'Word8 (S Word256)', 'InternalKey': '() PubKey', 'ScriptCMR': '() Word256',
}


def load(name, path):
    sp = importlib.util.spec_from_file_location(name, path)
    m = importlib.util.module_from_spec(sp)
    sp.loader.exec_module(m)
    return m


def extract(code, kind, name):
    if kind == 'declaration':
        pattern = r'\b(?:Definition|Fixpoint|Let|Record)\s+' + re.escape(name) + r"(?![\w']).*?\.\s*(?=\n|$)"
    elif kind == 'statement':
        pattern = r'\b(?:Lemma|Theorem)\s+' + re.escape(name) + r"(?![\w']).*?(?=\bProof\.)"
    elif kind == 'proof_definition':
        pattern = r'\bDefinition\s+' + re.escape(name) + r"(?![\w']).*?\bDefined\."
    else:
        raise ValueError('unknown raw-program declaration kind')
    found = re.findall(pattern, code, re.S)
    if len(found) != 1:
        raise ValueError('missing/ambiguous raw-program declaration: ' + name)
    return found[0]


def check(repo):
    repo = Path(repo)
    coq = repo / 'Coq'
    # Reuse the already reviewed SHA/tag, literal traversal and four-limb
    # unsigned hash decoder. Their own source/corruption checks remain required.
    inherited = load('raw_program_tapleaf_source', HERE.parent / 'bitcoin-tapleaf-literal/check-source.py')
    result = inherited.check(repo)
    p = load('raw_program_source_parser', coq / 'check-secp-predicates-specification.py')
    model = load('raw_program_fixed_model', HERE / 'source-model.py').MODEL
    paths, cache = set(), {}

    def read(name):
        path = repo / name
        paths.add(path)
        if path not in cache:
            cache[path] = (re.sub(r'/\*.*?\*/|//[^\n]*', ' ', path.read_text(), flags=re.S)
                           if path.suffix == '.c' else p.read_code(path))
        return cache[path]

    def equal(actual, expected, label):
        if p.compact(actual) != p.compact(expected):
            raise ValueError('raw-program selected source differs: ' + label)

    def line(path, name, expected):
        found = re.findall(r'(?m)^\s*' + re.escape(name) + r'\s*=([^\n]*)$', read(path))
        if len(found) != 1:
            raise ValueError('missing/ambiguous raw-program source clause: ' + name)
        equal(found[0], expected, path + ':' + name)

    for path, kind, name, expected in model['declarations']:
        equal(extract(read(path), kind, name), expected, path + ':' + name)
    for path, start, stop, expected in model['blocks']:
        code = read(path)
        if code.count(start) != 1 or code.count(stop) != 1:
            raise ValueError('missing/ambiguous raw-program source boundary: ' + start)
        equal(code.split(start, 1)[1].split(stop, 1)[0], expected, path + ':' + start)

    catalog = 'Haskell/Simplicity/Bitcoin/Jets.hs'
    wrapper = 'Haskell/Simplicity/Bitcoin/Programs/SigHash/Lib.hs'
    sig = 'Haskell/Simplicity/Bitcoin/Programs/SigHash.hs'
    primitive = 'Haskell/Bitcoin/Simplicity/Bitcoin/Primitive.hs'
    data = 'Haskell/Bitcoin/Simplicity/Bitcoin/DataTypes.hs'
    bitcoin = 'Haskell/Core/Simplicity/Programs/Bitcoin.hs'
    bitcoin_lib = 'Haskell/Core/Simplicity/Programs/Bitcoin/Lib.hs'
    for suffix, selector, field in JETS:
        constructor = selector[0].upper() + selector[1:]
        line(catalog, 'specificationSigHash ' + constructor, 'SigHash.' + selector)
        line(wrapper, selector, 'SigHash.' + selector + ' SigHash.lib')
        p.require(read(catalog), constructor + ' :: SigHashJet () Word256', 'hash jet domain')
        found = re.findall(r'\bbool\s+simplicity_bitcoin_' + suffix +
                           r'\s*\(frameItem\* dst, frameItem src, const txEnv\* env\)\s*\{([^{}]*)\}',
                           read('C/bitcoin/bitcoinJets.c'), re.S)
        if len(found) != 1:
            raise ValueError('missing/ambiguous complete original-C getter: ' + suffix)
        equal(found[0], '(void) src; writeHash(dst, &env->' + field + '); return true;', suffix)

    for name, expected in PRIMITIVE_CLAUSES.items():
        line(primitive, 'interpret ' + name, expected)
        line(primitive, 'primName ' + name, '"' + name[0].lower() + name[1:] + '"')
        p.require(read(primitive), name + ' :: Prim ' + PRIMITIVE_TYPES[name], 'raw primitive type')
    for path, name, expected in [
        (sig, 'lib', 'mkLib Sha256.lib Sha256.libAssert Transaction.lib'),
        (bitcoin_lib, 'outpointHash', 'Bitcoin.outpointHash Bitcoin.libAssert'),
        (bitcoin_lib, 'annexHash', 'Bitcoin.annexHash Bitcoin.libAssert'),
        (bitcoin, 'libAssert', 'mkLibAssert Sha256.lib Sha256.libAssert LibSecp256k1.lib'),
        (bitcoin, 'ctx8Add32', 'ctx8Addn vector32'),
        (bitcoin, 'ctx8Add4', 'ctx8Addn vector4'),
        (primitive, 'tx', 'envTx env'), (primitive, 'ix', 'envIx env'),
        (primitive, 'lookupInput', '(sigTxIn tx !?) . fromIntegral'),
        (primitive, 'lookupOutput', '(sigTxOut tx !?) . fromIntegral'),
        (primitive, 'cast (Just x)', 'Right x'), (primitive, 'cast Nothing', 'Left ()'),
        (primitive, 'element', 'const'),
        (primitive, 'atInput f', 'cast . fmap f . lookupInput . fromInteger . fromWord32'),
        (primitive, 'atOutput f', 'cast . fmap f . lookupOutput . fromInteger . fromWord32'),
        (primitive, 'encodeHash', 'toWord256 . integerHash256'),
        (primitive, 'encodeOutpoint op', '(toWord256 . integerHash256 $ opHash op, toWord32 . fromIntegral $ opIndex op)'),
        (primitive, 'encodeKey (Schnorr.PubKey x)', 'toWord256 . toInteger $ x'),
        (data, 'sigTxiValue', 'txoValue . sigTxiTxo'),
        (data, 'sigTxiScript', 'txoScript . sigTxiTxo'),
    ]:
        line(path, name, expected)
    for path, fragment in [
        (catalog, 'import qualified Simplicity.Bitcoin.Programs.SigHash.Lib as SigHash'),
        (wrapper, 'import qualified Simplicity.Bitcoin.Programs.SigHash as SigHash'),
        (sig, 'import qualified Simplicity.Programs.Sha256 as Sha256'),
        (sig, 'import Simplicity.Programs.Bitcoin.Lib'),
        (bitcoin_lib, 'import qualified Simplicity.Programs.Bitcoin as Bitcoin'),
        (primitive, 'import Data.Vector as Vector ((!?), length)'),
        (primitive, 'InputAnnexHash :: Prim Word32 (S (S Word256))'),
        (primitive, 'InternalKey :: Prim () PubKey'),
        (data, 'type Script = BSL.ByteString'), (data, 'type Lock = Word32'),
        (data, 'type Value = Word64'),
        (data, 'data Outpoint = Outpoint { opHash :: Hash256 , opIndex :: Word32 } deriving Show'),
        (data, 'data SigTxInput = SigTxInput { sigTxiPreviousOutpoint :: Outpoint , sigTxiTxo :: TxOutput , sigTxiSequence :: Word32 , sigTxiAnnex :: Maybe BSL.ByteString , sigTxiScriptSig :: Script } deriving Show'),
        (data, 'data TxOutput = TxOutput { txoValue :: Value , txoScript :: Script } deriving Show'),
        (data, 'data SigTx = SigTx { sigTxVersion :: Word32 , sigTxIn :: Vector SigTxInput , sigTxOut :: Vector TxOutput , sigTxLock :: Lock } deriving Show'),
        (data, 'data TapEnv = TapEnv { tapleafVersion :: Word8 , tapInternalKey :: PubKey , tappath :: [Hash256] , tapScriptCMR :: Hash256 } deriving Show'),
        ('Haskell/Core/Simplicity/LibSecp256k1/Schnorr.hs', 'import Simplicity.Word'),
        ('Haskell/Core/Simplicity/LibSecp256k1/Schnorr.hs', 'data PubKey = PubKey Word256'),
    ]:
        p.require(read(path), fragment, 'raw-program binding/carrier: ' + path)

    result['source_sha256'].update({str(path): hashlib.sha256(path.read_bytes()).hexdigest() for path in sorted(paths)})
    result.update(selected_jets=['Bitcoin.' + selector[0].upper() + selector[1:] for _, selector, _ in JETS],
        selected_primitives=['Bitcoin.' + name for name in PRIMITIVE_CLAUSES],
        canonical_raw_program_source_review_complete=True, whole_contracts_reviewed=True,
        shared_parametric_program_projection=True, original_c_getters=16,
        raw_data_interpretation=True, caller_environment_construction_proved=False,
        formal_host_library_equivalence=False, normal_registration=False, coverage_added=0)
    return result


if __name__ == '__main__':
    print(json.dumps(check(Path(sys.argv[1]).resolve()), indent=2))
