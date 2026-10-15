"""Direct digest getters: selected primitives and literal four-limb decoding."""
import argparse
import importlib.util
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def check(repo, coq, helper, endpoint):
    inherited = load('hash_shared_word_source', HERE.parent / 'elements-sequence-review/check-source.py')
    record = inherited.check(repo, coq, coq / 'C/jet_elements_sequence_literal.v')
    parser = load('hash_literal_source_parser', coq / 'check-secp-predicates-specification.py')
    paths = []
    def read(path):
        paths.append(path)
        return parser.read_code(path)
    def equal(actual, expected, label):
        if parser.compact(actual) != parser.compact(expected):
            raise ValueError('hash source differs: ' + label)
    def line(text, start, expected):
        found = re.findall(r'(?m)^\s*' + re.escape(start) + r'\s*=([^\n]*)$', text)
        if len(found) != 1:
            raise ValueError('missing/ambiguous hash clause: ' + start)
        equal(found[0], expected, start)
    def definition(path, name, expected):
        equal(parser.definition(read(path), name), expected, name)
    catalog = read(repo / 'Haskell/Simplicity/Elements/Jets.hs')
    primitive = read(repo / 'Haskell/Elements/Simplicity/Elements/Primitive.hs')
    line(primitive, 'element', 'const')
    line(primitive, 'encodeHash', 'toWord256 . integerHash256')
    for tag, name, field in [('ScriptCMR', 'scriptCMR', 'tapScriptCMR $ envTap env'),
                             ('GenesisBlockHash', 'genesisBlockHash', 'envGenesisBlock env')]:
        parser.require(catalog, tag + ' :: TransactionJet () Word256', 'jet type')
        line(catalog, 'specificationTransaction ' + tag, 'primitive Prim.' + tag)
        line(primitive, 'primName ' + tag, '"' + name + '"')
        expression = ('element . return . encodeHash . tapScriptCMR $ envTap env' if tag == 'ScriptCMR'
                      else 'element . return . encodeHash $ envGenesisBlock env')
        line(primitive, 'interpret ' + tag, expression)
    parser.require(primitive, 'envGenesisBlock :: Hash256', 'direct genesis carrier')
    parser.require(read(repo / 'Haskell/Elements/Simplicity/Elements/DataTypes.hs'),
                   'tapScriptCMR :: Hash256', 'direct CMR carrier')
    digest = read(repo / 'Haskell/Core/Simplicity/Digest.hs')
    for fragment in ['newtype Hash256 = Hash256 { hash256 :: BSS.ShortByteString }',
                     'get = Hash256 <$> getShortByteString 32', 'be256 = adapter to fro',
                     "to h = foldl' go 0 . BSS.unpack $ hash256 h",
                     'go n w = (n `shiftL` 8) .|. fromIntegral w']:
        parser.require(digest, fragment, 'literal digest byte fold')
    line(digest, 'be256_', 'under be256')
    line(digest, 'integerHash256 h', 'toInteger $ h^.be256_')
    numeric = read(repo / 'Haskell/Core/Simplicity/Word.hs')
    for fragment in ['data Word256 = Word256 !Word64 !Word64 !Word64 !Word64',
                     'import Data.Word (Word8, Word16, Word32, Word64)',
                     'liftUnary op x = fromInteger (op (toInteger x))',
                     'pointwiseBinary op (Word256 a3 a2 a1 a0) (Word256 b3 b2 b1 b0) = Word256 (op a3 b3) (op a2 b2) (op a1 b1) (op a0 b0)',
                     'fromInteger i = Word256 (fromInteger a3) (fromInteger a2) (fromInteger a1) (fromInteger i) where a1 = i `div` (2^64) a2 = a1 `div` (2^64) a3 = a2 `div` (2^64)',
                     'toInteger (Word256 a3 a2 a1 a0) = toInteger a0 + 2^64*(toInteger a1 + 2^64*(toInteger a2 + 2^64*toInteger a3))',
                     '(.|.) = pointwiseBinary (.|.)', 'shift a i = liftUnary (flip shift i) a']:
        parser.require(numeric, fragment, 'four-limb unsigned Word256')
    words = read(repo / 'Haskell/Core/Simplicity/Ty/Word.hs')
    for fragment in ['toWord256 = toWord word256', 'word256 = vector256', 'type Word256 = Vector256 Bit',
                     'vector256 = DoubleV vector128', 'vector128 = DoubleV vector64', 'vector64 = DoubleV vector32']:
        parser.require(words, fragment, 'balanced 256-bit output')
    port = read(coq / 'C/jet_elements_prim.v')
    for fragment in ['Let encodeHash (h : hash256) : tySem Word256 := from_hash256 h.',
                     '| GenesisBlockHash => fun _ => Some (encodeHash (envGenesisBlock e))',
                     '| ScriptCMR => fun _ => Some (encodeHash (tapScriptCMR (envTap e)))']:
        parser.require(port, fragment, 'selected primitive port')
    definition(helper, 'haskell_word64_modulus', '18446744073709551616')
    parser.require(read(helper), 'Record haskell_word256 := HaskellWord256 { hw3 : Z; hw2 : Z; hw1 : Z; hw0 : Z }.',
                   'four ordered unsigned limbs')
    definition(helper, 'haskell_word256_valid',
               'Forall (fun z => 0 <= z < haskell_word64_modulus) [hw3 w; hw2 w; hw1 w; hw0 w]')
    definition(helper, 'haskell_word256_modulus', '''haskell_word64_modulus * haskell_word64_modulus *
      haskell_word64_modulus * haskell_word64_modulus''')
    definition(helper, 'haskell_word256_from_integer', '''let a1 := z / haskell_word64_modulus in
      let a2 := a1 / haskell_word64_modulus in let a3 := a2 / haskell_word64_modulus in
      HaskellWord256 (a3 mod haskell_word64_modulus) (a2 mod haskell_word64_modulus)
        (a1 mod haskell_word64_modulus) (z mod haskell_word64_modulus)''')
    definition(helper, 'haskell_word256_integer', '''hw0 w + haskell_word64_modulus *
      (hw1 w + haskell_word64_modulus * (hw2 w + haskell_word64_modulus * hw3 w))''')
    definition(helper, 'haskell_word256_or', '''HaskellWord256 (Z.lor (hw3 x) (hw3 y)) (Z.lor (hw2 x) (hw2 y))
      (Z.lor (hw1 x) (hw1 y)) (Z.lor (hw0 x) (hw0 y))''')
    definition(helper, 'haskell_word256_shift8', 'haskell_word256_from_integer (Z.shiftl (haskell_word256_integer w) 8)')
    definition(helper, 'haskell_be256_step', '''haskell_word256_or (haskell_word256_shift8 w)
      (haskell_word256_from_integer (Byte.unsigned b))''')
    definition(helper, 'haskell_be256_run', '''match bytes with | nil => w
      | b :: rest => haskell_be256_run rest (haskell_be256_step w b) end''')
    definition(helper, 'haskell_integer_hash256',
               'haskell_word256_integer (haskell_be256_run bytes (haskell_word256_from_integer 0))')
    definition(endpoint, 'elements_hash_literal_spec', '''
      Some (haskell_to_word 8 (haskell_integer_hash256 (hash256_to_bytelist (field environment))))''')
    definition(coq / 'C/jet_elements_script_cmr_local.v', 'elements_script_cmr_env_rep', r'''
      exists be ebase bt tbase,
        env = Vptr be (Ptrofs.repr ebase) /\
        0 <= ebase /\ ebase + 88 <= Ptrofs.max_unsigned /\
        0 <= tbase /\ tbase + 176 <= Ptrofs.max_unsigned /\
        Mem.load Mptr m be (ebase + 8) = Some (Vptr bt (Ptrofs.repr tbase)) /\
        uint32_array_at m bt (tbase + 136) (hash256_reg (tapScriptCMR (Elements.envTap environment))) /\
        fp = [(be, ebase + 8, ebase + 16); (bt, tbase + 136, tbase + 168)]''')
    definition(coq / 'C/jet_elements_genesis_hash_local.v', 'elements_genesis_hash_env_rep', r'''
      exists be ebase,
        env = Vptr be (Ptrofs.repr ebase) /\
        0 <= ebase /\ ebase + 88 <= Ptrofs.max_unsigned /\
        uint32_array_at m be (ebase + 16) (hash256_reg (Elements.envGenesisBlock environment)) /\
        fp = [(be, ebase + 16, ebase + 48)]''')
    for suffix, function, rep, field in [
        ('script_cmr', 'script_cmr', 'elements_script_cmr_env_rep', '(fun e => tapScriptCMR (Elements.envTap e))'),
        ('genesis_hash', 'genesis_block_hash', 'elements_genesis_hash_env_rep', 'Elements.envGenesisBlock')]:
        theorem = 'elements_' + suffix + '_literal_local_spec'
        statements = re.findall(r'Theorem ' + theorem + r'\s*:(.*?)\bProof\.', read(endpoint), re.S)
        if len(statements) != 1:
            raise ValueError('missing/ambiguous direct hash C contract')
        equal(statements[0], 'application_jet_local_spec_sep f_simplicity_' + function +
              ' elements_ge Elements.env Ty.Unit Word256 ' + rep + ' (elements_hash_literal_spec ' + field + ').',
              'whole C contract ' + suffix)
        definition(coq / 'C' / ('jet_elements_' + ('script_cmr' if suffix == 'script_cmr' else 'genesis_hash') + '_local.v'),
                   'elements_' + suffix + '_spec', 'Primitive.Combinators.prim Elements.' +
                   ('ScriptCMR' if suffix == 'script_cmr' else 'GenesisBlockHash'))
    import hashlib
    record['source_sha256'].update({str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(set(paths))})
    record.update(selected_primitives=['Elements.ScriptCMR', 'Elements.GenesisBlockHash'],
                  four_limb_byte_decoder_reviewed=True)
    record['shared_dependency_primitive'] = record.pop('selected_primitive')
    return record


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    for name in ['repo', 'coq', 'helper', 'endpoint']:
        parser.add_argument('--' + name, type=Path, required=True)
    args = parser.parse_args()
    print(json.dumps(check(args.repo, args.coq, args.helper, args.endpoint), indent=2))
