"""Read-only null-data parser, encoding, environment and full-contract mutations."""
import importlib.util
from pathlib import Path
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('null_data_source_negative', HERE / 'check-source.py')
g = importlib.util.module_from_spec(sp)
sp.loader.exec_module(g)
repo = Path(sys.argv[1]).resolve()
original = Path.read_text
fixtures = []
hs = 'Haskell/Elements/Simplicity/Elements/Primitive.hs'
data = 'Haskell/Elements/Simplicity/Elements/DataTypes.hs'
catalog = 'Haskell/Simplicity/Elements/Jets.hs'
port = 'Coq/C/jet_elements_prim.v'
literal = 'Coq/C/jet_elements_null_data_literal.v'
context = 'Coq/C/jet_application_context_contract.v'
environment = 'Coq/C/jet_elements_null_data_environment.v'
parse = 'Coq/C/jet_elements_null_data_parse.v'


def add(path, old, new):
    assert old in original(repo / path), ('inactive source fixture', path, old)
    assert old != new
    fixtures.append((repo / path, old, new))


def scoped(path, kind, name, old, new):
    block = g.extract(original(repo / path), kind, name)
    assert old in block, ('inactive scoped fixture', name, old)
    add(path, block, block.replace(old, new, 1))


add(catalog, 'specificationTransaction OutputNullDatum = primitive Prim.OutputNullDatum',
    'specificationTransaction OutputNullDatum = primitive Prim.OutputScriptHash')
add(hs, 'primName OutputNullDatum = "outputNullDatum"', 'primName OutputNullDatum = "outputNullData"')
add(hs, 'lookupOutput = (sigTxOut tx !?) . fromIntegral', 'lookupOutput = (sigTxIn tx !?) . fromIntegral')
add(hs, 'txo <- lookupOutput . fromInteger $ fromWord32 i', 'txo <- lookupOutput . fromInteger $ fromWord32 j')
add(hs, 'nullData <- txNullData $ txoScript txo', 'nullData <- txNullData mempty')
add(hs, 'encodeNullDatum . fmap bslHash', 'encodeNullDatum . fmap bslDoubleHash')
add(hs, 'List.drop (fromInteger (fromWord32 j)) nullData', 'List.drop (fromInteger (fromWord32 i)) nullData')
for op in range(1, 17):
    add(data, 'go 0x%02x = return OP%d' % (0x50 + op, op),
        'go 0x%02x = return OPReserved' % (0x50 + op))
for old, new in [('getWord32le', 'getWord32be'), ('getWord16le', 'getWord16be'),
                 ('PushData <$> getLazyByteString', 'Immediate <$> getLazyByteString'),
                 ('op < 0x4c', 'op <= 0x4c'), ('0x6a <- getWord8', '0x6b <- getWord8'),
                 ('if emp then return [] else', 'if not emp then return [] else')]:
    add(data, old, new)
for constructor, code in [('Immediate', 0), ('PushData', 1), ('PushData2', 2), ('PushData4', 3)]:
    add(hs, 'encodeNullDatum (%s h) = Left (toWord2 %d, encodeHash h)' % (constructor, code),
        'encodeNullDatum (%s h) = Left (toWord2 %d, encodeHash h)' % (constructor, (code + 1) % 4))
for op in range(1, 17):
    # Preserve Haskell's original spacing in each selected line.
    line = next(line for line in original(repo / hs).splitlines()
                if line.strip().startswith('encodeNullDatum OP%d ' % op))
    add(hs, line, line.replace('0x%x' % (op - 1), '0x%x' % (op % 16)))
for old, new in [('encodeNullDatum OP1Negate = Right (Left (toBit False))',
                  'encodeNullDatum OP1Negate = Right (Left (toBit True))'),
                 ('encodeNullDatum OPReserved = Right (Left (toBit True))',
                  'encodeNullDatum OPReserved = Right (Left (toBit False))')]:
    add(hs, old, new)
for name, old, new in [
    ('getBytes', 'Z.leb n (Zlength bs)', 'Z.ltb n (Zlength bs)'),
    ('getBytes', 'firstn (Z.to_nat n) bs', 'skipn (Z.to_nat n) bs'),
    ('getBytes', 'skipn (Z.to_nat n) bs', 'firstn (Z.to_nat n) bs'),
    ('leValue', 'Byte.unsigned b + 256 * leValue rest', '256 * Byte.unsigned b + leValue rest'),
    ('getPush', 'getBytes width bs', 'getBytes 0 bs'),
    ('getPush', 'getBytes (leValue len) rest', 'getBytes (leValue len) bs'),
    ('getTxNullDatum', 'getPush 4 rest', 'getPush 2 rest'),
    ('getTxNullDatum', 'getPush 2 rest', 'getPush 4 rest'),
    ('getTxNullDatum', 'getPush 1 rest', 'getPush 2 rest'),
    ('getTxNullDatum', 'Z.ltb o 76', 'Z.leb o 76'),
    ('getTxNullData', '| [] => Some []', '| [] => None'),
    ('getTxNullData', '| O => None', '| O => Some []'),
    ('getTxNullData', 'getTxNullData fuel\' rest', 'getTxNullData fuel\' bs'),
    ('txNullData', '106', '107'),
    ('txNullData', 'getTxNullData (length rest) rest', 'getTxNullData 0 rest'),
]:
    scoped(port, 'declaration', name, old, new)
for code, constructor in [(96 - k, 'OP%d' % (16 - k)) for k in range(16)] + [(80, 'OPReserved'), (79, 'OP1Negate')]:
    scoped(port, 'declaration', 'getTxNullDatum',
        'if Z.eqb o %d then Some (%s, rest)' % (code, constructor),
        'if Z.eqb o %d then Some (OP1Negate, rest)' % (code - 1))
for name in ['elements_null_data_opcode_environment', 'elements_null_data_output_environment',
             'elements_null_data_environment_rep']:
    block = g.extract(original(repo / environment), 'declaration', name)
    head, body = block.split(':=', 1)
    add(environment, block, head + r':= True \/ (' + body.rstrip().rstrip('.') + ').\n')
for old, new in [('bm_separated L s', 'True'),
                 ('bitSize B <= writeEmpty', '0 <= writeEmpty'),
                 ('Clight2.eval_funcall ge m (Internal f)', 'Clight2.eval_funcall ge mf (Internal f)'),
                 ('activeReadFrame := activeReadFrame s', 'activeReadFrame := newReadFrame []'),
                 ('rev (@encode B value) ++ writeData', 'writeData'),
                 ('env_rep m env logical_env fp', 'True')]:
    scoped(context, 'declaration', 'application_jet_bitmachine_spec', old, new)
for old, new in [('haskell_from_word 5 (fst a)', 'haskell_from_word 5 (snd a)'),
                 ('haskell_from_word 5 (snd a)', 'haskell_from_word 5 (fst a)'),
                 ('| None => inl tt', '| None => inr (inl tt)'),
                 ('mapNullDatum byteStringHash d', 'mapNullDatum (fun _ => byteStringHash []) d')]:
    scoped(literal, 'declaration', 'elements_output_null_datum_literal_spec', old, new)
for old, new in [('application_jet_bitmachine_spec', 'False -> application_jet_bitmachine_spec'),
                 ('application_jet_bitmachine_spec', 'application_jet_local_spec_sep'),
                 ('f_simplicity_output_null_datum', 'f_simplicity_output_script_hash'),
                 ('elements_ge Elements.env', 'ge0 Elements.env'),
                 ('elements_ge Elements.env', 'elements_ge Bitcoin.env'),
                 ('elements_null_data_environment_rep', '(fun _ _ _ _ => True)'),
                 ('elements_output_null_datum_literal_spec', '(fun _ _ => Some (inl tt))')]:
    scoped(literal, 'statement', 'elements_output_null_datum_literal_bitmachine_spec', old, new)
scoped(parse, 'declaration', 'null_data_parse', '| null_data_parse_nil',
       '| null_data_parse_any bs ds : null_data_parse bs ds\n| null_data_parse_nil')
scoped(parse, 'statement', 'getTxNullData_fuel_adequate', '(length bs <= fuel)%nat', 'False')
for old, new in [('uint_fast32_t j = simplicity_read32(&src);', 'uint_fast32_t j = 0;'),
                 ('i < env->tx->numOutputs &&', 'i <= env->tx->numOutputs &&'),
                 ('j < env->tx->output[i].pnd.len', 'j <= env->tx->output[i].pnd.len'),
                 ('skipBits(dst, 1 + 1 + 2 + 256);', 'skipBits(dst, 1 + 2 + 256);')]:
    add('C/elements/elementsJets.c', old, new)
digest = 'Haskell/Core/Simplicity/Digest.hs'
add(digest, 'bslHash = ivHash . IV . pushChunks sha256Incremental . padSHA1',
    'bslHash = ivHash . IV . pushChunks sha256Incremental')
scoped('Coq/Simplicity/Digest.v', 'declaration', 'byteStringHash', 'generate_and_pad_alt x', 'generate_and_pad_alt (rev x)')
all_data = original(repo / data)
add(data, all_data, all_data + '\ngetWord32le = pure 0\n')

g.check(repo)
for path, a, b in fixtures:
    altered = original(path).replace(a, b, 1)
    assert altered != original(path)
    def read(self, *args, **kw):
        return altered if self == path else original(self, *args, **kw)
    with patch.object(Path, 'read_text', read):
        try:
            g.check(repo)
        except ValueError:
            pass
        else:
            raise AssertionError('accepted null-data source corruption: ' + str(path) + ':' + a)
g.check(repo)
print(str(len(fixtures)) + ' null-data parser/constructor/environment/whole-C-contract corruptions rejected')
