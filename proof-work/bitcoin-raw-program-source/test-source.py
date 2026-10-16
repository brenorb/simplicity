"""Read-only negative checks for the selected raw-program source boundary."""
import importlib.util
from pathlib import Path
import re
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('raw_program_negative', HERE / 'check-source.py')
g = importlib.util.module_from_spec(sp)
sp.loader.exec_module(g)
repo = Path(sys.argv[1]).resolve()
model = g.load('raw_program_negative_model', HERE / 'source-model.py').MODEL
original = Path.read_text
fixtures = []


def add(path, before, after):
    fixtures.append((repo / path, before, after))


for path, kind, name, _ in model['declarations']:
    code = original(repo / path)
    head = re.search(r'\b(?:Definition|Fixpoint|Let|Record|Lemma|Theorem)\s+' + re.escape(name) + r"(?![\w'])", code)
    if head is None:
        raise AssertionError('missing active declaration fixture: ' + name)
    add(path, head[0], head[0] + '_UNREVIEWED')
for path, start, stop, _ in model['blocks']:
    # Keeping the full original block in comments must not mask an active edit.
    text = original(repo / path)
    begin, end = text.index(start), text.index(stop, text.index(start))
    block = text[begin:end]
    add(path, block, block + '\nUNREVIEWED_ACTIVE_CLAUSE\n')

catalog = 'Haskell/Simplicity/Bitcoin/Jets.hs'
wrapper = 'Haskell/Simplicity/Bitcoin/Programs/SigHash/Lib.hs'
primitive = 'Haskell/Bitcoin/Simplicity/Bitcoin/Primitive.hs'
for suffix, selector, field in g.JETS:
    constructor = selector[0].upper() + selector[1:]
    clause = 'specificationSigHash ' + constructor + ' = SigHash.' + selector
    add(catalog, clause, clause + '_UNREVIEWED\n-- ' + clause)
    clause = selector + ' = SigHash.' + selector + ' SigHash.lib'
    add(wrapper, clause, clause.replace('SigHash.lib', 'otherLib'))
    add(catalog, constructor + ' :: SigHashJet () Word256', constructor + ' :: SigHashJet Word32 Word256')
    c = 'writeHash(dst, &env->' + field + ');'
    add('C/bitcoin/bitcoinJets.c', c, 'writeHash(dst, &env->wrongHash); /* ' + c + ' */')
for name, expected in g.PRIMITIVE_CLAUSES.items():
    clause = 'interpret ' + name + ' = ' + expected
    add(primitive, clause, clause + ' UNREVIEWED\n-- ' + clause)
    add(primitive, name + ' :: Prim ' + g.PRIMITIVE_TYPES[name], name + ' :: Prim () ()')
    clause = 'primName ' + name + ' = "' + name[0].lower() + name[1:] + '"'
    add(primitive, clause, clause.replace('"', '"UNREVIEWED', 1))

for path, a, b in [
    ('Coq/C/jet_bitcoin_raw_program.v', 'Bitcoin.sem q a (raw_base environment)', 'None'),
    ('Coq/C/jet_bitcoin_raw_program.v', 'raw_ext_sem q a environment', 'None'),
    ('Coq/C/jet_bitcoin_raw_program.v', 'f a (project_raw_environment environment Hpath) = g a environment', 'True'),
    ('Coq/C/jet_bitcoin_raw_env.v', '(length (raw_tap_path environment) <= 128)%nat', '(length (raw_tap_path environment) <= 127)%nat'),
    ('Coq/C/jet_bitcoin_raw_env.v', 'extInScriptHash := map (fun i => byteStringHash (raw_redeemed_script i))', 'extInScriptHash := map (fun i => byteStringHash (raw_script_sig i))'),
    ('Coq/C/jet_bitcoin_raw_env.v', '| None => inl tt', '| None => inr (inl tt)'),
    ('Coq/C/jet_forWhile_spec.v', 'for_while_program k (for_while_program k', 'for_while_program k (for_while_program 0'),
    ('Coq/C/jet_bitcoin_tx_hash.v', '| inl _ => [byte_zero]', '| inl _ => [byte_one]'),
    ('Coq/C/jet_bitcoin_tx_hash.v', '@ctx8_addn_spec 3 term', '@ctx8_addn_spec 2 term'),
    ('Haskell/Bitcoin/Simplicity/Bitcoin/DataTypes.hs', 'type Value = Word64', 'type Value = Word32'),
    ('Haskell/Bitcoin/Simplicity/Bitcoin/DataTypes.hs', 'sigTxVersion :: Word32', 'sigTxVersion :: Word64'),
    ('Haskell/Bitcoin/Simplicity/Bitcoin/DataTypes.hs', 'sigTxiValue = txoValue . sigTxiTxo', 'sigTxiValue = txoValue . otherTxo'),
    ('Haskell/Core/Simplicity/LibSecp256k1/Schnorr.hs', 'data PubKey = PubKey Word256', 'data PubKey = PubKey FE'),
    ('Haskell/Simplicity/Bitcoin/Programs/SigHash.hs', 'hashWord256s8 = hashWord256s word8', 'hashWord256s8 = hashWord256s word32'),
    ('Haskell/Simplicity/Bitcoin/Programs/SigHash.hs', 'ctx8Add64 = ctx8Addn vector64', 'ctx8Add64 = ctx8Addn vector32'),
    ('Haskell/Core/Simplicity/Programs/Bitcoin.hs', 'ih &&& take (zero word8)', 'ih &&& take (one word8)'),
    ('Haskell/Core/Simplicity/Programs/Bitcoin/Lib.hs', 'annexHash = Bitcoin.annexHash Bitcoin.libAssert', 'annexHash = Bitcoin.outpointHash Bitcoin.libAssert'),
]:
    add(path, a, b)

p = g.load('raw_program_fixture_parser', repo / 'Coq/check-secp-predicates-specification.py')
path = 'Coq/C/jet_bitcoin_hash_raw_program.v'
for suffix, _, _ in g.JETS:
    name = 'bitcoin_' + suffix + '_raw_program_local_spec'
    block = g.extract(p.read_code(repo / path), 'statement', name).strip()
    for a, b in [
        ('application_jet_local_spec_sep', 'False -> application_jet_local_spec_sep'),
        ('f_simplicity_bitcoin_' + suffix, 'f_simplicity_bitcoin_wrong_jet'),
        ('bitcoin_ge raw_bitcoin_environment', 'other_ge raw_bitcoin_environment'),
        ('Ty.Unit Word256', 'Word32 Word256'), ('raw_env_rep', 'wrong_rep'),
        ('raw_fullalg', 'fullalg'),
    ]:
        if a not in block:
            raise AssertionError('inactive full-contract fixture: ' + name + ':' + a)
        add(path, block, block.replace(a, b, 1))

g.check(repo)
for path, a, b in fixtures:
    text = original(path)
    if a not in text:
        raise AssertionError('inactive raw-program fixture: ' + str(path) + ':' + a)
    altered = text.replace(a, b, 1)
    if altered == text:
        raise AssertionError('no-op raw-program fixture')
    def read(self, *args, **kwargs):
        return altered if self == path else original(self, *args, **kwargs)
    with patch.object(Path, 'read_text', read):
        try:
            g.check(repo)
        except ValueError:
            pass
        else:
            raise AssertionError('accepted raw-program source corruption: ' + str(path) + ':' + a)
g.check(repo)
print(str(len(fixtures)) + ' raw Bitcoin program/primitive/carrier/getter/full-contract corruptions rejected')
