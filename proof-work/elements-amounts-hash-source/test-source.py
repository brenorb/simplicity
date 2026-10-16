"""Read-only, active corruptions of serializer/pairing/primitive/whole-C sources."""
import importlib.util
from pathlib import Path
import re
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('amounts_negative_source', HERE / 'check-source.py')
g = importlib.util.module_from_spec(spec)
spec.loader.exec_module(g)
repo = Path(sys.argv[1]).resolve()
model = g.load('amounts_negative_model', HERE / 'source-model.py').MODEL
original = Path.read_text
fixtures = []


def add(path, before, after):
    fixtures.append((repo / path, before, after))


for path, kind, name, _ in model['declarations']:
    head = re.search(r'\b(?:Definition|Fixpoint|Let|Record|Lemma|Theorem)\s+' + re.escape(name) + r"(?![\w'])",
                     original(repo / path))
    if head is None:
        raise AssertionError('missing amounts declaration fixture: ' + name)
    add(path, head[0], head[0] + '_UNREVIEWED')
for path, start, stop, _ in model['blocks']:
    add(path, start, start + 'UNREVIEWED ')
for path, name, _ in model['lines']:
    found = re.findall(r'(?m)^\s*' + re.escape(name) + r'\s*=[^\n]*$', original(repo / path))
    if len(found) != 1:
        raise AssertionError('missing/ambiguous amounts binding fixture: ' + name)
    add(path, found[0], found[0] + ' UNREVIEWED')
for path, fragment in model['fragments']:
    add(path, fragment, fragment + ' UNREVIEWED')

serializer = 'Coq/C/jet_elements_asset_amount_hash_spec.v'
endpoint = 'Coq/C/jet_elements_amounts_hash_program.v'
core = 'Haskell/Core/Simplicity/Programs/Elements.hs'
for path, before, after in [
    (serializer, 'asset_byte_even : Ty.tySem Word8 := @fromZ (WordToZ 3) 10',
     'asset_byte_even : Ty.tySem Word8 := @fromZ (WordToZ 3) 11'),
    (serializer, 'amount_byte_even : Ty.tySem Word8 := @fromZ (WordToZ 3) 8',
     'amount_byte_even : Ty.tySem Word8 := @fromZ (WordToZ 3) 9'),
    (serializer, '(@ctx8_addn_spec 3 term)', '(@ctx8_addn_spec 5 term)'),
    (serializer, '| inr v => byte_one :: vector_values Word8 3 v',
     '| inr v => byte_one :: vector_values Word8 5 v'),
    (serializer, 'elements_asset_bytes (fst v) ++ elements_amount_bytes (snd v)',
     'elements_amount_bytes (snd v) ++ elements_asset_bytes (fst v)'),
    (serializer, 'AC.copair (Alg.scribe prefix_even) (Alg.scribe prefix_odd)',
     'AC.copair (Alg.scribe prefix_odd) (Alg.scribe prefix_even)'),
    (endpoint, 'Elements.OutputAmount Elements.OutputAsset', 'Elements.InputAmount Elements.InputAsset'),
    (endpoint, 'Elements.InputAmount Elements.InputAsset', 'Elements.OutputAmount Elements.OutputAsset'),
    (endpoint, '(@EFP.Combinators.prim _ _ alg pm) (@EFP.Combinators.prim _ _ alg pa)',
     '(@EFP.Combinators.prim _ _ alg pa) (@EFP.Combinators.prim _ _ alg pm)'),
    (core, '(scribe (toWord8 0x0a)) (scribe (toWord8 0x0b))',
     '(scribe (toWord8 0x0b)) (scribe (toWord8 0x0a))'),
    (core, '(scribe (toWord8 0x08)) (scribe (toWord8 0x09))',
     '(scribe (toWord8 0x09)) (scribe (toWord8 0x08))'),
    (core, '&&& oh >>> ctx8Add8)', '&&& oh >>> ctx8Add32)'),
    ('Haskell/Simplicity/Elements/Programs/Transaction.hs',
     'outputAmount = primitive OutputAmount &&& primitive OutputAsset',
     'outputAmount = primitive OutputAsset &&& primitive OutputAmount'),
    ('Haskell/Simplicity/Elements/Programs/SigHash.hs',
     'body = take (drop outputAmount) &&& ih', 'body = take (drop inputAmount) &&& ih'),
    ('Haskell/Simplicity/Elements/Programs/SigHash.hs',
     'body = take (drop inputAmount) &&& ih', 'body = take (drop outputAmount) &&& ih'),
    ('Coq/C/jet_elements_asset_literal.v',
     'haskell_to_word 8 (packed_fe_integer_literal packed)', 'haskell_to_word 8 0'),
    ('Coq/C/jet_elements_amount_literal.v',
     'haskell_to_word 6 (Int64.unsigned v)', 'haskell_to_word 8 (Int64.unsigned v)'),
]:
    add(path, before, after)

parser = g.load('amounts_complete_contract_fixtures', repo / 'Coq/check-secp-predicates-specification.py')
for direction, offset in [('output', 24), ('input', 248)]:
    block = g.extract(parser.read_code(repo / endpoint), 'statement',
        'elements_' + direction + '_amounts_hash_program_local_spec').strip()
    for before, after in [
        ('application_jet_local_spec_sep', 'False -> application_jet_local_spec_sep'),
        ('f_simplicity_' + direction + '_amounts_hash', 'wrong_function'),
        ('elements_ge Elements.env', 'wrong_ge Elements.env'),
        ('Ty.Unit Word256', 'Word32 Word256'),
        ('hash_getter_rep elements_' + direction + '_amounts_hash_of', 'hash_getter_rep wrong_hash_of'),
        ('0 ' + str(offset) + ' 760', '0 88 760'),
        ('elements_' + direction + '_amounts_hash_spec', 'elements_prim_words_hash_spec'),
        ('elements_hash_alg', 'wrong_alg'),
    ]:
        if before not in block:
            raise AssertionError('inactive complete amounts contract fixture: ' + before)
        add(endpoint, block, block.replace(before, after, 1))
    add('C/elements/elementsJets.c', 'writeHash(dst, &env->tx->' + direction + 'AssetAmountsHash);',
        'writeHash(dst, &env->tx->' + direction + 'ScriptsHash);')

for path, before, after in fixtures:
    if before not in original(path) or before == after:
        raise AssertionError('inactive/no-op amounts fixture: ' + str(path) + ':' + before)
g.check(repo)
for path, before, after in fixtures:
    altered = original(path).replace(before, after, 1)
    def read(self, *args, **kwargs):
        return altered if self == path else original(self, *args, **kwargs)
    with patch.object(Path, 'read_text', read):
        try:
            g.check(repo)
        except ValueError:
            pass
        else:
            raise AssertionError('accepted amounts source corruption: ' + str(path) + ':' + before)
g.check(repo)
print(str(len(fixtures)) + ' amounts serializer/pairing/primitive/loop/C/full-contract corruptions rejected')
