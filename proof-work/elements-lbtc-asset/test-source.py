"""In-memory constant/endian/source/full-contract mutations; no invalid compilation."""
import importlib.util
from pathlib import Path
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('lbtc_source_negative', HERE / 'check-source.py')
g = importlib.util.module_from_spec(sp)
sp.loader.exec_module(g)
repo = Path(sys.argv[1]).resolve()
proof = repo / 'Coq/C/jet_elements_lbtc_asset_local.v'
execution = repo / 'Coq/C/jet_elements_lbtc_asset_exec.v'
fixtures = [
    (repo / 'Haskell/Simplicity/Elements/Jets.hs', 'specificationIssuance LbtcAsset = Prog.lbtcAsset', 'specificationIssuance LbtcAsset = Prog.calculateAsset'),
    (repo / 'Haskell/Core/Simplicity/Programs/Elements/Lib.hs', 'lbtcAsset = Elements.lbtcAsset Elements.lib', 'lbtcAsset = Elements.calculateAsset Elements.lib'),
    (repo / 'Haskell/Core/Simplicity/Programs/Elements.hs', 'review (over le256) ' + g.CONSTANT, 'review (over be256) ' + g.CONSTANT),
    (repo / 'Haskell/Core/Simplicity/Programs/Elements.hs', g.CONSTANT, g.CONSTANT[:-1] + 'e'),
    (repo / 'Haskell/Core/Simplicity/Digest.hs', 'le256 = adapter rev rev . be256', 'le256 = be256'),
    (repo / 'Haskell/Core/Simplicity/Digest.hs', 'BS.reverse . BSS.fromShort', 'id . BSS.fromShort'),
    (repo / 'Haskell/Core/Simplicity/Word.hs', 'put a3 >> put a2 >> put a1 >> put a0', 'put a0 >> put a1 >> put a2 >> put a3'),
    (proof, g.CONSTANT, g.CONSTANT[:-1] + 'e'),
    (proof, '(List.seq 0 32)', '(List.seq 0 31)'),
    (proof, '(8 * Z.of_nat i)', '(8 * (31 - Z.of_nat i))'),
    (proof, '[hw3 w; hw2 w; hw1 w; hw0 w]', '[hw0 w; hw1 w; hw2 w; hw3 w]'),
    (proof, 'haskell_to_word 8', 'haskell_to_word 7'),
    (proof, 'Alg.scribe lbtc_asset_literal', 'Alg.scribe (fromZ 0)'),
    (proof, 'lbtc_asset_bytes = rev (haskell_word256_be_bytes', 'lbtc_asset_bytes = (haskell_word256_be_bytes'),
    (execution, '1834097720', '1834097721'),
    (repo / 'C/elements/elementsJets.c', '0x6d521c38u', '0x6d521c39u'),
]
text = proof.read_text()
start = text.index('Theorem elements_lbtc_asset_local_spec :')
stop = text.index('Proof.', start)
statement = text[start:stop]
for old, new in [('application_jet_local_spec_sep', 'False -> application_jet_local_spec_sep'),
                 ('f_simplicity_lbtc_asset', 'f_simplicity_internal_key'),
                 ('elements_ge Elements.env', 'elements_ge Bitcoin.env'),
                 ('Ty.Unit Word256', 'Ty.Unit Word128'),
                 ('fp = []', 'False'),
                 ('Some (@lbtc_asset_spec Alg.CoreFunSem a)', 'Some (fromZ 0)')]:
    assert old in statement
    fixtures.append((proof, statement, statement.replace(old, new, 1)))
original = Path.read_text
g.check(repo)
for path, old, new in fixtures:
    text = original(path)
    assert old in text, ('inactive fixture', old)
    altered = text.replace(old, new, 1)
    def read(self, *a, **kw):
        return altered if self == path else original(self, *a, **kw)
    with patch.object(Path, 'read_text', read):
        try:
            g.check(repo)
        except ValueError:
            pass
        else:
            raise AssertionError('accepted lbtc source corruption: ' + old)
g.check(repo)
print(str(len(fixtures)) + ' canonical-constant/endian/limb/source/whole-C-contract corruptions rejected')
