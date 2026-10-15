"""Mutate byte semantics/contracts in memory; never compile invalid text."""
import importlib.util
from pathlib import Path
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('tapleaf_negative_source', HERE / 'check-source.py')
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)
repo, coq, literal = map(Path, sys.argv[1:])
gate.check(repo, coq, literal)
fixtures = [
    (repo / 'Haskell/Simplicity/Elements/Jets.hs',
     'specificationTransaction TapleafVersion = primitive Prim.TapleafVersion',
     'specificationTransaction TapleafVersion = primitive Prim.InternalKey'),
    (repo / 'Haskell/Elements/Simplicity/Elements/Primitive.hs',
     'interpret TapleafVersion = element . return . toWord8 . toInteger . tapleafVersion $ envTap env',
     'interpret TapleafVersion = element . return . toWord16 . toInteger . tapleafVersion $ envTap env'),
    (repo / 'Haskell/Elements/Simplicity/Elements/Primitive.hs', 'element = const', 'element = const . const'),
    (repo / 'Haskell/Elements/Simplicity/Elements/DataTypes.hs', 'tapleafVersion :: Word8', 'tapleafVersion :: Word32'),
    (repo / 'Haskell/Core/Simplicity/Ty/Word.hs', 'word8 = vector8', 'word8 = vector4'),
    (repo / 'Haskell/Core/Simplicity/Ty/Word.hs', 'toWord8 = toWord word8', 'toWord8 = toWord word16'),
    (coq / 'C/jet_elements_prim.v',
     '| TapleafVersion => fun _ => Some (fromZ (Byte.unsigned (tapleafVersion (envTap e))))',
     '| TapleafVersion => fun _ => Some (fromZ (Byte.signed (tapleafVersion (envTap e))))'),
    (coq / 'C/jet_elements_tapleaf_version_local.v',
     '(tbase + 169) = Some (Vint (Int.repr', '(tbase + 168) = Some (Vint (Int.repr'),
    (literal, 'haskell_to_word 3 (Byte.unsigned', 'haskell_to_word 4 (Byte.unsigned'),
    (literal, 'Theorem elements_tapleaf_version_literal_local_spec :',
     'Theorem elements_tapleaf_version_literal_local_spec : False ->'),
    (literal, 'application_jet_local_spec_sep f_simplicity_tapleaf_version',
     'application_jet_local_spec_sep f_simplicity_version'),
    (literal, 'elements_ge Elements.env Ty.Unit Word8', 'elements_ge Bitcoin.env Ty.Unit Word8'),
    (literal, 'elements_ge Elements.env Ty.Unit Word8', 'elements_ge Elements.env Ty.Unit Word16'),
]
original = Path.read_text
for path, old, new in fixtures:
    text = original(path)
    if old not in text:
        raise AssertionError('inactive tapleaf fixture: ' + old)
    altered = text.replace(old, new, 1)
    def read(self, *args, **kwargs):
        return altered if self == path else original(self, *args, **kwargs)
    with patch.object(Path, 'read_text', read):
        try:
            gate.check(repo, coq, literal)
        except ValueError:
            pass
        else:
            raise AssertionError('accepted tapleaf corruption: ' + old)
gate.check(repo, coq, literal)
print(str(len(fixtures)) + ' byte-primitive/source/representation/full-C-contract corruptions rejected')
