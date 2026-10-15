"""In-memory source/limb/contract corruptions; never compile bad proofs."""
import importlib.util
from pathlib import Path
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('negative_hash_source', HERE / 'check-source.py')
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)
repo, coq, helper, endpoint = map(Path, sys.argv[1:])
gate.check(repo, coq, helper, endpoint)
fixtures = [
    (repo / 'Haskell/Core/Simplicity/Digest.hs', '(n `shiftL` 8)', '(n `shiftL` 16)'),
    (repo / 'Haskell/Core/Simplicity/Digest.hs', "foldl' go 0", "foldl' go 1"),
    (repo / 'Haskell/Core/Simplicity/Digest.hs', 'getShortByteString 32', 'getShortByteString 16'),
    (repo / 'Haskell/Core/Simplicity/Word.hs', 'Word256 !Word64 !Word64 !Word64 !Word64', 'Word256 !Word32 !Word32 !Word32 !Word32'),
    (repo / 'Haskell/Core/Simplicity/Word.hs', 'toInteger a0 + 2^64*', 'toInteger a3 + 2^64*'),
    (repo / 'Haskell/Core/Simplicity/Word.hs', '(.|.) = pointwiseBinary (.|.)', '(.|.) = pointwiseBinary (.&.)'),
    (repo / 'Haskell/Core/Simplicity/Ty/Word.hs', 'toWord256 = toWord word256', 'toWord256 = toWord word128'),
    (repo / 'Haskell/Elements/Simplicity/Elements/Primitive.hs', 'encodeHash = toWord256 . integerHash256', 'encodeHash = toWord128 . integerHash256'),
    (helper, '18446744073709551616', '4294967296'),
    (helper, 'let a3 := a2 / haskell_word64_modulus', 'let a3 := a1 / haskell_word64_modulus'),
    (helper, '(Z.lor (hw0 x) (hw0 y))', '(Z.lor (hw0 x) (hw1 y))'),
    (helper, '(Z.shiftl (haskell_word256_integer w) 8)', '(Z.shiftl (haskell_word256_integer w) 16)'),
    (helper, 'haskell_be256_run bytes (haskell_word256_from_integer 0)', 'haskell_be256_run bytes (haskell_word256_from_integer 1)'),
    (coq / 'C/jet_elements_script_cmr_local.v', '(tbase + 136) (hash256_reg', '(tbase + 128) (hash256_reg'),
    (coq / 'C/jet_elements_genesis_hash_local.v', '(ebase + 16) (hash256_reg', '(ebase + 24) (hash256_reg'),
    (endpoint, 'Theorem elements_script_cmr_literal_local_spec :', 'Theorem elements_script_cmr_literal_local_spec : False ->'),
    (endpoint, 'f_simplicity_genesis_block_hash elements_ge', 'f_simplicity_script_cmr elements_ge'),
    (endpoint, 'elements_ge Elements.env', 'elements_ge Bitcoin.env'),
    (endpoint, 'haskell_to_word 8 (haskell_integer_hash256', 'haskell_to_word 7 (haskell_integer_hash256'),
]
original = Path.read_text
for path, old, new in fixtures:
    text = original(path)
    if old not in text:
        raise AssertionError('inactive hash source fixture: ' + old)
    altered = text.replace(old, new, 1)
    def read(self, *args, **kwargs):
        return altered if self == path else original(self, *args, **kwargs)
    with patch.object(Path, 'read_text', read):
        try:
            gate.check(repo, coq, helper, endpoint)
        except ValueError:
            pass
        else:
            raise AssertionError('accepted hash source corruption: ' + old)
gate.check(repo, coq, helper, endpoint)
print(str(len(fixtures)) + ' digest/limb/primitive/representation/whole-C-contract corruptions rejected')
