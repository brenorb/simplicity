"""In-memory mutations of the selected Version correspondence/public boundary."""
import importlib.util
from pathlib import Path
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
archive = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('version_source_test', archive / 'check-version-source.py')
gate = importlib.util.module_from_spec(spec); spec.loader.exec_module(gate)
repo, coq = map(Path, sys.argv[1:])
gate.check(repo, coq)
root = coq / 'C/jet_elements_version_local.v'
canonical = coq / 'C/jet_elements_version_canonical.v'
port = coq / 'C/jet_elements_prim.v'
hs_prim = repo / 'Haskell/Elements/Simplicity/Elements/Primitive.hs'
hs_jets = repo / 'Haskell/Simplicity/Elements/Jets.hs'
unit = coq / 'C/jet_elements_translation_unit.c'
fixtures = [
    (root, 'f_simplicity_version elements_ge', 'f_simplicity_lock_time elements_ge'),
    (root, 'elements_ge Elements.env', 'ge0 Elements.env'),
    (root, 'Elements.env Ty.Unit Word32', 'Elements.env Ty.Unit Word64'),
    (root, 'Theorem elements_version_local_spec :', 'Theorem elements_version_local_spec : False ->'),
    (root, 'Theorem elements_version_local_spec :',
     'Theorem elements_version_local_spec : True. Proof. exact I. Qed.\nTheorem elements_version_local_spec :'),
    (root, 'txbase + 720', 'txbase + 728'),
    (root, 'exists be ebase bt txbase version,', 'False /\\ exists be ebase bt txbase version,'),
    (root, 'elements_version_env_rep\n', 'wrong_env_rep\n'),
    (canonical, 'Primitive.Combinators.prim Elements.Version', 'Primitive.Combinators.prim Elements.LockTime'),
    (port, 'primName : string := "Elements"', 'primName : string := "Bitcoin"'),
    (port, '| Version => "version"', '| Version => "different"'),
    (port, '| Version => fun _ => Some (fromZ (Int.unsigned (sigTxVersion tx)))',
     '| Version => fun _ => None'),
    (port, 'let tx := envTx e in', 'let tx := otherTx e in'),
    (hs_prim, 'interpret Version = element . return . toWord32 . toInteger $ sigTxVersion tx',
     'interpret Version = element . return . toWord32 . toInteger $ sigTxLock tx'),
    (hs_prim, 'primPrefix = "Elements"', 'primPrefix = "Other"'),
    (hs_jets, 'specificationTransaction Version = primitive Prim.Version',
     'specificationTransaction Version = primitive Prim.LockTime'),
    (unit, '#include "../../C/elements/elementsJets.c"', '#include "replacement.c"'),
]
original = Path.read_text
for target, old, new in fixtures:
    text = original(target)
    if old not in text:
        raise AssertionError('missing active mutation fixture: ' + old)
    changed = text.replace(old, new, 1)
    def read(path, *args, **kwargs):
        return changed if path == target else original(path, *args, **kwargs)
    with patch.object(Path, 'read_text', read):
        try:
            gate.check(repo, coq)
        except ValueError:
            pass
        else:
            raise AssertionError('version correspondence mutation accepted: ' + old)
gate.check(repo, coq)
print(f'{len(fixtures)} Version source/public boundary mutations rejected; all inputs unchanged')

