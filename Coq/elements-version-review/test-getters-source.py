"""In-memory selected getter boundary/semantics corruption fixtures."""
import importlib.util
from pathlib import Path
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
spec = importlib.util.spec_from_file_location('getter_guard', Path(__file__).with_name('check-getters-source.py'))
gate = importlib.util.module_from_spec(spec); spec.loader.exec_module(gate)
repo, coq = map(Path, sys.argv[1:])
gate.check(repo, coq)
fixtures = []
for suffix, primitive, function in [('locktime', 'LockTime', 'lock_time'), ('current_index', 'CurrentIndex', 'current_index')]:
    root = coq / ('C/jet_elements_' + suffix + '_local.v')
    fixtures += [(root, 'f_simplicity_' + function + ' elements_ge', 'f_simplicity_version elements_ge'),
                 (root, 'elements_ge Elements.env', 'ge0 Elements.env'),
                 (root, 'Elements.env Ty.Unit Word32', 'Elements.env Ty.Unit Word64'),
                 (root, 'Theorem elements_' + suffix + '_local_spec :', 'Theorem elements_' + suffix + '_local_spec : False ->'),
                 (root, 'Primitive.Combinators.prim Elements.' + primitive, 'Primitive.Combinators.prim Elements.Version'),
                 (repo / 'Haskell/Simplicity/Elements/Jets.hs', 'specificationTransaction ' + primitive + ' = primitive Prim.' + primitive,
                  'specificationTransaction ' + primitive + ' = primitive Prim.Version'),
                 (coq / 'C/jet_elements_prim.v', '| ' + primitive + ' => fun _ => Some', '| ' + primitive + ' => fun _ => other')]
fixtures += [(coq / 'C/jet_elements_locktime_local.v', 'txbase + 728', 'txbase + 720'),
             (coq / 'C/jet_elements_current_index_local.v', 'ebase + 80', 'ebase + 72'),
             (coq / 'C/jet_elements_prim.v', 'let ix := envIx e in', 'let ix := otherIx e in'),
             (coq / 'C/jet_elements_prim.v', 'envIxWord32 : (Z.of_nat envIx < 4294967296)%Z', 'envIxWord32 : True'),
             (repo / 'Haskell/Elements/Simplicity/Elements/DataTypes.hs', 'type Lock = Word32', 'type Lock = Word64')]
original = Path.read_text
for target, old, new in fixtures:
    text = original(target)
    if old not in text: raise AssertionError('inactive fixture: ' + old)
    changed = text.replace(old, new, 1)
    def read(self, *args, **kwargs): return changed if self == target else original(self, *args, **kwargs)
    with patch.object(Path, 'read_text', read):
        try: gate.check(repo, coq)
        except ValueError: pass
        else: raise AssertionError('getter corruption accepted: ' + old)
print(str(len(fixtures)) + ' selected getter source mutations rejected')
