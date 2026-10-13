"""Normal snapshot/dependency mutations in memory, no edited audit inputs."""
import importlib.util
import json
from pathlib import Path
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
archive = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('square_normal_test', archive / 'review-normal.py')
review = importlib.util.module_from_spec(spec); spec.loader.exec_module(review)
assembly = json.loads((archive / 'ASSEMBLY.json').read_text())
base, candidate = Path(assembly['baseline']) / 'Coq', Path(assembly['candidate']) / 'Coq'
review.contracts(assembly, base, candidate); review.dependencies(assembly, candidate)
original = Path.read_text
compact = candidate / 'C/jet_contracts.expected'
deep = candidate.parent / 'normal_deep_contracts.out'
deps = candidate.parent / 'normal_assumptions.out'
count = 0


def corrupt(path, changed, action):
    global count
    def read(p, *args, **kwargs):
        return changed if p == path else original(p, *args, **kwargs)
    with patch.object(Path, 'read_text', read):
        try:
            action()
        except ValueError:
            count += 1
        else:
            raise AssertionError('normal evidence corruption accepted')


text = original(compact)
corrupt(compact, text.replace('\n', ' \n', 1), lambda: review.contracts(assembly, base, candidate))
corrupt(compact, text + 'unknown = True\n', lambda: review.contracts(assembly, base, candidate))
full = original(deep)
marker = 'NORMAL_SQUARE_TYPE C.' + assembly['modules'][0]['name'] + '.' + assembly['modules'][0]['results'][0]
for bad in [full + '...', full.replace(marker, marker + '\n' + marker, 1),
            full.replace(marker, 'NORMAL_SQUARE_TYPE wrong', 1)]:
    corrupt(deep, bad, lambda: review.contracts(assembly, base, candidate))
raw = original(deps)
for bad in [raw + 'JET_ASSUMPTIONS pending\n',
            raw.replace('Events.external_functions_sem\n', 'new_axiom\n', 1),
            raw.replace('JET_ASSUMPTIONS ', 'JET_ASSUMPTIONS wrong.', 1)]:
    corrupt(deps, bad, lambda: review.dependencies(assembly, candidate))

definitions = [('C.jet_secp_reduce512_wide', 'wide_column'), ('C.jet_secp_reduce512_wide', 'wcolumn')]
decl = 'Variant wide_column : Type := wcolumn : wide_column.\n'
review.contract_records(decl * 2, [], definitions)
for bad, rows in [(decl, definitions),
                  (decl + 'Variant wide_column : Type := other : wide_column.\n', definitions),
                  (decl * 2, [definitions[0], ('C.wrong', 'wcolumn')])]:
    try:
        review.contract_records(bad, [], rows)
    except ValueError:
        count += 1
    else:
        raise AssertionError('constructor identity/missing Print accepted')
print(f'normal square review: positive fixtures and {count} corruption fixtures passed; no inputs changed')
