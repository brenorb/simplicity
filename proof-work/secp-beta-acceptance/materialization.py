"""Correct the preparation's before-state observations additively.

The initial preparation and actual candidate remain byte-identical. Its final
fingerprint/after hashes were right, but the ten added source and two project
before hashes were sampled after materialization. Bind the true checked-parent
delta separately rather than retargeting that historical receipt.
"""
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('beta_materialization_preparation', HERE / 'prepare.py')
p = importlib.util.module_from_spec(sp)
sp.loader.exec_module(p)
s = p.s


def delta():
    r = json.loads((HERE / 'PREPARATION.json').read_text())
    work, base = Path(r['candidate']), Path(r['parent_candidate'])
    if s.inputs.fingerprint(base / 'Coq', base) != r['parent_input_sha256']:
        raise ValueError('checked parent differs from actual preparation input')
    result, corrected = {}, []
    for name, row in r['changed_inputs'].items():
        parent = base / name
        before = s.sha(parent.read_bytes()) if parent.exists() else None
        after = s.sha((work / name).read_bytes())
        if after != row['after']:
            raise ValueError('prepared candidate after-state differs: ' + name)
        result[name] = dict(before=before, after=after)
        if before != row['before']:
            corrected.append(name)
    if len(corrected) != 12 or set(corrected) != set(r['inherited_extra_sources']) | {'Coq/_CoqProject', 'Coq/_CoqProject.jets'}:
        raise ValueError('unexpected preparation bookkeeping discrepancy')
    return dict(preparation_sha256=s.sha((HERE / 'PREPARATION.json').read_bytes()),
        checker_sha256=s.sha(Path(__file__).read_bytes()), changed_inputs=result,
        corrected_before_observations=corrected, candidate_edited=False, historical_receipt_edited=False)


def check():
    r = delta()
    if json.loads((HERE / 'MATERIALIZATION.json').read_text()) != r:
        raise ValueError('corrected checked-parent materialization observations differ')
    return r


if __name__ == '__main__':
    if len(sys.argv) != 2 or sys.argv[1] not in {'record', 'check'}:
        raise SystemExit('usage: materialization.py record|check')
    if sys.argv[1] == 'record':
        if (HERE / 'MATERIALIZATION.json').exists():
            raise ValueError('materialization correction already recorded')
        s.changed({HERE / 'MATERIALIZATION.json': json.dumps(delta(), indent=2) + '\n'})
    else:
        check()
    print('Exact parent-to-candidate materialization delta checked; original receipt and proof sources unchanged')
