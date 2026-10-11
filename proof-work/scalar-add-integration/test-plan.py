"""In-memory regression tests for read-only declaration reconciliation."""
import importlib.util
from pathlib import Path
import sys
sys.dont_write_bytecode = True

path = Path(__file__).with_name('plan-main.py')
spec = importlib.util.spec_from_file_location('plan', path)
plan = importlib.util.module_from_spec(spec)
spec.loader.exec_module(plan)

results = [('C.left', 'same'), ('C.right', 'same')]
definitions = [('C.fix', 'find_label_app'), ('C.boundary', 'call_boundary'),
               ('C.record', 'record'), ('Simplicity.Primitive.Bitcoin', 'Bitcoin.sem'),
               ('C.legacy', 'repeat'), ('C.legacy', 'repeat')]
text = ('same\n     : nat\nright.same\n     : bool\n'
        'find_label_app =\nfix find_label_app (x : nat) := x\nfor\n'
        'find_label_app\n     : nat -> nat\nArguments find_label_app x\n'
        'Variant\ncall_boundary (x : nat) : Prop := B : call_boundary x.\n'
        'Record\nrecord (x : nat) : Type := B_record { field : nat }.\n'
        'Bitcoin.Bitcoin.sem =\nfun x => x\n     : nat -> nat\n'
        'repeat =\nO\n     : nat\nrepeat =\nO\n     : nat\n')
old = plan.contract_records(text, results, definitions)
assert len(old) == 8
assert old[-2][0] == ('DEF', 'C.legacy', 'repeat', 1)
assert old[-1][0] == ('DEF', 'C.legacy', 'repeat', 2)
assert plan.compare_contracts(old, old)['inherited_contract_bytes_identical']

count = 0
for bad in [text.replace('right.same\n     : bool\n', ''),
            text.replace('right.same\n     : bool\n', 'right.same\n     : bool\n' * 2),
            text.replace('Bitcoin.Bitcoin.sem =', 'other.sem ='),
            text.replace('call_boundary (x : nat)', 'different (x : nat)', 1)]:
    try:
        plan.contract_records(bad, results, definitions)
    except ValueError:
        count += 1
    else:
        raise AssertionError('malformed/missing/duplicate/relabelled record accepted')

# Two modules with one displayed name must remain separate records.
bad = plan.contract_records(text.replace('right.same\n     : bool',
                                         'right.same\n     : nat'), results, definitions)
report = plan.compare_contracts(old, bad)
assert not report['inherited_contract_bytes_identical']
assert [(r['module'], r['name']) for r in report['changed_contract_records']] == [('C.right', 'same')]
count += 1

# A new definition with an old short name must not become an inherited record.
new = plan.contract_records(text + 'same =\ntrue\n     : bool\n', results,
                            definitions + [('C.new', 'same')])
report = plan.compare_contracts(old, new)
assert report['inherited_contract_bytes_identical'] and report['new_contract_records'] == 1

# Retain exact bytes, both legacy occurrences and the fully qualified identity.
for index in [0, 5, 6, 7]:
    bad = list(old)
    key, chunk = bad[index]
    bad[index] = (key, chunk + '\n')
    report = plan.compare_contracts(old, bad)
    assert not report['inherited_contract_bytes_identical']
    assert report['changed_contract_records'][0]['occurrence'] == key[3]
    count += 1
for bad in [old[:-1], [old[1], old[0], *old[2:]]]:
    assert not plan.compare_contracts(old, bad)['inherited_contract_bytes_identical']
    count += 1
print(f'declaration reconciliation: positive fixtures and {count} drift fixtures passed; no audit inputs modified')
