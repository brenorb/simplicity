"""Read-only negative fixtures for the batch's evidence checks."""
import importlib.util
from pathlib import Path
import sys

sys.dont_write_bytecode = True
spec = importlib.util.spec_from_file_location('foundation_check', Path(__file__).with_name('check.py'))
check = importlib.util.module_from_spec(spec)
spec.loader.exec_module(check)


def rejects(callback):
    try:
        callback()
    except (ValueError, IndexError):
        return
    raise AssertionError('corrupt evidence was accepted')


name = 'C.example.result'
closed = 'FOUNDATION_ASSUMPTIONS ' + name + '\nClosed under the global context\n'
assert check.parse_assumptions(closed, [name]) == {name: []}
inherited = 'FOUNDATION_ASSUMPTIONS ' + name + '\nAxioms:\nClassical_Prop.classic : forall P, P \\/ ~P\n'
assert check.parse_assumptions(inherited, [name]) == {name: ['Classical_Prop.classic']}
assert check.parse_assumptions(inherited + 'FOUNDATION_TYPE ' + name + '\nC.example.result : True\n', [name]) == {name: ['Classical_Prop.classic']}
rejects(lambda: check.parse_assumptions(closed + closed, [name]))
rejects(lambda: check.parse_assumptions(closed, [name, 'C.other.missing']))
rejects(lambda: check.parse_assumptions(closed, []))
rejects(lambda: check.parse_assumptions(inherited.replace('Classical_Prop.classic', 'Invented.axiom'), [name]))
rejects(lambda: check.parse_assumptions('Axioms:\nInvented.axiom : True\n', []))

safe = '\n'.join(['Constants/Inductives relying on type-in-type: <none>',
                  'unsafe (co)fixpoints: <none>', 'positivity is assumed: <none>', '* Axioms:'])
safe += '\n' + (check.REPO / 'Coq/C/jet_coqchk_axioms.expected').read_text() + '\n'
check.kernel(safe)
for marker in ['type-in-type: <none>', 'unsafe (co)fixpoints: <none>', 'positivity is assumed: <none>']:
    rejects(lambda marker=marker: check.kernel(safe.replace(marker, marker.replace('<none>', 'UNSAFE'))))
rejects(lambda: check.kernel(safe.replace('* Axioms:', '* Other:')))
rejects(lambda: check.kernel(safe.replace('* Axioms:', '* Axioms:\nInvented.axiom')))
record = 'FOUNDATION_TYPE ' + name + '\nC.example.result : True\n'
check.contract_records(record, [('TYPE', name)])
rejects(lambda: check.contract_records(record, []))
rejects(lambda: check.contract_records(record + record, [('TYPE', name)]))
rejects(lambda: check.contract_records(record + '...', [('TYPE', name)]))
print('foundation evidence negative fixtures passed: 13')
