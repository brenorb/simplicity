"""In-memory tests of exact read-only reconciliation; no proof inputs edited."""
import importlib.util
from pathlib import Path
import sys

sys.dont_write_bytecode = True
archive = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('multiply_plan', archive / 'plan-main.py')
plan = importlib.util.module_from_spec(spec)
spec.loader.exec_module(plan)

# Run the earlier duplicate/full-identity/order/byte-drift fixtures against
# the multiply parser, rather than retesting only the obsolete parent parser.
old_test = (archive.parent / 'scalar-add-integration/test-plan.py').read_text()
start = old_test.index('\nresults = ') + 1
exec(compile(old_test[start:], str(archive.parent / 'scalar-add-integration/test-plan.py'), 'exec'),
     {'plan': plan})

definitions = [('C.jet_secp_reduce512_wide', 'wide_column'),
               ('C.jet_secp_reduce512_wide', 'wcolumn')]
declaration = 'Variant wide_column : Type := wcolumn : wide_column.\n'
records = plan.contract_records(declaration * 2, [], definitions)
assert records[0][0] == ('DEF', *definitions[0], 1)
assert records[1][0] == ('DEF', *definitions[1], 1)
assert plan.compare_contracts(records, records)['inherited_contract_bytes_identical']
for text, defs in [(declaration + 'Variant wide_column : Type := other : wide_column.\n', definitions),
                   (declaration * 2, [definitions[0], ('C.unrelated', 'wcolumn')]),
                   (declaration, definitions)]:
    try:
        plan.contract_records(text, [], defs)
    except ValueError:
        pass
    else:
        raise AssertionError('missing/misidentified constructor Print accepted')
print('multiply reconciliation: three constructor-identity mutations rejected; no files changed')
