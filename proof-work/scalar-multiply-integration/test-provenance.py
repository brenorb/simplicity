"""Keep future/unrelated namespace archives out of the historical collector."""
import importlib.util
from pathlib import Path
import sys

sys.dont_write_bytecode = True
spec = importlib.util.spec_from_file_location('multiply_provenance', Path(__file__).with_name('assemble-candidate.py'))
assembler = importlib.util.module_from_spec(spec); spec.loader.exec_module(assembler)


def record(**kw):
    return {'file': 'example.v', 'sha256': 'checked', 'results': ['example'], **kw}


known = [record(module=prefix + 'example') for prefix in assembler.PREFIXES]
legacy = record(name='MulC.legacy')
unrelated = [record(module='BorrowC.new'), record(module='SqLitC.new'),
             record(module='C.new'), record(module=123), record(name='unqualified')]
data = {'nested': [*known, legacy, {'future': unrelated}]}
actual = list(assembler.module_records(data))
assert actual == known + [{**legacy, 'module': 'MulC.legacy'}]
assert list(assembler.module_records({'module': 'OwnC.incomplete', 'file': 'x.v'})) == []
print('multiplication provenance: four supported namespaces and legacy records retained; six unrelated/incomplete records ignored')
