"""Read-only tests for the actual-audit printer-context extractor."""
import importlib.util
from pathlib import Path
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('normal467_v3_printer', HERE.parent / 'normal-delta-prepare-v3.py')
g = importlib.util.module_from_spec(sp)
sp.loader.exec_module(g)
coq = Path(sys.argv[1]).resolve() / 'Coq'
original = Path.read_text
script = coq / 'audit-jet-contracts.sh'
header = g.contract_printer_header(coq)
assert 'Require C.jet_clight_forward.' in header
assert 'Require Import C.jet_clight_forward.' not in header
count = 0


def reject(path, transform):
    global count
    before = original(path)
    after = transform(before)
    if before == after:
        raise AssertionError('inactive printer fixture: ' + str(path))
    def read(self, *args, **kwargs):
        return after if self == path else original(self, *args, **kwargs)
    with patch.object(Path, 'read_text', read):
        try:
            g.contract_printer_header(coq)
        except ValueError:
            count += 1
            return
    raise AssertionError('accepted malformed printer context: ' + str(path))


start = "{\n  echo 'Set Warnings \"-notation-overridden\".'\n"
stop = "  awk '!/^#/ && NF==2 {\n"
reject(script, lambda t: t.replace(start, '{\n', 1))
reject(script, lambda t: t + start)
reject(script, lambda t: t.replace(stop, "  awk 'false {\n", 1))
reject(script, lambda t: t + stop)
reject(script, lambda t: t.replace('Set Printing Width 120.', 'Set Printing Width 121.', 1))
reject(script, lambda t: t.replace('Set Printing All.', 'Set Printing Universes.', 1))
reject(script, lambda t: t.replace('sort -u |', 'sort -ur |', 1))
reject(script, lambda t: t.replace("  echo 'Set Printing All.'", "  echo 'Require C.extra_unregistered_module.'\n  echo 'Set Printing All.'", 1))
reject(coq / 'C/jet_public_theorems.txt', lambda t: t + '\nmalformed declaration row\n')
# The expected registry and actual shell output must agree, not just contain
# individually valid Require commands. This mock adds an expected-only module.
reject(coq / 'C/jet_public_theorems.txt', lambda t: t + '\nC.extra_expected_module theorem\n')
assert g.contract_printer_header(coq) == header
print(str(count) + ' malformed/ambiguous/reordered/incomplete audit headers rejected; actual context retained')
