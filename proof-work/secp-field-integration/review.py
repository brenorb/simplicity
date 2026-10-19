"""Run the unchanged scoped FeMultiply review against the integrated endpoint."""
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('field_integration_review_assembly', HERE / 'assemble.py')
a = importlib.util.module_from_spec(sp)
sp.loader.exec_module(a)
work, receipt = a.identity()
sp = importlib.util.spec_from_file_location('unchanged_multiply_source_review',
    HERE.parent / 'secp-field-literal/check-source.py')
gate = importlib.util.module_from_spec(sp)
sp.loader.exec_module(gate)

# The checker and its ten mutations are unchanged. Substitute only the input
# reader so every fixture is derived from the actual isolated candidate.
candidate_sources = {
    'catalog': gate.p.read_code(work / 'Haskell/Core/Simplicity/CoreJets.hs'),
    'program': gate.p.read_code(work / 'Haskell/Core/Simplicity/Programs/LibSecp256k1.hs'),
    'port': gate.p.read_code(work / 'Coq/C/jet_secp_negate_literal_contract.v'),
    'jet': gate.scanner.code_only((work / 'Coq' / (receipt['root'].replace('.', '/') + '.v')).read_text()),
}
gate.sources = lambda: dict(candidate_sources)
gate.test()
