"""Regression test: exported Coq names keep apostrophes, locals stay local."""
import importlib.util
from pathlib import Path
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
spec = importlib.util.spec_from_file_location('tx_inventory_gate', Path(__file__).with_name('run.py'))
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)
meta = {'modules': [{'origin': 'fixture.v'}]}
fixture = b"""(* Lemma comment_only : True. *)
Lemma public' : True.
Local Lemma hidden : True.
Theorem headline : True.
Definition adapter' := True.
Local Definition hidden_definition := True.
"""
with patch.object(gate.stage, 'blob', return_value=fixture):
    gate.correct_inventory(meta)
entry = meta['modules'][0]
assert entry['results'] == ["public'", 'headline'], entry
assert entry['definitions'] == ["adapter'"], entry
real = {'modules': [{'origin': 'Coq/bitcoin-env/C/jet_bitcoin_env_ctxs_core.v'}]}
gate.correct_inventory(real)
assert "ctxs_sep_shape'" in real['modules'][0]['results']
assert 'ctxs_sep_shape' not in real['modules'][0]['results']
print('Primed-name/comment/local-declaration inventory regressions passed')
