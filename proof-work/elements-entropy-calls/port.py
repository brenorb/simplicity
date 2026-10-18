"""Byte-exact, proof-only port for the original Elements entropy helper.

Only import/local-array-lemma names change. The environment-only hashBuffer
execution is not imported; its pure hash_buffer_regs definition is extracted.
"""
import importlib.util
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('entropy_port_base', HERE.parent / 'elements-calculation-calls/basis.py')
b = importlib.util.module_from_spec(sp)
sp.loader.exec_module(b)
s, g = b.s, b.g
NAMES = ['jet_elements_env_ctxo', 'jet_elements_env_ctxo_more',
    'jet_elements_env_ctxo_uchars', 'jet_elements_env_le32_write',
    'jet_elements_env_u32le_exec', 'jet_elements_env_ctxo_le',
    'jet_elements_env_tx_calls', 'jet_elements_env_entropy']
MODEL = 'jet_elements_entropy_hash_model'
ROOT = 'C.jet_elements_env_entropy'


def expected():
    result = {}
    for n in NAMES:
        source = (s.REPO / 'Coq/elements-env/C' / (n + '.v')).read_text()
        for old, new in [
            ('C.jet_elements_env_field_eval', 'C.jet_elements_calc_field_eval'),
            ('C.jet_elements_make_tapleaf_exec', 'C.jet_elements_calc_field_eval'),
            ('C.jet_elements_env_hashbuffer', 'C.' + MODEL),
            ('C.jet_elements_env_calc', 'C.jet_elements_calculate_asset_exec'),
            ('el_eval_local_mid_s', 'calc_eval_local_mid_s')]:
            source = source.replace(old, new)
        result[n] = source
    hb = (s.REPO / 'Coq/elements-env/C/jet_elements_env_hashbuffer.v').read_text()
    definition = 'Definition hash_buffer_regs' + hb.split('Definition hash_buffer_regs', 1)[1].split('Definition hb_env', 1)[0]
    result[MODEL] = '''(** Pure hash formula extracted verbatim; no environment-unit execution imported. *)
From Coq Require Import ZArith List.
From compcert Require Import Integers.
Require Import C.jet_sha256_iv_init C.jet_sha_uchars_prep C.jet_sha_ctx_abs C.jet_sha_finalize_exec.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
\n''' + definition
    return result


def check(actual):
    if actual != expected():
        raise ValueError('entropy proof port differs from reviewed import-only transformations')
    for n, source in actual.items():
        s.safe_source(source, n)


def prepare(work):
    b.tree(work)
    want = expected()
    for n in want:
        if (work / 'Coq/C' / (n + '.v')).exists():
            raise ValueError('new entropy port would overwrite a source: ' + n)
    check(want)
    s.changed({**{HERE / 'source' / (n + '.v.source'): text for n, text in want.items()},
               **{work / 'Coq/C' / (n + '.v'): text for n, text in want.items()}})
    print('Prepared nine exact proof-support sources; no compilation or equivalence claimed', flush=True)


def audit():
    actual = {p.name.removesuffix('.v.source'): p.read_text() for p in (HERE / 'source').glob('*.v.source')}
    check(actual)
    tests = [
        ('jet_elements_env_entropy', '(Hmodel : memcpy_model)', '(Hmodel : True)'),
        ('jet_elements_env_entropy', 'entropy_regs txid ix con', 'entropy_regs con ix txid'),
        ('jet_elements_env_entropy', 'oop + 32', 'oop + 24'),
        ('jet_elements_env_le32_write', 'Definition c_le32_bytes', 'Definition c_be32_bytes'),
        (MODEL, 'sha_pad (Int64.repr', 'sha_pad (Int64.add Int64.one'),
    ]
    for n, old, new in tests:
        if old not in actual[n]:
            raise ValueError('mutation fixture does not apply: ' + old)
        changed = dict(actual)
        changed[n] = changed[n].replace(old, new, 1)
        try:
            check(changed)
        except ValueError:
            continue
        raise ValueError('entropy port guard accepted a changed proof')
    print('Nine-source exact proof port checked; five in-memory mutations rejected', flush=True)


if __name__ == '__main__':
    if len(sys.argv) == 3 and sys.argv[1] == 'prepare':
        prepare(Path(sys.argv[2]).resolve())
    elif len(sys.argv) == 2 and sys.argv[1] == 'check':
        audit()
    else:
        raise ValueError('usage: port.py prepare PRIVATE_TREE | check')
