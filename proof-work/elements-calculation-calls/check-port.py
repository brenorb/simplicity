"""Read-only byte-exact audit of the small proof-support port, not acceptance."""
import importlib.util
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('port_support', HERE.parent / 'elements-count/support.py')
s = importlib.util.module_from_spec(sp)
sp.loader.exec_module(s)


def expected():
    r = s.REPO
    field = (r / 'Coq/elements-env/C/jet_elements_env_field_eval.v').read_text().split(
        'Lemma envu_rawElementsBuffer_buf :')[0]
    field = ('(** Generic field-evaluation proof prefix from the environment support, checked here for the original Elements program; raw-environment field facts are not imported. *)\n'
             + field)
    field = field.replace('Require Import C.jets_sha C.jet_sha_linkage.',
                          'Require Import C.jets_sha C.jet_sha_linkage C.jet_sha_add_n_init.')
    local = (r / 'Coq/elements-sha/C/jet_elements_make_tapleaf_exec.v').read_text().split(
        'Lemma el_eval_local_mid_s ')[1].split('Qed.')[0]
    field += '\nLemma calc_eval_local_mid_s ' + local + 'Qed.\n'
    asset = (r / 'Coq/elements-env/C/jet_elements_env_calc.v').read_text().replace(
        'C.jet_elements_env_field_eval C.jet_elements_make_tapleaf_exec',
        'C.jet_elements_calc_field_eval').replace('el_eval_local_mid_s', 'calc_eval_local_mid_s')
    token = (r / 'Coq/elements-env/C/jet_elements_env_calc_token.v').read_text().replace(
        'C.jet_elements_env_field_eval C.jet_elements_env_isfee C.jet_elements_env_calc',
        'C.jet_elements_calc_field_eval C.jet_elements_calculate_asset_exec')
    token = token.replace('Set Default Timeout 300.',
        'Set Default Timeout 300.\n\n(** Same proof-support Boolean encoding as the removed isFee import. *)\nDefinition b2i (c : bool) : int := if c then Int.one else Int.zero.')
    return {'jet_elements_calc_field_eval': field, 'jet_elements_calculate_asset_exec': asset,
        'jet_elements_calculate_token_exec': token,
        'jet_env_store_words': (r / 'Coq/elements-env/C/jet_env_store_words.v').read_text(),
        'jet_elements_sha_program': (r / 'Coq/elements-sha/C/jet_elements_sha_program.v').read_text(),
        'jet_elements_issuance_calc_spec': (r / 'proof-work/elements-issuance-computed/source/jet_elements_issuance_calc_spec.v.source').read_text(),
        'jet_elements_calc_registers': (r / 'proof-work/elements-issuance-registers/Registers.v.source').read_text()}


def check(actual, want):
    if actual != want:
        raise ValueError('proof port differs from the explicitly reviewed transformations')
    for n, source in actual.items():
        s.safe_source(source, n)


def main():
    want = expected()
    actual = {p.name.removesuffix('.v.source'): p.read_text() for p in (HERE / 'source').glob('*.v.source')}
    check(actual, want)
    mutations = [
        ('jet_elements_calculate_asset_exec', 'ent ++ repeat Int.zero 8', 'ent ++ repeat Int.zero 7'),
        ('jet_elements_calculate_asset_exec', '(Hmodel : memcpy_model)', '(Hmodel : True)'),
        ('jet_elements_calculate_token_exec', 'Int.eq (Int.repr 2) pfx', 'Int.eq (Int.repr 4) pfx'),
        ('jet_elements_calculate_token_exec', 'if c then Int.one else Int.zero', 'if c then Int.zero else Int.one'),
        ('jet_elements_sha_program', 'jets_sha.prog = jets_elements.prog', 'jets_sha.prog = jets_sha.prog'),
        ('jet_elements_calc_field_eval', 'envu_field_at _sha256_midstate _s 0', 'envu_field_at _sha256_midstate _s 4'),
        ('jet_elements_calc_registers', 'Int.repr 16777216', 'Int.repr 16777217'),
        ('jet_elements_issuance_calc_spec', '(2 ^ 248)', '(2 ^ 247)'),
    ]
    for name, old, new in mutations:
        if old not in actual[name]:
            raise ValueError('negative fixture no longer applies: ' + old)
        bad = dict(actual)
        bad[name] = bad[name].replace(old, new, 1)
        try:
            check(bad, want)
        except ValueError:
            continue
        raise ValueError('accepted a changed proof-port fixture: ' + old)
    print('Exact seven-source proof port matches; eight in-memory mutations rejected; no acceptance claimed')


if __name__ == '__main__':
    main()
