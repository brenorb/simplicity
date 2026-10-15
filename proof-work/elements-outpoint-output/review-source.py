"""Review supplementary canonical correspondence; retain the earlier checkpoint."""
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    return m


checkpoint = load('indexed_source_checkpoint', HERE / 'review.py')
s = checkpoint.s
TOOLS = ['check-source.py', 'test-source.py', 'prepare-source.py']


def commands(work):
    coq = work / 'Coq'
    literal = coq / 'C/jet_elements_indexed_literal.v'
    return {
        'source': [sys.executable, '-B', str(HERE / 'check-source.py'), '--repo', str(work), '--coq', str(coq), '--literal', str(literal)],
        'source-negative': [sys.executable, '-B', str(HERE / 'test-source.py'), str(work), str(coq), str(literal)],
        'ast': ['bash', 'C/check-elements-jets-generation.sh'],
    }


def review():
    original = checkpoint.review()
    r = json.loads((HERE / 'PREPARATION.json').read_text())
    checked = json.loads((HERE / 'CHECKED.json').read_text())
    work = Path(checked['candidate'])
    if (r['candidate'] != str(work) or r['candidate_input_sha256'] != checked['candidate_input_sha256'] or
            r['checkpoint_sha256'] != s.sha((HERE / 'CHECKED.json').read_bytes()) or
            r['checkpoint_review_sha256'] != s.sha((HERE / 'EVIDENCE-REVIEW.json').read_bytes()) or
            r['canonical_source_review_complete'] is not True or r['normal_registration'] is not False or
            r['coverage_added'] != 0 or r['full_acceptance'] is not False):
        raise ValueError('wrong supplementary correspondence/acceptance scope')
    gate = load('indexed_source_replay', HERE / 'check-source.py')
    actual = gate.check(work, work / 'Coq', work / 'Coq/C/jet_elements_indexed_literal.v')
    expected_jets = ['Elements.InputPrevOutpoint', 'Elements.CurrentPrevOutpoint', 'Elements.OutputScriptHash']
    if (r['source_correspondence'] != actual or actual['selected_jets'] != expected_jets or
            any(actual[n] is not True for n in ['outpoint_tuple_conversion_reviewed', 'output_script_digest_reviewed',
                                               'whole_contracts_reviewed', 'index_and_digest_conversion_reviewed']) or
            any(actual[n] is not False for n in ['caller_cache_construction_proved', 'formal_host_crypto_equivalence',
                                                'kernel_checked_by_this_tool', 'normal_registration'])):
        raise ValueError('selected source correspondence changed or overclaimed')
    if (set(r['commands']) != set(commands(work)) or
            r['tools_sha256'] != {n: s.sha((HERE / n).read_bytes()) for n in TOOLS}):
        raise ValueError('source checker inventory/tool drift')
    for n, command in commands(work).items():
        row = r['commands'][n]
        if (row['command'] != command or row['exit_code'] != 0 or
                row['log_sha256'] != s.sha((work / (n + '.log')).read_bytes()) or
                (HERE / (n + '.log')).read_bytes() != (work / (n + '.log')).read_bytes()):
            raise ValueError('source/negative/AST command/status/log evidence differs')
    return {**original, 'canonical_source_review_complete': True, 'selected_jets': expected_jets,
            'normal_registration': False, 'coverage_added': 0, 'full_acceptance': False}


if __name__ == '__main__':
    print(json.dumps(review(), indent=2))
