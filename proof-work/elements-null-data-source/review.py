"""Bind selected source review to checked complete-C and parser evidence.

No normal coverage is added here. The formal evidence receipt is immutable;
this separate receipt records the subsequently completed source review.
"""
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
PROOF = HERE.parent / 'elements-null-data-literal'


def load(name, path):
    sp = importlib.util.spec_from_file_location(name, path)
    m = importlib.util.module_from_spec(sp)
    sp.loader.exec_module(m)
    return m


formal = load('null_data_formal_review', PROOF / 'review.py')
s = formal.s
source = load('null_data_source_review', HERE / 'check-source.py')
TOOLS = [HERE / n for n in ['check-source.py', 'source-model.py', 'test-source.py', 'review.py']]
TOOLS += [HERE.parent / n for n in [
    'elements-hash-literal/check-source.py', 'elements-sequence-review/check-source.py']]


def tool_hashes(work):
    paths = TOOLS + [work / 'Coq/check-secp-predicates-specification.py']
    return {str(p): s.sha(p.read_bytes()) for p in paths}


def proof_review(work):
    result = formal.review(work)
    r = json.loads((PROOF / 'EVIDENCE-REVIEW.json').read_text())
    if (r['review'] != result or
        r['checked_sha256'] != s.sha((PROOF / 'CHECKED.json').read_bytes()) or
        r['launch_sha256'] != s.sha((PROOF / 'RUN.json').read_bytes()) or
        r['candidate_input_sha256'] != s.inputs.fingerprint(work / 'Coq', work) or
        any(r[n] is not False for n in ['canonical_source_gate_complete', 'normal_registration', 'full_acceptance']) or
        r['tools_sha256'] != {n: s.sha((PROOF / n).read_bytes()) for n in ['check.py', 'review.py', 'test-review.py']}):
        raise ValueError('formal proof/evidence receipt differs')
    expected = [sys.executable, '-B', str(PROOF / 'test-review.py'), str(work)]
    if set(r['commands']) != {'evidence-tests'}:
        raise ValueError('wrong formal evidence-test inventory')
    row = r['commands']['evidence-tests']
    log = work / 'evidence-tests.log'
    if (row['command'] != expected or row['exit_code'] != 0 or
        row['log_sha256'] != s.sha(log.read_bytes()) or
        (PROOF / log.name).read_bytes() != log.read_bytes() or
        '41' not in log.read_text()):
        raise ValueError('formal negative-test command/log differs')
    return result


def review(work):
    proof = proof_review(work)
    selected = source.check(work)
    return dict(candidate=str(work), formal_review=proof, selected_source_review=selected,
        canonical_null_data_source_review_complete=True, parser_fuel_adequacy_proved=True,
        whole_c_endpoint_checked=True, caller_environment_construction_proved=False,
        formal_host_library_equivalence=False, normal_registration=False, coverage_added=0,
        full_acceptance=False)


def verify(work):
    r = json.loads((HERE / 'SOURCE-REVIEW.json').read_text())
    if (r['review'] != review(work) or r['tools_sha256'] != tool_hashes(work) or
        r['proof_checked_sha256'] != s.sha((PROOF / 'CHECKED.json').read_bytes()) or
        r['proof_evidence_sha256'] != s.sha((PROOF / 'EVIDENCE-REVIEW.json').read_bytes()) or
        r['candidate_input_sha256'] != s.inputs.fingerprint(work / 'Coq', work) or
        r['main_inputs'] != s.input_map() or r['staged_patch_sha256'] != s.index_hash()):
        raise ValueError('source review provenance/source/index differs')
    commands = {n: [sys.executable, '-B', str(HERE / f), str(work)] for n, f in
                [('source-check', 'check-source.py'), ('source-tests', 'test-source.py')]}
    if set(r['commands']) != set(commands):
        raise ValueError('wrong source-check command inventory')
    for n, command in commands.items():
        row, log = r['commands'][n], work / (n + '.log')
        if (row['command'] != command or row['exit_code'] != 0 or
            row['log_sha256'] != s.sha(log.read_bytes()) or
            (HERE / log.name).read_bytes() != log.read_bytes()):
            raise ValueError('source-check terminal command/log differs')
    if json.loads((work / 'source-check.log').read_text()) != r['review']['selected_source_review']:
        raise ValueError('source-check log/result differs')
    if (work / 'source-tests.log').read_text().strip() != (
        '113 null-data parser/constructor/environment/whole-C-contract corruptions rejected'):
        raise ValueError('wrong negative source-test result')
    return r['review']


def finish(work):
    if (HERE / 'SOURCE-REVIEW.json').exists():
        raise ValueError('review already recorded; verify it instead')
    before, index = s.input_map(), s.index_hash()
    fingerprint, tools = s.inputs.fingerprint(work / 'Coq', work), tool_hashes(work)
    result = review(work)
    commands = {n: s.run(work, [sys.executable, '-B', str(HERE / f), str(work)], n, 600)
                for n, f in [('source-check', 'check-source.py'), ('source-tests', 'test-source.py')]}
    if (review(work) != result or s.input_map() != before or s.index_hash() != index or
        s.inputs.fingerprint(work / 'Coq', work) != fingerprint or tool_hashes(work) != tools):
        raise ValueError('proof/source/tool/main/index drift during source review')
    r = dict(review=result, proof_checked_sha256=s.sha((PROOF / 'CHECKED.json').read_bytes()),
        proof_evidence_sha256=s.sha((PROOF / 'EVIDENCE-REVIEW.json').read_bytes()),
        candidate_input_sha256=fingerprint, tools_sha256=tools, main_inputs=before,
        staged_patch_sha256=index, commands=commands)
    s.changed({HERE / 'SOURCE-REVIEW.json': json.dumps(r, indent=2) + '\n',
               **{HERE / (n + '.log'): (work / (n + '.log')).read_text() for n in commands}})
    verify(work)
    print('Null-data selected source review verified; 113 corruptions rejected; no normal admission', flush=True)


if __name__ == '__main__':
    if len(sys.argv) != 3 or sys.argv[1] not in ['finish', 'verify']:
        raise ValueError('usage: review.py finish|verify PRIVATE_TREE')
    work = Path(sys.argv[2]).resolve()
    if sys.argv[1] == 'finish':
        finish(work)
    else:
        print(json.dumps(verify(work), indent=2))
