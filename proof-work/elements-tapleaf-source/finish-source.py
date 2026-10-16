"""Record exact positive/negative canonical tapleaf source evidence."""
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('tapleaf_source_finished', HERE / 'check-source.py')
g = importlib.util.module_from_spec(sp)
sp.loader.exec_module(g)
s = g.load('tapleaf_source_support', HERE.parent / 'elements-count/support.py')


def main(work):
    if (HERE / 'SOURCE-REVIEW.json').exists():
        raise ValueError('tapleaf source review already recorded; inspect its evidence')
    record_path = HERE.parent / 'elements-tapleaf/RUN.json'
    record = json.loads(record_path.read_text())
    if (record['candidate'] != str(work) or work == s.REPO or s.REPO in work.parents or
        record['candidate_input_sha256'] != s.inputs.fingerprint(work / 'Coq', work)):
        raise ValueError('fresh tapleaf proof source differs')
    inherited = HERE.parent / 'elements-stream-source'
    previous = json.loads((inherited / 'SOURCE-REVIEW.json').read_text())
    for name, digest in previous['tools_sha256'].items():
        if s.sha((inherited / name).read_bytes()) != digest:
            raise ValueError('inherited Elements source tool changed')
    before, index = s.input_map(), s.index_hash()
    result = g.check(work)
    commands = {}
    for stem, name in [('tapleaf-source', 'check-source.py'), ('tapleaf-negative', 'test-source.py')]:
        commands[stem] = s.run(work, [sys.executable, '-B', str(HERE / name), str(work)], stem, 600)
        print('Passed ' + stem, flush=True)
    if (g.check(work) != result or s.input_map() != before or s.index_hash() != index or
        s.inputs.fingerprint(work / 'Coq', work) != record['candidate_input_sha256']):
        raise ValueError('source review changed main/index/private inputs')
    evidence = dict(candidate=str(work), candidate_input_sha256=record['candidate_input_sha256'],
        compile_receipt_sha256=s.sha(record_path.read_bytes()), staged_patch_sha256=index,
        inherited_source_review_sha256=s.sha((inherited / 'SOURCE-REVIEW.json').read_bytes()),
        source_review=result, commands=commands,
        tools_sha256={n: s.sha((HERE / n).read_bytes()) for n in
            ['check-source.py', 'test-source.py', 'source-model.py', 'finish-source.py']},
        canonical_source_review_complete=True, recursive_kernel_result_checked_by_this_tool=False,
        normal_registration=False, coverage_added=0, full_acceptance=False)
    s.changed({HERE / 'SOURCE-REVIEW.json': json.dumps(evidence, indent=2) + '\n',
        **{HERE / (n + '.log'): (work / (n + '.log')).read_text() for n in commands}})
    print('Canonical Elements tapleaf source/negative review recorded; kernel/admission remain separate', flush=True)


if __name__ == '__main__':
    if len(sys.argv) != 2:
        raise ValueError('usage: finish-source.py PRIVATE_TREE')
    main(Path(sys.argv[1]).resolve())
