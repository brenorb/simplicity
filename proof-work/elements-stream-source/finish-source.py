"""Record source review independently of the running recursive kernel phase."""
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
PROOF = HERE.parent / 'elements-stream'


def load(name, path):
    sp = importlib.util.spec_from_file_location(name, path)
    m = importlib.util.module_from_spec(sp)
    sp.loader.exec_module(m)
    return m


g = load('elements_stream_source_checkpoint', PROOF / 'check.py')
s = g.s
source = load('elements_stream_selected_guard', HERE / 'check-source.py')


def main(work):
    if (HERE / 'SOURCE-REVIEW.json').exists():
        raise ValueError('Elements stream source review already recorded; inspect its evidence')
    compiled = json.loads((PROOF / 'RUN.json').read_text())
    g.tree(work)
    if (compiled['candidate'] != str(work) or compiled['whole_c_endpoints'] != 7 or
        compiled['candidate_input_sha256'] != s.inputs.fingerprint(work / 'Coq', work)):
        raise ValueError('completed Elements stream compile source boundary differs')
    for field, suffix in [('source_sha256', '.v'), ('object_sha256', '.vo')]:
        for module, digest in compiled[field].items():
            if s.sha((work / 'Coq' / (module.replace('.', '/') + suffix)).read_bytes()) != digest:
                raise ValueError('fresh stream source/object differs before source review')
    before, index = s.input_map(), s.index_hash()
    files = ['check-source.py', 'test-source.py', 'source-model.py', 'finish-source.py']
    tools = {n: s.sha((HERE / n).read_bytes()) for n in files}
    result, commands = source.check(work), {}
    for stem, script in [('stream-source', 'check-source.py'), ('stream-source-negative', 'test-source.py')]:
        commands[stem] = s.run(work, [sys.executable, '-B', str(HERE / script), str(work)], stem, 600)
        print('Passed ' + stem, flush=True)
    if (source.check(work) != result or g.tree(work)[0] != Path(compiled['base_candidate']) or
        s.inputs.fingerprint(work / 'Coq', work) != compiled['candidate_input_sha256'] or
        s.input_map() != before or s.index_hash() != index or
        {n: s.sha((HERE / n).read_bytes()) for n in files} != tools):
        raise ValueError('source review changed main/index/private inputs/tools')
    record = dict(candidate=str(work), candidate_input_sha256=compiled['candidate_input_sha256'],
        compile_receipt_sha256=s.sha((PROOF / 'RUN.json').read_bytes()),
        staged_patch_sha256=index, source_review=result, commands=commands, tools_sha256=tools,
        canonical_source_review_complete=True, recursive_kernel_result_checked_by_this_tool=False,
        normal_registration=False, coverage_added=0, full_acceptance=False)
    s.changed({HERE / 'SOURCE-REVIEW.json': json.dumps(record, indent=2) + '\n',
        **{HERE / (n + '.log'): (work / (n + '.log')).read_text() for n in commands}})
    print('Seven selected Elements programs/primitive encodings/whole-C contracts source-reviewed; kernel and admission separate', flush=True)


if __name__ == '__main__':
    main(Path(sys.argv[1]).resolve())
