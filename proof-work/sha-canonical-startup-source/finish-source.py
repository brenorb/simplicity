"""Record read-only SHA source fidelity only after the actual kernel receipt."""
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('sha_canonical_source_finish', HERE / 'check-source.py')
g = importlib.util.module_from_spec(sp)
sp.loader.exec_module(g)
proof = g.load('sha_canonical_completed_proof', HERE.parent / 'sha-canonical-startup/check.py')
kd = g.load('sha_canonical_completed_kernel', HERE.parent / 'sha-canonical-startup/kernel.py')
s = proof.s


def main(work):
    if (HERE / 'SOURCE-REVIEW.json').exists():
        raise ValueError('SHA source review already recorded; inspect it instead of overwriting')
    folder = proof.HERE
    compiled, launch, checked = [json.loads((folder / name).read_text()) for name in
                                 ['RUN.json', 'KERNEL-RUN.json', 'CHECKED.json']]
    if (checked != dict(compiled, commands=checked['commands'], recursive_kernel_check=True,
                        kernel_launch_sha256=s.sha((folder / 'KERNEL-RUN.json').read_bytes())) or
        checked['candidate'] != str(work) or checked['modules'] != [proof.MODULE] or
        checked['freshly_compiled_support'] != proof.SUPPORT or
        checked['tools_sha256'] != {'check.py': s.sha((folder / 'check.py').read_bytes())} or
        checked['whole_c_endpoints'] != 18 or checked['conditional_memcpy_endpoints'] != 17 or
        checked['inherited_endpoint_assumptions'] != 8 or checked['new_axioms'] != 0 or
        checked['coverage_added'] != 0 or checked['normal_registration'] is not False or
        checked['full_acceptance'] is not False):
        raise ValueError('wrong actual completed SHA source/kernel identity/scope')
    expected_launch = dict(candidate=str(work), command=kd.COMMAND,
        compiled_receipt_sha256=s.sha((folder / 'RUN.json').read_bytes()),
        candidate_input_sha256=compiled['candidate_input_sha256'],
        staged_patch_sha256=compiled['staged_patch_sha256'],
        driver_sha256=s.sha((folder / 'kernel.py').read_bytes()), recursive_kernel_check=False)
    if launch != expected_launch:
        raise ValueError('SHA kernel launch/driver/provenance differs')
    for field, suffix in [('source_sha256', '.v'), ('object_sha256', '.vo')]:
        if set(checked[field]) != set(proof.SUPPORT + [proof.MODULE]):
            raise ValueError('incomplete freshly compiled SHA source/object inventory')
        for module, digest in checked[field].items():
            path = work / 'Coq' / (module.replace('.', '/') + suffix)
            if path.is_symlink() or s.sha(path.read_bytes()) != digest:
                raise ValueError('completed SHA source/object changed')
    for stem, row in checked['commands'].items():
        log = work / (stem + '.log')
        if (row['exit_code'] != 0 or row['log_sha256'] != s.sha(log.read_bytes()) or
            (folder / log.name).read_bytes() != log.read_bytes()):
            raise ValueError('completed SHA command/exit/log differs')
    if (checked['commands']['kernel']['command'] != kd.COMMAND or
        checked['commands']['ast']['command'] != ['bash', 'C/check-sha-jets-generation.sh']):
        raise ValueError('completed SHA kernel/AST command differs')
    s.kernel.kernel((work / 'kernel.log').read_text(),
        sorted((work / 'Coq/C/jet_coqchk_axioms.expected').read_text().split()))
    proof.tree(work)
    before, index = s.input_map(), s.index_hash()
    if (before != checked['main_inputs'] or index != checked['staged_patch_sha256'] or
        s.inputs.fingerprint(work / 'Coq', work) != checked['candidate_input_sha256']):
        raise ValueError('main/index/completed private SHA source changed')
    result = g.check(work)
    commands = {}
    for stem, script in [('sha-canonical-source', 'check-source.py'), ('sha-canonical-negative', 'test-source.py')]:
        commands[stem] = s.run(work, [sys.executable, '-B', str(HERE / script), str(work)], stem, 600)
        print('Passed ' + stem, flush=True)
    if (g.check(work) != result or s.input_map() != before or s.index_hash() != index or
        s.inputs.fingerprint(work / 'Coq', work) != checked['candidate_input_sha256']):
        raise ValueError('SHA source review changed bound source/main/index')
    evidence = dict(candidate=str(work), candidate_input_sha256=checked['candidate_input_sha256'],
        compile_receipt_sha256=s.sha((folder / 'RUN.json').read_bytes()),
        checked_receipt_sha256=s.sha((folder / 'CHECKED.json').read_bytes()),
        kernel_launch_sha256=s.sha((folder / 'KERNEL-RUN.json').read_bytes()), staged_patch_sha256=index,
        source_review=result, commands=commands,
        tools_sha256={n: s.sha((HERE / n).read_bytes()) for n in
            ['check-source.py', 'test-source.py', 'source-model.py', 'create-model.py', 'finish-source.py']},
        canonical_source_review_complete=True, prior_recursive_kernel_evidence_validated=True,
        independent_evidence_review_complete=False, formal_host_library_equivalence=False,
        normal_registration=False, coverage_added=0, full_acceptance=False)
    s.changed({HERE / 'SOURCE-REVIEW.json': json.dumps(evidence, indent=2) + '\n',
        **{HERE / (n + '.log'): (work / (n + '.log')).read_text() for n in commands}})
    print('SHA source/negative review recorded; independent evidence review and normal admission remain', flush=True)


if __name__ == '__main__':
    if len(sys.argv) != 2:
        raise ValueError('usage: finish-source.py COMPLETED_SHA_TREE')
    main(Path(sys.argv[1]).resolve())
