"""Fresh proof/report and recursive-kernel phases for the annexes getter.

No metadata/registration changes; use a completed Elements proof cache, not a
live audit. Each phase checks exact source inheritance and main/index stability.
"""
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('elements_annexes_completed_stream', HERE.parent / 'elements-stream/check.py')
upstream = importlib.util.module_from_spec(sp)
sp.loader.exec_module(upstream)
shared, s = upstream.shared, upstream.s
BASE_RECEIPT = HERE.parent / 'elements-stream/CHECKED.json'
BASE_RECORD = json.loads(BASE_RECEIPT.read_text())
BASE = Path(BASE_RECORD['candidate'])
MODULES = ['C.jet_sha_hash_elems_reader', 'C.jet_elements_annexes_hash_program']
NEW = [m.replace('.', '/') + '.v' for m in MODULES]
ENDPOINT = MODULES[1] + '.elements_input_annexes_hash_program_local_spec'
KERNEL = ['bash', '-c', 'ulimit -s 65520; exec bash build-jets.sh --coqchk -silent -o ' + ' '.join(MODULES)]


def tree(work):
    if (work == s.REPO or s.REPO in work.parents or work == BASE or
        (work / 'Coq').is_symlink() or BASE_RECORD['recursive_kernel_check'] is not True or
        s.inputs.fingerprint(BASE / 'Coq', BASE) != BASE_RECORD['candidate_input_sha256']):
        raise ValueError('distinct private tree and completed Elements source base required')
    upstream.tree(BASE)
    old = shared.inventory(BASE / 'Coq')
    if shared.inventory(work / 'Coq') != old | set(NEW):
        raise ValueError('unexpected annexes source or metadata inventory')
    for name in old:
        if (work / 'Coq' / name).read_bytes() != (BASE / 'Coq' / name).read_bytes():
            raise ValueError('annexes proof changes inherited source: ' + name)
    for name in NEW:
        p = work / 'Coq' / name
        if p.is_symlink() or p.read_bytes() != (HERE / 'source' / (p.name + '.source')).read_bytes():
            raise ValueError('private and archived annexes proof differ')
        s.safe_source(p.read_text(), name)


def compile(work):
    if (HERE / 'RUN.json').exists():
        raise ValueError('annexes compilation already recorded; inspect existing evidence')
    tree(work)
    before, index = s.input_map(), s.index_hash()
    fingerprint = s.inputs.fingerprint(work / 'Coq', work)
    commands = {}
    for module, name in zip(MODULES, NEW):
        commands[module] = s.run(work, ['bash', 'build-jets.sh', '--coqc', '-q', name], module, 60)
        print('Freshly compiled ' + module, flush=True)
    results, definitions, deps = shared.reports(work,
        [(m, work / 'Coq' / n) for m, n in zip(MODULES, NEW)], 'elements-annexes', commands)
    if ((len(results), len(definitions)) != (9, 4) or ENDPOINT not in results or
        deps[ENDPOINT] != s.SIX or any(not ds <= s.SIX for ds in deps.values())):
        raise ValueError('wrong complete annexes declaration/assumption inventory')
    tree(work)
    if (s.input_map() != before or s.index_hash() != index or
        s.inputs.fingerprint(work / 'Coq', work) != fingerprint):
        raise ValueError('annexes compile/report changed main/index/private sources')
    record = dict(candidate=str(work), base_candidate=str(BASE),
        base_checked_sha256=s.sha(BASE_RECEIPT.read_bytes()),
        base_review_sha256=s.sha((HERE.parent / 'elements-stream/EVIDENCE-REVIEW.json').read_bytes()),
        candidate_input_sha256=fingerprint, main_inputs=before, staged_patch_sha256=index,
        modules=MODULES, new_sources=NEW, results=results, definitions=definitions,
        endpoints=[ENDPOINT], closed_results=[n for n in results if not deps[n]],
        dependencies={n: sorted(ds) for n, ds in deps.items()}, commands=commands,
        source_sha256={m: s.sha((work / 'Coq' / n).read_bytes()) for m, n in zip(MODULES, NEW)},
        object_sha256={m: s.sha((work / 'Coq' / n).with_suffix('.vo').read_bytes()) for m, n in zip(MODULES, NEW)},
        tools_sha256={'check.py': s.sha(Path(__file__).read_bytes())},
        environment_generic_loop=True, existing_pure_prefix_and_counter_proofs_reused=True,
        whole_c_endpoints=1, caller_cached_hashes_established=False,
        canonical_source_review_complete=False, recursive_kernel_check=False,
        normal_registration=False, coverage_added=0, full_acceptance=False)
    s.changed({HERE / 'RUN.json': json.dumps(record, indent=2) + '\n',
        **{HERE / (n + '.log'): (work / (n + '.log')).read_text() for n in commands}})
    print('Whole-C Elements annexes endpoint freshly compiled/reported; kernel/source/admission remain', flush=True)


def kernel(work):
    if (HERE / 'KERNEL-RUN.json').exists():
        raise ValueError('annexes kernel phase already launched; poll its existing process')
    record = json.loads((HERE / 'RUN.json').read_text())
    if record['candidate'] != str(work) or record['tools_sha256'] != {'check.py': s.sha(Path(__file__).read_bytes())}:
        raise ValueError('annexes compilation identity differs')
    tree(work)
    for field, suffix in [('source_sha256', '.v'), ('object_sha256', '.vo')]:
        for module, digest in record[field].items():
            if s.sha((work / 'Coq' / (module.replace('.', '/') + suffix)).read_bytes()) != digest:
                raise ValueError('annexes source/object changed between phases')
    before, index = s.input_map(), s.index_hash()
    if before != record['main_inputs'] or index != record['staged_patch_sha256']:
        raise ValueError('main/index changed between annexes phases')
    launch = dict(candidate=str(work), command=KERNEL,
        compiled_receipt_sha256=s.sha((HERE / 'RUN.json').read_bytes()),
        candidate_input_sha256=record['candidate_input_sha256'],
        staged_patch_sha256=index, recursive_kernel_check=False)
    s.changed({HERE / 'KERNEL-RUN.json': json.dumps(launch, indent=2) + '\n'})
    commands = dict(record['commands'])
    commands['ast'] = s.run(work, ['bash', 'C/check-elements-jets-generation.sh'], 'ast', 300)
    commands['kernel'] = s.run(work, KERNEL, 'kernel', 3600)
    s.kernel.kernel((work / 'kernel.log').read_text(), sorted((work / 'Coq/C/jet_coqchk_axioms.expected').read_text().split()))
    tree(work)
    if (s.input_map() != before or s.index_hash() != index or
        s.inputs.fingerprint(work / 'Coq', work) != record['candidate_input_sha256']):
        raise ValueError('annexes kernel changed main/index/private sources')
    record.update(commands=commands, recursive_kernel_check=True,
        kernel_launch_sha256=s.sha((HERE / 'KERNEL-RUN.json').read_bytes()))
    s.changed({HERE / 'CHECKED.json': json.dumps(record, indent=2) + '\n',
        **{HERE / (n + '.log'): (work / (n + '.log')).read_text() for n in ['ast', 'kernel']}})
    print('Original-C annexes hash endpoint recursively kernel-checked; canonical source/admission remain', flush=True)


if __name__ == '__main__':
    if len(sys.argv) != 3 or sys.argv[1] not in ['compile', 'kernel']:
        raise ValueError('usage: check.py compile|kernel PRIVATE_TREE')
    (compile if sys.argv[1] == 'compile' else kernel)(Path(sys.argv[2]).resolve())
