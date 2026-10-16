"""Fresh complete tapEnvHash reports and recursive kernel/AST phases.

The compiled tapleaf source is rebuilt, not copied from its live kernel run.
No registration or main audit input is edited by either phase.
"""
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('elements_tapenv_compiled_dependency', HERE.parent / 'elements-tapleaf/check.py')
leaf = importlib.util.module_from_spec(sp)
sp.loader.exec_module(leaf)
shared, s = leaf.shared, leaf.s
BASE = leaf.BASE
MODULE = 'C.jet_elements_tap_env_hash_program'
NAME = MODULE.replace('.', '/') + '.v'
NEW = [leaf.NAME, NAME]
FRESH = [leaf.MODULE, MODULE]
ENDPOINT = MODULE + '.elements_tap_env_hash_program_local_spec'
KERNEL = ['bash', '-c', 'ulimit -s 65520; exec bash build-jets.sh --coqchk -silent -o ' + MODULE]


def tree(work):
    if (work == s.REPO or s.REPO in work.parents or work == BASE or
        (work / 'Coq').is_symlink() or
        s.inputs.fingerprint(BASE / 'Coq', BASE) != leaf.BASE_RECORD['candidate_input_sha256']):
        raise ValueError('distinct private tapenv tree and completed Elements source base required')
    leaf.base.tree(BASE)
    old = shared.inventory(BASE / 'Coq')
    if shared.inventory(work / 'Coq') != old | set(NEW):
        raise ValueError('unexpected tapenv source/metadata inventory')
    for name in old:
        if (work / 'Coq' / name).read_bytes() != (BASE / 'Coq' / name).read_bytes():
            raise ValueError('tapenv changes inherited source: ' + name)
    dep = json.loads((leaf.HERE / 'RUN.json').read_text())
    for name, archive in [(leaf.NAME, leaf.HERE / 'source/jet_elements_tapleaf_hash_program.v.source'),
                          (NAME, HERE / 'source/jet_elements_tap_env_hash_program.v.source')]:
        p = work / 'Coq' / name
        if p.is_symlink() or p.read_bytes() != archive.read_bytes():
            raise ValueError('tapenv private/archive source differs')
        s.safe_source(p.read_text(), name)
    if s.sha((work / 'Coq' / leaf.NAME).read_bytes()) != dep['source_sha256'][leaf.MODULE]:
        raise ValueError('tapenv compiled tapleaf dependency source differs')


def compile(work):
    if (HERE / 'RUN.json').exists():
        raise ValueError('tapenv compilation already recorded; inspect existing evidence')
    tree(work)
    before, index = s.input_map(), s.index_hash()
    fingerprint = s.inputs.fingerprint(work / 'Coq', work)
    commands = {}
    for module in FRESH:
        commands[module] = s.run(work, ['bash', 'build-jets.sh', '--coqc', '-q', module.replace('.', '/') + '.v'], module, 60)
    results, definitions, deps = shared.reports(work, [(MODULE, work / 'Coq' / NAME)], 'elements-tapenv', commands)
    if ((len(results), len(definitions)) != (3, 2) or ENDPOINT not in results or
        deps[ENDPOINT] != s.SIX or any(not ds <= s.SIX for ds in deps.values())):
        raise ValueError('wrong complete tapenv declaration/assumption inventory')
    tree(work)
    if (s.input_map() != before or s.index_hash() != index or
        s.inputs.fingerprint(work / 'Coq', work) != fingerprint):
        raise ValueError('tapenv compile/report changed main/index/private sources')
    record = dict(candidate=str(work), base_candidate=str(BASE),
        base_checked_sha256=s.sha(leaf.RECEIPT.read_bytes()),
        tapleaf_compile_sha256=s.sha((leaf.HERE / 'RUN.json').read_bytes()),
        candidate_input_sha256=fingerprint, main_inputs=before, staged_patch_sha256=index,
        modules=[MODULE], fresh_modules=FRESH, new_sources=NEW, results=results, definitions=definitions,
        endpoints=[ENDPOINT], closed_results=[n for n in results if not deps[n]],
        dependencies={n: sorted(ds) for n, ds in deps.items()}, commands=commands,
        source_sha256={m: s.sha((work / 'Coq' / (m.replace('.', '/') + '.v')).read_bytes()) for m in FRESH},
        object_sha256={m: s.sha((work / 'Coq' / (m.replace('.', '/') + '.vo')).read_bytes()) for m in FRESH},
        tools_sha256={'check.py': s.sha(Path(__file__).read_bytes())},
        tapleaf_and_tappath_program_semantics_reused=True, native_word_internal_key=True,
        whole_c_endpoints=1, caller_cached_hashes_established=False, canonical_source_review_complete=False,
        recursive_kernel_check=False, normal_registration=False, coverage_added=0, full_acceptance=False)
    s.changed({HERE / 'RUN.json': json.dumps(record, indent=2) + '\n',
        **{HERE / (n + '.log'): (work / (n + '.log')).read_text() for n in commands}})
    print('Original Elements tapEnvHash C-to-program endpoint freshly compiled/reported; kernel/source/admission remain', flush=True)


def kernel(work):
    if (HERE / 'KERNEL-RUN.json').exists():
        raise ValueError('tapenv kernel phase already launched; poll the existing handle')
    record = json.loads((HERE / 'RUN.json').read_text())
    if record['candidate'] != str(work) or record['tools_sha256'] != {'check.py': s.sha(Path(__file__).read_bytes())}:
        raise ValueError('tapenv fresh compilation identity differs')
    tree(work)
    for field, suffix in [('source_sha256', '.v'), ('object_sha256', '.vo')]:
        for module, digest in record[field].items():
            if s.sha((work / 'Coq' / (module.replace('.', '/') + suffix)).read_bytes()) != digest:
                raise ValueError('tapenv source/object changed between phases')
    before, index = s.input_map(), s.index_hash()
    if before != record['main_inputs'] or index != record['staged_patch_sha256']:
        raise ValueError('tapenv main/index changed between phases')
    launch = dict(candidate=str(work), command=KERNEL,
        compiled_receipt_sha256=s.sha((HERE / 'RUN.json').read_bytes()),
        candidate_input_sha256=record['candidate_input_sha256'], staged_patch_sha256=index,
        recursive_kernel_check=False)
    s.changed({HERE / 'KERNEL-RUN.json': json.dumps(launch, indent=2) + '\n'})
    commands = dict(record['commands'])
    commands['ast'] = s.run(work, ['bash', 'C/check-elements-jets-generation.sh'], 'ast', 300)
    commands['kernel'] = s.run(work, KERNEL, 'kernel', 3600)
    s.kernel.kernel((work / 'kernel.log').read_text(), sorted((work / 'Coq/C/jet_coqchk_axioms.expected').read_text().split()))
    tree(work)
    if (s.input_map() != before or s.index_hash() != index or
        s.inputs.fingerprint(work / 'Coq', work) != record['candidate_input_sha256']):
        raise ValueError('tapenv kernel changed main/index/private sources')
    record.update(commands=commands, recursive_kernel_check=True,
        kernel_launch_sha256=s.sha((HERE / 'KERNEL-RUN.json').read_bytes()))
    s.changed({HERE / 'CHECKED.json': json.dumps(record, indent=2) + '\n',
        **{HERE / (n + '.log'): (work / (n + '.log')).read_text() for n in ['ast', 'kernel']}})
    print('Original Elements tapEnvHash C endpoint recursively kernel-checked; source/admission remain', flush=True)


if __name__ == '__main__':
    if len(sys.argv) != 3 or sys.argv[1] not in ['compile', 'kernel']:
        raise ValueError('usage: check.py compile|kernel PRIVATE_TREE')
    (compile if sys.argv[1] == 'compile' else kernel)(Path(sys.argv[2]).resolve())
