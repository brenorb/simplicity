"""Exact per-result profile review and source-bound entropy helper kernel audit."""
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('entropy_compile', HERE / 'verify.py')
v = importlib.util.module_from_spec(sp)
sp.loader.exec_module(v)
s, p = v.s, v.p
FOUR = s.SIX - {'Events.external_functions_sem', 'Events.inline_assembly_sem'}


def profile(r):
    expected = {n: set() for n in r['results']}
    four = ['C.jet_elements_env_ctxo.' + n for n in ['ctxo_valid', 'ctxo_block_perm', 'ctxo_other', 'ctxo_step']]
    four += ['C.jet_elements_env_entropy.' + n for n in ['ent_ev_buf', 'ent_optx_value']]
    six = {
        'jet_elements_env_ctxo': ['ctxo_hash', 'ctxo_finalize', 'ctxo_init'],
        'jet_elements_env_ctxo_more': ['ctxo_uchar', 'ctxo_u32be', 'ctxo_u64be'],
        'jet_elements_env_ctxo_uchars': ['ctxo_uchars'],
        'jet_elements_env_le32_write': ['wle32_assign', 'eval_WriteLE32'],
        'jet_elements_env_u32le_exec': ['eval_sha256_u32le'],
        'jet_elements_env_ctxo_le': ['ctxo_u32le'],
        'jet_elements_env_tx_calls': ['mt_call_hash', 'mt_call_u32be', 'mt_call_u64be', 'mt_call_finalize'],
        'jet_elements_env_entropy': ['ent_init_exec', 'ent_from_uchars_exec', 'ent_u32le_exec',
                                    'ent_final_exec', 'eval_generateIssuanceEntropy'],
    }
    expected.update({n: FOUR for n in four})
    expected.update({'C.' + m + '.' + n: s.SIX for m, ns in six.items() for n in ns})
    if (len(r['results']), len(r['definitions'])) != (51, 21) or {
        n: set(d) for n, d in r['dependencies'].items()} != expected:
        raise ValueError('entropy complete 51-result/21-definition profile differs')
    return {n: sorted(d) for n, d in expected.items()}


def identity(work):
    r = json.loads((HERE / 'RUN.json').read_text())
    bound = json.loads((HERE / 'SOURCE-CLOSURE.json').read_text())
    v.tree(work)
    force = s.load('entropy_kernel_objects', HERE.parent / 'verify-forced-closure.py')
    force.objects(work, bound['compiled_and_loaded_local_modules'])
    if (Path(r['candidate']) != work or Path(bound['candidate']) != work or
        s.sha((HERE / 'RUN.json').read_bytes()) != bound['compile_sha256'] or
        r['tools_sha256'] != {n: s.sha((HERE / n).read_bytes()) for n in ['verify.py', 'port.py']} or
        r['main_inputs'] != s.input_map() or r['staged_patch_sha256'] != s.index_hash()):
        raise ValueError('entropy source-bound compile identity changed')
    profile(r)
    return r, bound


def review(work):
    r, bound = identity(work)
    record = dict(candidate=str(work), compile_sha256=s.sha((HERE / 'RUN.json').read_bytes()),
        source_closure_sha256=s.sha((HERE / 'SOURCE-CLOSURE.json').read_bytes()),
        dependencies=profile(r), closed_results=25, four_dependency_results=6,
        six_dependency_results=20, local_source_module_count=len(bound['compiled_and_loaded_local_modules']),
        exact_per_result_profile_review=True, recursive_kernel_check=False,
        tool_sha256=s.sha(Path(__file__).read_bytes()), normal_registration=False, coverage_added=0)
    if (HERE / 'PROFILE.json').exists():
        if json.loads((HERE / 'PROFILE.json').read_text()) != record:
            raise ValueError('review receipt differs; preserve its original inputs')
    else:
        s.changed({HERE / 'PROFILE.json': json.dumps(record, indent=2) + '\n'})
    print('Entropy helper exact profile reviewed: 25 closed, 6 four-dependency, 20 six-dependency results', flush=True)


def kernel(work):
    if (HERE / 'KERNEL-RUN.json').exists():
        raise ValueError('entropy kernel already launched; inspect the original process')
    review(work)
    r, bound = identity(work)
    command = ['bash', '-c', 'ulimit -s 65520; exec bash build-jets.sh --coqchk -silent -o ' + ' '.join(v.ROOTS)]
    s.changed({HERE / 'KERNEL-RUN.json': json.dumps(dict(command=command,
        compile_sha256=s.sha((HERE / 'RUN.json').read_bytes()),
        source_closure_sha256=s.sha((HERE / 'SOURCE-CLOSURE.json').read_bytes()),
        profile_sha256=s.sha((HERE / 'PROFILE.json').read_bytes()),
        driver_sha256=s.sha(Path(__file__).read_bytes()), recursive_kernel_check=False), indent=2) + '\n'})
    driver_hash = s.sha(Path(__file__).read_bytes())
    row = s.run(work, command, 'entropy-kernel', 3600)
    log = (work / 'entropy-kernel.log').read_text()
    s.kernel.kernel(log, sorted((work / 'Coq/C/jet_coqchk_axioms.expected').read_text().split()))
    identity(work)
    if driver_hash != s.sha(Path(__file__).read_bytes()):
        raise ValueError('entropy kernel driver changed during check')
    r.update(recursive_kernel_check=True, kernel=row, exact_per_result_profile_review=True,
             kernel_launch_sha256=s.sha((HERE / 'KERNEL-RUN.json').read_bytes()))
    s.changed({HERE / 'CHECKED.json': json.dumps(r, indent=2) + '\n', HERE / 'entropy-kernel.log': log})
    print('Original-program entropy helper and all 276 local source-built dependencies recursively kernel-checked', flush=True)


if __name__ == '__main__':
    if len(sys.argv) != 3 or sys.argv[1] not in ['review', 'kernel']:
        raise ValueError('usage: kernel.py review|kernel PRIVATE_TREE')
    globals()[sys.argv[1]](Path(sys.argv[2]).resolve())
