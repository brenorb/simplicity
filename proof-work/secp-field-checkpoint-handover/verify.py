"""Check a reusable post-store checkpoint without inventing fresh input memory."""
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
PARENT = HERE.parent / 'secp-field-third'
sp = importlib.util.spec_from_file_location('handover_parent', PARENT / 'verify.py')
v = importlib.util.module_from_spec(sp)
sp.loader.exec_module(v)
s, g = v.s, v.g
ROOT = 'FieldNext.Checkpoint'


def identity(work):
    previous, base, inherited, extra = v.identity(work)
    r = json.loads((PARENT / 'CHECKED.json').read_text())
    if (r['candidate'] != str(work) or not r['recursive_kernel_check'] or r['kernel']['exit_code'] != 0 or
            r['kernel']['log_sha256'] != s.sha((PARENT / 'third-kernel.log').read_bytes()) or
            r['main_inputs'] != s.input_map() or r['staged_patch_sha256'] != s.index_hash() or
            r['parent_checked_sha256'] != s.sha((v.PARENT / 'CHECKED.json').read_bytes()) or
            r['tools_sha256'] != {'verify.py': s.sha((PARENT / 'verify.py').read_bytes())} or
            r['loaded_local_source_objects'] != base['loaded_local_source_objects'] or
            r['inherited_extension_sources_objects'] != inherited):
        raise ValueError('checked third-checkpoint parent identity differs')
    v.profile(r['results'], r['definitions'], {n: set(a) for n, a in r['dependencies'].items()})
    for m, p in previous:
        if r['extension_sources_objects'][m] != v.v.source_object(p):
            raise ValueError('checked third-checkpoint source/object changed: ' + m)
        inherited[m] = v.v.source_object(p)
    p = work / 'next/Checkpoint.v'
    if p.is_symlink() or p.read_bytes() != (HERE / 'Checkpoint.v.source').read_bytes():
        raise ValueError('handover archive/source differs')
    if {q.name for q in p.parent.glob('*.v')} != {'Checkpoint.v'}:
        raise ValueError('unexpected handover source inventory')
    s.safe_source(p.read_text(), ROOT)
    return p, base, inherited, extra + ['-Q', str(p.parent), 'FieldNext']


def profile(rs, ds, deps):
    endpoint = ROOT + '.exec_original_third_checkpoint'
    if (len(rs) != 7 or len(set(rs)) != 7 or len(ds) != 6 or endpoint not in rs or
            deps != {n: (s.SIX if n == endpoint else set()) for n in rs}):
        raise ValueError('exact checkpoint-handover profile differs: six closed, one SIX')


def bound(work, r):
    p, base, inherited, extra = identity(work)
    if (r['parent_checked_sha256'] != s.sha((PARENT / 'CHECKED.json').read_bytes()) or
            r['tools_sha256'] != {'verify.py': s.sha(Path(__file__).read_bytes())} or
            r['main_inputs'] != s.input_map() or r['staged_patch_sha256'] != s.index_hash() or
            r['loaded_local_source_objects'] != base['loaded_local_source_objects'] or
            r['inherited_extension_sources_objects'] != inherited or
            r['extension_source_object'] != v.v.source_object(p)):
        raise ValueError('handover checked-input identity differs')
    profile(r['results'], r['definitions'], {n: set(a) for n, a in r['dependencies'].items()})
    return extra


def compile(work):
    if (HERE / 'LAUNCH.json').exists():
        raise ValueError('compilation already launched; poll original handle')
    p, base, inherited, extra = identity(work)
    before, index = s.input_map(), s.index_hash()
    parent_hash = s.sha((PARENT / 'CHECKED.json').read_bytes())
    s.changed({HERE / 'LAUNCH.json': json.dumps(dict(candidate=str(work), root=ROOT,
        parent_checked_sha256=parent_hash, compile_complete=False), indent=2) + '\n'})
    commands = {'compile': s.run(work, ['bash', 'build-jets.sh', '--coqc', '-q', *extra, str(p)], 'handover-fresh', 60)}
    rs, ds, deps = g.reports(work, [(ROOT, p)], 'handover', commands, extra)
    profile(rs, ds, deps)
    query = subprocess.run(['bash', 'build-jets.sh', '--coqtop', '-quiet', *extra],
        input='Require ' + ROOT + '.\nPrint Libraries.\n', cwd=work / 'Coq', env=s.ENV,
        text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=60)
    local = {m.replace('.', '/') + '.v' for m in re.findall(r'^  ((?:C|Simplicity|Util)\.[A-Za-z0-9_.]+)$', query.stdout, re.M)}
    ext = set(re.findall(r'^  ((?:SecpShift|FieldRun|FieldCheckpoint|FieldFirst|FieldSecond|FieldSecondValues|FieldThird|FieldNext)\.[A-Za-z0-9_.]+)$', query.stdout, re.M))
    if (query.returncode or re.search(r'(?m)^(?:Error|Anomaly):', query.stdout) or
            local != set(base['loaded_local_source_objects']) or ext != set(inherited) | {ROOT}):
        raise ValueError('handover loaded closure lacks exact source-built provenance')
    r = dict(candidate=str(work), main_inputs=before, staged_patch_sha256=index, commands=commands,
        results=rs, definitions=ds, dependencies={n: sorted(a) for n, a in deps.items()},
        parent_checked_sha256=parent_hash, loaded_local_source_objects=base['loaded_local_source_objects'],
        inherited_extension_sources_objects=inherited, extension_source_object=v.v.source_object(p),
        tools_sha256={'verify.py': s.sha(Path(__file__).read_bytes())}, original_statement_heads_executed=68,
        stored_outputs_separate_from_cached_inputs=True, checkpoint_entry_derived_from_real_execution=True,
        fresh_physical_memory_assumed=False, full_field_product_proved=False, public_jet_equivalence=False,
        normal_registration=False, coverage_added=0, recursive_kernel_check=False)
    bound(work, r)
    s.changed({HERE / 'RUN.json': json.dumps(r, indent=2) + '\n', HERE / 'loaded-libraries.log': query.stdout,
        **{HERE / (n + '.log'): (work / (n + '.log')).read_text() for n in ['handover-assumptions', 'handover-contracts']}})
    print('Seven handover results freshly compiled: stored outputs and cached inputs separated, real entry derived', flush=True)


def kernel(work):
    if (HERE / 'KERNEL-RUN.json').exists():
        raise ValueError('kernel already launched; poll original handle')
    r = json.loads((HERE / 'RUN.json').read_text())
    extra = bound(work, r)
    cmd = ['bash', '-c', 'ulimit -s 65520; exec bash build-jets.sh --coqchk -silent -o ' + ' '.join(extra + [ROOT])]
    s.changed({HERE / 'KERNEL-RUN.json': json.dumps(dict(command=cmd,
        compile_sha256=s.sha((HERE / 'RUN.json').read_bytes()), recursive_kernel_check=False), indent=2) + '\n'})
    row = s.run(work, cmd, 'handover-kernel', 3600)
    log = (work / 'handover-kernel.log').read_text()
    s.kernel.kernel(log, sorted((work / 'Coq/C/jet_coqchk_axioms.expected').read_text().split()))
    bound(work, r)
    r.update(recursive_kernel_check=True, kernel=row,
        kernel_launch_sha256=s.sha((HERE / 'KERNEL-RUN.json').read_bytes()))
    s.changed({HERE / 'CHECKED.json': json.dumps(r, indent=2) + '\n', HERE / 'handover-kernel.log': log})
    print('Reusable post-store checkpoint handover recursively kernel-checked', flush=True)


if __name__ == '__main__':
    if len(sys.argv) != 3 or sys.argv[1] not in {'compile', 'kernel'}:
        raise ValueError('usage: verify.py compile|kernel PRIVATE_AUDIT_TREE')
    globals()[sys.argv[1]](Path(sys.argv[2]).resolve())
