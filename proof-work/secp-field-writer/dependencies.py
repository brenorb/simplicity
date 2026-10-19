"""Fresh source-built writer closure; no change to the existing proof scanner."""
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
PARENT = HERE.parent / 'secp-field-normalize'
sp = importlib.util.spec_from_file_location('writer_normalizer_parent', PARENT / 'verify.py')
v = importlib.util.module_from_spec(sp)
sp.loader.exec_module(v)
s, g = v.s, v.g
ROOT = 'C.jet_secp_write_fe_wide_exec'
ARCHIVED = {'C.jet_secp_write_fe_wide_' + n for n in ['checks', 'values', 'exec']}


def reviewed_source(path, module):
    source = path.read_text()
    if module != 'Simplicity.BitMachine':
        return s.safe_source(source, module)
    # The inherited machine-code datatype names a real constructor Abort.
    # This is not the vernacular Abort command. Do not loosen the scanner:
    # bind this one original file to its immutable starting-revision bytes.
    baseline = subprocess.check_output(['git', 'show', '91d89bac:Coq/Simplicity/BitMachine.v'], cwd=s.REPO)
    hits = s.scanner.violations(source)
    if (path.read_bytes() != baseline or len(hits) != 3 or
            any(m.group() != 'Abort' for m in hits) or
            re.search(r'(?m)^\s*Abort\s*\.', s.scanner.code_only(source))):
        raise ValueError('original BitMachine constructor source differs')
    return s.scanner.code_only(source)


def closure():
    seen, active, order = set(), set(), []
    def visit(module):
        if module in active:
            raise ValueError('cyclic local import: ' + module)
        if module in seen:
            return
        active.add(module)
        p = s.REPO / 'Coq' / (module.replace('.', '/') + '.v')
        code = reviewed_source(p, module)
        for block in re.findall(r'\bRequire(?:\s+(?:Import|Export))?\s+(.*?)\.(?=\s|$)', code, re.S):
            for d in block.split():
                if d.startswith(('C.', 'Simplicity.', 'Util.')):
                    visit(d)
        active.remove(module)
        seen.add(module)
        order.append(module)
    visit(ROOT)
    return order


def parent(work):
    r = json.loads((PARENT / 'CHECKED.json').read_text())
    extra = v.bound(work, r)
    if (not r['recursive_kernel_check'] or r['kernel']['exit_code'] != 0 or
            r['kernel']['log_sha256'] != s.sha((PARENT / 'normalize-kernel.log').read_bytes()) or
            r['kernel_launch_sha256'] != s.sha((PARENT / 'KERNEL-RUN.json').read_bytes()) or
            json.loads((PARENT / 'KERNEL-RUN.json').read_text())['compile_sha256'] != s.sha((PARENT / 'RUN.json').read_bytes())):
        raise ValueError('checked normalization evidence differs')
    return r, extra


def sources(work, r):
    inherited = r['loaded_local_source_objects']
    order = [m for m in closure() if m.replace('.', '/') + '.v' not in inherited]
    if len(order) != 49 or not ARCHIVED <= set(order):
        raise ValueError('unexpected additional writer dependency closure')
    for m in order:
        name = m.replace('.', '/') + '.v'
        p, q = work / 'Coq' / name, s.REPO / 'Coq' / name
        if p.is_symlink() or p.read_bytes() != q.read_bytes():
            raise ValueError('private/source mismatch: ' + m)
        reviewed_source(p, m)
        if m in ARCHIVED and p.read_bytes() != (HERE / 'inherited' / (p.name + '.source')).read_bytes():
            raise ValueError('reviewed wide-writer archive differs: ' + m)
    return order


def bound(work, r):
    prior, extra = parent(work)
    order = sources(work, prior)
    if (r['candidate'] != str(work) or r['parent_checked_sha256'] != s.sha((PARENT / 'CHECKED.json').read_bytes()) or
            r['tools_sha256'] != {'dependencies.py': s.sha(Path(__file__).read_bytes())} or
            r['main_inputs'] != s.input_map() or r['staged_patch_sha256'] != s.index_hash() or
            list(r['modules']) != order):
        raise ValueError('writer dependency receipt differs')
    local = dict(prior['loaded_local_source_objects'])
    for m, row in r['modules'].items():
        p = work / 'Coq' / (m.replace('.', '/') + '.v')
        if (row['command'] != ['bash', 'build-jets.sh', '--coqc', '-q', str(p)] or row['exit_code'] != 0 or
                row['log_sha256'] != s.sha((work / ('writer-dependency-' + m + '.log')).read_bytes()) or
                {k: row[k] for k in ['source_sha256', 'object_sha256']} != v.source_object(p)):
            raise ValueError('writer dependency source/object/compile differs: ' + m)
        local[m.replace('.', '/') + '.v'] = v.source_object(p)
    return prior, extra, local


def compile(work):
    if (HERE / 'DEPENDENCY-LAUNCH.json').exists():
        raise ValueError('writer dependency build already launched; poll its original handle')
    prior, extra = parent(work)
    order = sources(work, prior)
    before, index = s.input_map(), s.index_hash()
    parent_hash = s.sha((PARENT / 'CHECKED.json').read_bytes())
    s.changed({HERE / 'DEPENDENCY-LAUNCH.json': json.dumps(dict(candidate=str(work),
        modules=order, parent_checked_sha256=parent_hash, compile_complete=False), indent=2) + '\n'})
    rows = {}
    for m in order:
        p = work / 'Coq' / (m.replace('.', '/') + '.v')
        rows[m] = s.run(work, ['bash', 'build-jets.sh', '--coqc', '-q', str(p)], 'writer-dependency-' + m, 600)
        rows[m].update(v.source_object(p))
        print('freshly compiled ' + m, flush=True)
    r = dict(candidate=str(work), parent_checked_sha256=parent_hash, modules=rows,
        main_inputs=before, staged_patch_sha256=index,
        tools_sha256={'dependencies.py': s.sha(Path(__file__).read_bytes())},
        recursive_kernel_check=False, normal_registration=False, coverage_added=0)
    bound(work, r)
    s.changed({HERE / 'DEPENDENCIES.json': json.dumps(r, indent=2) + '\n'})
    print('49 additional writer dependencies freshly compiled and source/object-bound', flush=True)


if __name__ == '__main__':
    if len(sys.argv) != 3 or sys.argv[1] not in {'compile'}:
        raise ValueError('usage: dependencies.py compile PRIVATE_AUDIT_TREE')
    compile(Path(sys.argv[2]).resolve())
