"""Check the square caller's concrete storage and writer adapters, not a public jet."""
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('square_caller_numeric_basis', HERE.parent / 'secp-square-values/verify.py')
p = importlib.util.module_from_spec(sp)
sp.loader.exec_module(p)
s, g = p.s, p.g
EXT = Path('/private/tmp/jet-square-caller.xnOv1u')
ROOT = 'SquareCaller.Bridge'
EXTRA = p.EXTRA + ['-Q', str(EXT), 'SquareCaller']
PREFIX = 'square-caller'


def identity():
    p.check()
    work, known = p.identity()
    source = EXT / 'Bridge.v'
    if (source.is_symlink() or {f.name for f in EXT.glob('*.v')} != {'Bridge.v'} or
            source.read_bytes() != (HERE / 'Bridge.v.source').read_bytes()):
        raise ValueError('square caller source/archive inventory differs')
    s.safe_source(source.read_text(), ROOT)
    return work, known, source


def objects(source):
    return dict(source_sha256=s.sha(source.read_bytes()), object_sha256=s.sha(source.with_suffix('.vo').read_bytes()))


def profiles(results, definitions, deps):
    if len(results) != 5 or definitions or set(results) != set(deps) or any(not set(ds) <= s.SIX for ds in deps.values()):
        raise ValueError('square caller report inventory/profile differs')
    if set(deps[ROOT + '.eval_square_for_writer']) != s.SIX or deps[ROOT + '.square_foot_owner']:
        raise ValueError('square caller execution/closed-frame profile differs')


def kernel_command():
    return ['bash', '-c', 'ulimit -s 65520; exec bash build-jets.sh --coqchk -silent -o ' + ' '.join(EXTRA + [ROOT])]


def run():
    if (HERE / 'LAUNCH.json').exists():
        raise ValueError('square caller audit already launched; poll the original process')
    work, known, source = identity()
    before, index = s.input_map(), s.index_hash()
    parent = s.sha((p.HERE / 'CHECKED.json').read_bytes())
    driver = s.sha(Path(__file__).read_bytes())
    source_hash = s.sha(source.read_bytes())
    s.changed({HERE / 'LAUNCH.json': json.dumps(dict(candidate=str(EXT), complete=False,
        source_sha256=source_hash, driver_sha256=driver, parent_checked_sha256=parent), indent=2) + '\n'})
    commands = {PREFIX + '-compile': s.run(work,
        ['bash', 'build-jets.sh', '--coqc', '-q', *EXTRA, str(source)], PREFIX + '-compile', 90)}
    results, definitions, deps = g.reports(work, [(ROOT, source)], PREFIX, commands, EXTRA)
    profiles(results, definitions, deps)
    query = subprocess.run(['bash', 'build-jets.sh', '--coqtop', '-quiet', *EXTRA],
        input='Require ' + ROOT + '.\nPrint Libraries.\n', cwd=work / 'Coq', env=s.ENV,
        text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=60)
    libraries = set(re.findall(r'^\s+([A-Z_a-z][\w]*(?:\.[\w]+)+)\s*$', query.stdout, re.M))
    local = {n.replace('.', '/') + '.v' for n in libraries if n.startswith(('C.', 'Simplicity.', 'Util.'))}
    unknown = {n for n in libraries if not n.startswith(('C.', 'Simplicity.', 'Util.', 'SquareRun.',
        'SquareValue.', 'SquareCaller.', 'Coq.', 'compcert.', 'Flocq.', 'VST.', 'sha.'))}
    private = {n for n in libraries if n.startswith(('SquareRun.', 'SquareValue.', 'SquareCaller.'))}
    expected = {ROOT, p.p.ROOT, *('SquareValue.' + n for n in p.NAMES)}
    if (query.returncode or re.search(r'(?m)^(?:Error|Anomaly):', query.stdout) or unknown or
            not local <= set(known) or private != expected):
        raise ValueError('square caller loaded an unreviewed module')
    snap = objects(source)
    print('Five square caller storage/frame results compiled and assumption-audited', flush=True)
    commands[PREFIX + '-kernel'] = s.run(work, kernel_command(), PREFIX + '-kernel', 1200)
    kernel_log = (work / (PREFIX + '-kernel.log')).read_text()
    s.kernel.kernel(kernel_log, sorted((work / 'Coq/C/jet_coqchk_axioms.expected').read_text().split()))
    _, now, _ = identity()
    if (before != s.input_map() or index != s.index_hash() or objects(source) != snap or
            snap['source_sha256'] != source_hash or driver != s.sha(Path(__file__).read_bytes()) or
            parent != s.sha((p.HERE / 'CHECKED.json').read_bytes()) or any(now[n] != known[n] for n in local)):
        raise ValueError('square caller exact inputs changed during the audit')
    r = dict(candidate=str(EXT), basis=str(work), results=results, definitions=definitions,
        dependencies={n: sorted(ds) for n, ds in deps.items()}, commands=commands, source_objects=snap,
        loaded_local_source_objects={n: known[n] for n in sorted(local)},
        main_inputs=before, staged_patch_sha256=index, driver_sha256=driver,
        parent_checked_sha256=parent, recursive_kernel_check=True,
        reader_storage_and_writer_adapter_proved=True, whole_square_jet_proved=False, coverage_added=0)
    changes = {HERE / 'CHECKED.json': json.dumps(r, indent=2) + '\n', HERE / 'loaded-libraries.log': query.stdout}
    for stem in commands:
        changes[HERE / (stem + '.log')] = (work / (stem + '.log')).read_text()
    s.changed(changes)
    print('Original square reader-storage/writer adapters recursively kernel-checked', flush=True)


def check():
    work, known, source = identity()
    r = json.loads((HERE / 'CHECKED.json').read_text())
    if (not r['recursive_kernel_check'] or r['source_objects'] != objects(source) or
            r['main_inputs'] != s.input_map() or r['staged_patch_sha256'] != s.index_hash() or
            r['driver_sha256'] != s.sha(Path(__file__).read_bytes()) or
            r['parent_checked_sha256'] != s.sha((p.HERE / 'CHECKED.json').read_bytes()) or
            any(known[n] != row for n, row in r['loaded_local_source_objects'].items())):
        raise ValueError('square caller recorded inputs differ')
    profiles(r['results'], r['definitions'], r['dependencies'])
    if r['commands'][PREFIX + '-kernel']['command'] != kernel_command():
        raise ValueError('square caller recursive kernel command differs')
    for stem, row in r['commands'].items():
        if (row['exit_code'] or row['log_sha256'] != s.sha((HERE / (stem + '.log')).read_bytes()) or
                (HERE / (stem + '.log')).read_bytes() != (work / (stem + '.log')).read_bytes()):
            raise ValueError('square caller completed log differs: ' + stem)
    s.kernel.kernel((HERE / (PREFIX + '-kernel.log')).read_text(),
        sorted((work / 'Coq/C/jet_coqchk_axioms.expected').read_text().split()))
    print('Exact square caller source/object/reports/kernel inputs verified')


if __name__ == '__main__':
    if len(sys.argv) != 2 or sys.argv[1] not in {'run', 'check'}:
        raise SystemExit('usage: verify.py run|check')
    {'run': run, 'check': check}[sys.argv[1]]()
