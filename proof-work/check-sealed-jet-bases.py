"""Read-only source/object/kernel reuse checks, not current-tree acceptance.

Old whole-checkout preservation sentinels are historical observations. They
must not be rewritten after an unrelated proof repair. Instead validate the
exact sealed proof/dependency inputs and their current mirrors explicitly.
No old receipt is modified and no kernel check is claimed to have run anew.
"""
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
REPO = HERE.parent
sp = importlib.util.spec_from_file_location('sealed_reuse_support', HERE / 'elements-count/support.py')
s = importlib.util.module_from_spec(sp)
sp.loader.exec_module(s)


def read(path):
    return json.loads(path.read_text())


def same(path, digest):
    if path.is_symlink() or s.sha(path.read_bytes()) != digest:
        raise ValueError('sealed input/object/log differs: ' + str(path))


def local_objects(work, rows):
    for name, row in rows.items():
        p = work / 'Coq' / name
        same(p, row['source_sha256'])
        same(p.with_suffix('.vo'), row['object_sha256'])
        mirror = REPO / 'Coq' / name
        if mirror.exists():
            same(mirror, row['source_sha256'])


def command_logs(work, rows, aliases=None):
    for name, row in rows.items():
        if row['exit_code']:
            raise ValueError('sealed command was unsuccessful: ' + name)
        stem = (aliases or {}).get(name, name)
        same(work / (stem + '.log'), row['log_sha256'])


def kernel(work, folder, receipt, command, log):
    row = receipt['kernel']
    if not receipt['recursive_kernel_check'] or row['exit_code'] or row['command'] != command:
        raise ValueError('sealed kernel command/result differs')
    same(work / log, row['log_sha256'])
    same(folder / log, row['log_sha256'])
    text = (folder / log).read_text()
    context = sorted(text.split('* Axioms:\n', 1)[1].split('* Constants/Inductives', 1)[0].split())
    if not set(context) <= set((REPO / 'Coq/C/jet_coqchk_axioms.expected').read_text().split()):
        raise ValueError('sealed kernel contains a non-inherited library axiom')
    s.kernel.kernel(text, context)


def field():
    folder = HERE / 'secp-field-integration'
    prep, built, report, checked = [read(folder / n) for n in
        ['PREPARATION.json', 'BUILT.json', 'REPORTED.json', 'CHECKED.json']]
    work = Path(prep['candidate'])
    same(folder / 'REPORTED.json', checked['reported_sha256'])
    same(folder / 'BUILT.json', report['built_sha256'])
    same(folder / 'PREPARATION.json', built['preparation_sha256'])
    same(folder / 'assemble.py', prep['assembler_sha256'])
    same(folder / 'verify.py', report['verifier_sha256'])
    rows = {n.removeprefix('Coq/'): dict(source_sha256=r['sha256'],
        object_sha256=built['source_objects'][n]) for n, r in prep['sources'].items()}
    if len(rows) != 235 or len(report['dependencies']) != 413:
        raise ValueError('sealed field dependency/result inventory differs')
    local_objects(work, rows)
    for name, row in prep['projects'].items():
        same(work / 'Coq' / name, row['sha256'])
    command_logs(work, built['commands'])
    command_logs(work, report['commands'], {'original-targets': 'integration-original-targets'})
    command_logs(work, report['source_review_commands'],
        {n: 'integration-review-' + n for n in report['source_review_commands']})
    expected = ['bash', '-c', 'ulimit -s 65520; exec bash build-jets.sh --coqchk -silent -o ' + prep['root']]
    kernel(work, folder, checked, expected, 'integration-kernel.log')
    print('Sealed field proof reused: exact 235 source/object inputs and original successful kernel evidence')


def extension(name, root, subdir, source_name, prefix, kind):
    folder = HERE / name
    checked = read(folder / 'CHECKED.json')
    report = read(folder / 'RUN.json') if kind == 'identity' else checked
    work = Path(report['candidate'])
    source = work / subdir / (source_name + '.v')
    same(source, report['source_sha256'])
    same(folder / (source_name + '.v.source'), report['source_sha256'])
    same(source.with_suffix('.vo'), report['object_sha256'])
    local_objects(work, report['loaded_local_source_objects'])
    if kind == 'identity':
        same(folder / 'RUN.json', checked['run_sha256'])
        same(folder / 'verify.py', report['driver_sha256'])
        if len(report['dependencies']) != 3 or any(report['dependencies'].values()):
            raise ValueError('identity diagnostic is not the three closed results')
        aliases = {'compile': 'identity-compile'}
    else:
        same(folder / 'check.py', report['checker_sha256'])
        four = s.SIX - {'Events.external_functions_sem', 'Events.inline_assembly_sem'}
        expected = {n: four if n.endswith(('.cell_ok_borrow', '.region_ok_borrow')) else set()
                    for n in report['dependencies']}
        if len(expected) != 7 or {n: set(ds) for n, ds in report['dependencies'].items()} != expected:
            raise ValueError('borrowed helper exact profiles differ')
        aliases = {'compile': 'borrowed-compile'}
    command_logs(work, report['commands'], aliases)
    extra = ['-Q', str(source.parent), root.split('.')[0]]
    expected = ['bash', '-c', 'ulimit -s 65520; exec bash build-jets.sh --coqchk -silent -o ' + ' '.join(extra + [root])]
    kernel(work, folder, checked, expected, prefix + '-kernel.log')
    print('Sealed ' + kind + ' proofs reused: exact source/object/dependency inputs and original kernel evidence')


def count():
    folder = HERE / 'bitcoin-count-frozen'
    checked = read(folder / 'CHECKED.json')
    work = Path(checked['candidate'])
    same(folder / 'check.py', checked['checker_sha256'])
    same(folder / 'REPAIR.json', checked['repair_sha256'])
    local_objects(work, checked['loaded_local_source_objects'])
    if len(checked['results']) != 10 or not checked['only_one_proof_line_changed']:
        raise ValueError('count repair theorem/scope inventory differs')
    repair = read(folder / 'REPAIR.json')
    same(REPO / repair['original'], repair['new_source_sha256'])
    same(folder / 'Bridge.v.source', repair['new_source_sha256'])
    aliases = {m: 'count-fresh-' + m.split('.')[-1] for m in
        ['C.jet_bitcoin_count_bridge', 'C.jet_bitcoin_count_local']}
    command_logs(work, checked['commands'], aliases)
    expected = ['bash', '-c', 'ulimit -s 65520; exec bash build-jets.sh --coqchk -silent -o C.jet_bitcoin_count_local']
    kernel(work, folder, checked, expected, 'count-kernel.log')
    print('Count repair matches promoted source; exact ten result/dependency inputs and original kernel evidence reused')


if __name__ == '__main__':
    if len(sys.argv) != 2 or sys.argv[1] not in {'field', 'identity', 'borrowed', 'count', 'all'}:
        raise SystemExit('usage: check-sealed-jet-bases.py field|identity|borrowed|count|all')
    selected = sys.argv[1]
    if selected in {'field', 'all'}:
        field()
    if selected in {'identity', 'all'}:
        extension('bitcoin-frozen-identity', 'FrozenBitcoin.Frozen', 'identity-diagnostic', 'Frozen', 'identity', 'identity')
    if selected in {'borrowed', 'all'}:
        extension('secp-borrowed-region', 'FieldBorrow.Borrow', 'borrowed-probe', 'Borrow', 'borrowed', 'borrowed')
    if selected in {'count', 'all'}:
        count()
    # This independently checks the unchanged C/canonical/generation target,
    # not the old unrelated whole-checkout preservation sentinel.
    subprocess.run([sys.executable, '-B', str(REPO / 'Coq/check-jet-source-target.py')],
        cwd=REPO, check=True)
    print('Reuse scope only; no fresh kernel run or whole-current-checkout acceptance claimed')
