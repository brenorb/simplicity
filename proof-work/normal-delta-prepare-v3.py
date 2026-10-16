"""Normal preparation using the exact audited printer context (version three).

A batch supplies exact source boundaries, modules and checked dependency sets.
The inherited snapshots are preserved byte-for-byte; only freshly printed new
records are appended. Consumers must independently review all deltas and run
the real full acceptance without update/skip flags.
"""
import json
import re
import subprocess

def contract_printer_header(coq):
    """Execute only the existing audit's header-emission fragment.

    Fail closed if its expected shell boundaries or emitted grammar change.
    This runs neither compilation nor snapshot comparison and changes no file.
    The header, including Require versus Require Import, has one source of truth.
    """
    script = (coq / 'audit-jet-contracts.sh').read_text()
    start = "{\n  echo 'Set Warnings \"-notation-overridden\".'\n"
    stop = "  awk '!/^#/ && NF==2 {\n"
    if script.count(start) != 1 or script.count(stop) != 1:
        raise ValueError('missing/ambiguous audited printer header boundary')
    fragment = script.split(start, 1)[1].split(stop, 1)[0]
    # The initial warning is part of start, not the captured fragment.
    fragment = "echo 'Set Warnings \"-notation-overridden\".'\n" + fragment
    done = subprocess.run(['bash', '-e', '-u', '-o', 'pipefail', '-c', fragment],
        cwd=coq, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, timeout=30)
    if done.returncode or done.stderr:
        raise ValueError('audited printer header command failed: ' + done.stderr)
    lines = done.stdout.splitlines()
    trailer = ['Import Simplicity.BitMachine Simplicity.Translate.',
               'Set Printing All.', 'Set Printing Width 120.']
    if not lines or lines[0] != 'Set Warnings "-notation-overridden".' or lines[-3:] != trailer:
        raise ValueError('unexpected audited printer settings/order')
    modules = []
    for line in lines[1:-3]:
        match = re.fullmatch(r'Require(?: Import)? ([A-Za-z_][A-Za-z0-9_.]*)[.]', line)
        if not match:
            raise ValueError('unexpected audited printer import grammar')
        modules.append(match[1])
    expected = set()
    for name in ['jet_public_theorems.txt', 'jet_contract_definitions.txt']:
        for line in (coq / 'C' / name).read_text().splitlines():
            fields = line.split()
            if line.startswith('#') or not fields:
                continue
            if len(fields) != 2:
                raise ValueError('malformed audited printer declaration inventory')
            expected.add(fields[0])
    if modules != sorted(expected):
        raise ValueError('audited printer header does not cover the exact module inventory')
    return lines


def prepare(g, work):
    s, normal = g.s, g.normal
    if (work / 'PREPARATION.json').exists():
        raise ValueError('normal preparation already recorded; inspect it instead of overwriting')
    meta = json.loads((work / 'ASSEMBLY.json').read_text())
    g.boundaries()
    before = s.input_map()
    built = s.run(work, ['bash', 'build-jets.sh', '-j2'], 'build', 10800)
    fresh = {m: s.run(work, ['bash', 'build-jets.sh', '--coqc', '-q', m.replace('.', '/') + '.v'],
                       'fresh-' + m, 180) for m in g.MODULES}
    coq = work / 'Coq'
    results = [tuple(row.split()) for row in meta['extensions']['C/jet_public_theorems.txt']]
    definitions = [tuple(row.split()) for row in meta['extensions']['C/jet_contract_definitions.txt']]
    printer = contract_printer_header(coq)
    header = printer[:-3]
    assumptions = header[:]
    for m, n in results:
        assumptions += ['Goal True. idtac "JET_ASSUMPTIONS ' + m + '.' + n + '". exact I. Qed.', 'Print Assumptions ' + m + '.' + n + '.']
    wanted = [('TYPE', m + '.' + n) for m, n in results] + [('DEF', m + '.' + n) for m, n in definitions]
    driver = printer[:]
    for depth, marker in [(50, 'DELTA_COMPACT_'), (1000000, 'DELTA_DEEP_')]:
        driver += ['Set Printing Depth ' + str(depth) + '.']
        for kind, n in wanted:
            driver += ['Goal True. idtac "' + marker + kind + ' ' + n + '". exact I. Qed.', ('Check @' if kind == 'TYPE' else 'Print ') + n + '.']
    s.changed({work / 'new_contracts.v': '\n'.join(driver) + '\n', work / 'new_assumptions.v': '\n'.join(assumptions) + '\n'})
    contracts = s.run(work, ['bash', 'build-jets.sh', '--coqc', '-q', str(work / 'new_contracts.v')], 'new_contracts', 1800)
    audited = s.run(work, ['bash', 'build-jets.sh', '--coqc', '-q', str(work / 'new_assumptions.v')], 'new_assumptions', 1800)
    report = (work / 'new_contracts.log').read_text().split('DELTA_DEEP_', 1)[0]
    marks = list(re.finditer(r'(?m)^DELTA_COMPACT_(TYPE|DEF) (\S+)\n', report))
    if [(m[1], m[2]) for m in marks] != wanted or report[:marks[0].start()]:
        raise ValueError('incomplete compact delta report')
    bodies = {wanted[i]: ''.join(line.rstrip() + '\n' for line in report[m.end():marks[i+1].start() if i+1 < len(marks) else len(report)].splitlines()) for i, m in enumerate(marks)}
    inherited = normal.contract_records((g.BASE / 'C/jet_contracts.expected').read_text(),
        normal.rows(g.BASE / 'C/jet_public_theorems.txt'), normal.rows(g.BASE / 'C/jet_contract_definitions.txt'))
    snapshot = ''.join(t for (k, _, _, _), t in inherited if k == 'TYPE') + ''.join(bodies['TYPE', m + '.' + n] for m, n in results)
    snapshot += ''.join(t for (k, _, _, _), t in inherited if k == 'DEF') + ''.join(bodies['DEF', m + '.' + n] for m, n in definitions)
    deps = normal.assumptions((work / 'new_assumptions.log').read_text())
    if set(deps) != {m + '.' + n for m, n in results} or any(sorted(ds) != g.PR['dependencies'][n] for n, ds in deps.items()):
        raise ValueError('new assumptions differ from checked proofs')
    old_deps = g.snapshot_deps((g.BASE / 'C/jet_assumptions.expected').read_text())
    if set(old_deps) & set(deps):
        raise ValueError('overlapping old/new assumption records')
    old_deps.update({n: sorted(ds) for n, ds in deps.items()})
    text = ''.join(n + ' : ' + (', '.join(ds) or 'closed') + '\n' for n, ds in sorted(old_deps.items()))
    s.changed({coq / 'C/jet_contracts.expected': snapshot, coq / 'C/jet_assumptions.expected': text})
    g.boundaries()
    if s.input_map() != before or s.index_hash() != meta['staged_patch_sha256']:
        raise ValueError('main/index drift during normal preparation')
    r = dict(candidate=str(work), build=built, fresh_compiles=fresh, contracts=contracts, assumptions=audited,
        new_dependencies={n: sorted(ds) for n, ds in deps.items()},
        new_objects_sha256={m: s.sha((coq / (m.replace('.', '/') + '.vo')).read_bytes()) for m in g.MODULES},
        printer_header_sha256=s.sha(('\n'.join(printer) + '\n').encode()),
        printer_script_sha256=s.sha((coq / 'audit-jet-contracts.sh').read_bytes()),
        coverage_added=g.COVERAGE_ADDED, full_acceptance=False)
    g.write(work / 'PREPARATION.json', r)
    g.write(g.HERE / 'PREPARATION.json', r)
    print('Normal delta prepared; independent review and full acceptance remain required', flush=True)
