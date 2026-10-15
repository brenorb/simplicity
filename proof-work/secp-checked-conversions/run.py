"""Check four existing secp conversion equalities without unchecked casts.

Only copied external candidates are compiled. No main sources/registries are
changed by prepare/check. An independently checked source-only repair is a
separate operation; there is no snapshot regeneration or coverage claim here.
"""
import argparse
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
spec = importlib.util.spec_from_file_location('checked_secp_support', HERE.parent / 'elements-count/support.py')
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)
ROOTS = ['C.jet_secp_fns', 'C.jet_secp_fe_nv', 'C.jet_secp_fe_b32', 'C.jet_frame_constructible_secp']
REPAIRS = {'jet_secp_fns': ['secp_pure_lookup'], 'jet_secp_fe_nv': ['nv_run_eq'],
           'jet_secp_fe_b32': ['sb_run_eq', 'gb_run_eq']}
SHARED_COMMIT = '30404face45383153528f36d915de6d7df11f3f4'


def write(path, value):
    gate.changed({path: json.dumps(value, indent=2) + '\n'})


def repaired(name, original):
    text = original
    for lemma in REPAIRS[name]:
        pattern = r'(\bLemma ' + lemma + r'\b.*?\bProof\.)\s*vm_cast_no_check\s+.*?\bQed\.'
        text, count = re.subn(pattern, r'\1 timeout 10 (vm_compute; reflexivity). Qed.', text, flags=re.S)
        if count != 1:
            raise ValueError('ambiguous conversion repair: ' + lemma)
    gate.safe_source(text, name)
    # Only the frozen proof sentences can differ; all declarations/definitions,
    # other proofs, comments and whitespace are preserved by the replacement.
    return text


def prepare():
    work = Path(tempfile.mkdtemp(prefix='jet-secp-checked.', dir='/tmp')).resolve()
    coq = work / 'Coq'
    shutil.copytree(REPO / 'Coq/Simplicity', coq / 'Simplicity')
    shutil.copy2(REPO / 'Coq/build-jets.sh', coq / 'build-jets.sh')
    cache = json.loads((HERE.parent / 'elements-count/payload/REVIEW.json').read_text())
    cached = Path(cache['candidate'])
    entries, changes, seen, active = [], {}, set(), set()
    def visit(logical):
        if logical in seen:
            return
        if logical in active:
            raise ValueError('dependency cycle')
        active.add(logical)
        name = logical[2:]
        origin = 'Coq/C/' + name + '.v'
        if logical == 'C.jet_frame_constructible_secp':
            raw = subprocess.check_output(['git', 'show', SHARED_COMMIT + ':' + origin], cwd=REPO).decode()
        else:
            raw = (REPO / origin).read_text()
        text = repaired(name, raw) if name in REPAIRS else raw
        code = gate.safe_source(text, origin)
        deps = sorted(set(re.findall(r"\b(C\.[\w']+)", code)) - {logical})
        for dep in deps:
            visit(dep)
        rel = 'C/' + name + '.v'
        changes[coq / rel] = text
        entries.append({'logical': logical, 'relative': rel, 'origin': origin,
                        'origin_sha256': gate.sha(raw.encode()), 'sha256': gate.sha(text.encode()),
                        'dependencies': deps, 'repaired_lemmas': REPAIRS.get(name, [])})
        seen.add(logical)
        active.remove(logical)
    for root in ROOTS:
        visit(root)
    changes[coq / '_CoqProject.jets'] = '-Q Simplicity Simplicity\n-R C C\n' + '\n'.join(
        [str(p.relative_to(coq)) for p in sorted((coq / 'Simplicity').rglob('*.v'))] +
        [e['relative'] for e in entries]) + '\n'
    gate.changed(changes)
    reused = {}
    for entry in entries:
        if entry['logical'] in ROOTS:
            continue
        relative = 'Coq/' + entry['relative']
        old = cached / relative
        obj = old.with_suffix('.vo')
        key = str(obj.relative_to(cached))
        if (old.exists() and gate.sha(old.read_bytes()) == entry['sha256'] and obj.exists()
                and gate.sha(obj.read_bytes()) == cache['evidence_sha256'].get(key)):
            target = coq / entry['relative']
            stamp = old.stat()
            os.utime(target, ns=(stamp.st_atime_ns, stamp.st_mtime_ns))
            for suffix in ['.vo', '.vok', '.vos', '.glob']:
                if old.with_suffix(suffix).exists():
                    shutil.copy2(old.with_suffix(suffix), target.with_suffix(suffix))
            reused[key] = cache['evidence_sha256'][key]
    meta = {'candidate': str(work), 'roots': ROOTS, 'modules': entries,
            'reused_checked_objects': reused, 'shared_commit': SHARED_COMMIT,
            'main_inputs_sha256': gate.inputs.fingerprint(REPO / 'Coq', REPO),
            'staged_patch_sha256': gate.index_hash(), 'coverage_added': 0,
            'normal_registration': False}
    write(work / 'ASSEMBLY.json', meta)
    write(HERE / 'ASSEMBLY.json', meta)
    print(json.dumps({'candidate': str(work), 'modules': len(entries), 'reused': len(reused)}), flush=True)


def check(work):
    meta = json.loads((work / 'ASSEMBLY.json').read_text())
    for entry in meta['modules']:
        source = work / 'Coq' / entry['relative']
        if gate.sha(source.read_bytes()) != entry['sha256']:
            raise ValueError('candidate source drift')
        gate.safe_source(source.read_text(), str(source))
    build = gate.run(work, ['bash', 'build-jets.sh', '-j2'], 'build', 10800)
    print('Checked conversion modules and fresh-frame callers compiled', flush=True)
    results = [entry['logical'] + '.' + lemma for entry in meta['modules'] if entry['logical'] in ROOTS
               for lemma in re.findall(r'^(?:Theorem|Lemma)\s+(\w+)',
                   (work / 'Coq' / entry['relative']).read_text(), re.M)]
    lines = ['Require ' + ' '.join(ROOTS) + '.']
    assumptions = lines[:]
    contracts = lines + ['Set Printing All.', 'Set Printing Width 120.', 'Set Printing Depth 1000000.']
    for name in results:
        assumptions += ['Goal True. idtac "JET_ASSUMPTIONS ' + name + '". exact I. Qed.', 'Print Assumptions ' + name + '.']
        contracts += ['Goal True. idtac "CHECKED_TYPE ' + name + '". exact I. Qed.', 'Check ' + name + '.']
    gate.changed({work / 'assumptions.v': '\n'.join(assumptions) + '\n',
                  work / 'contracts.v': '\n'.join(contracts) + '\n'})
    a = gate.run(work, ['bash', 'build-jets.sh', '--coqc', '-q', str(work / 'assumptions.v')], 'assumptions')
    deps = gate.reports.assumptions((work / 'assumptions.log').read_text())
    if set(deps) != set(results) or any(not ds <= gate.SIX for ds in deps.values()):
        raise ValueError('unreviewed assumptions')
    for entry in meta['modules']:
        for lemma in entry['repaired_lemmas']:
            if deps[entry['logical'] + '.' + lemma]:
                raise ValueError('conversion equality must be closed')
    c = gate.run(work, ['bash', 'build-jets.sh', '--coqc', '-q', str(work / 'contracts.v')], 'contracts')
    if '...' in (work / 'contracts.log').read_text():
        raise ValueError('truncated types')
    print('Full types and assumptions passed; recursive kernel check starting', flush=True)
    k = gate.run(work, ['bash', 'build-jets.sh', '--coqchk', '-o'] + ROOTS, 'kernel', 10800)
    gate.kernel.kernel((work / 'kernel.log').read_text(),
                       sorted((REPO / 'Coq/C/jet_coqchk_axioms.expected').read_text().split()))
    if (gate.index_hash() != meta['staged_patch_sha256'] or
            gate.inputs.fingerprint(REPO / 'Coq', REPO) != meta['main_inputs_sha256']):
        raise ValueError('main inputs changed during audit')
    receipt = {'candidate': str(work), 'assembly_sha256': gate.sha((work / 'ASSEMBLY.json').read_bytes()),
               'build': build, 'assumptions': a, 'contracts': c, 'kernel': k,
               'results': results, 'dependencies': {n: sorted(d) for n, d in deps.items()},
               'evidence_sha256': {str(p.relative_to(work)): gate.sha(p.read_bytes()) for p in work.rglob('*')
                                   if p.is_file() and p.suffix in ['.vo', '.log']},
               'main_installation': False, 'coverage_added': 0, 'normal_registration': False}
    write(work / 'REVIEW.json', receipt)
    write(HERE / 'REVIEW.json', receipt)
    print('Four conversion equalities and full caller closure kernel-checked', flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('action', choices=['prepare', 'check'])
    parser.add_argument('work', nargs='?')
    args = parser.parse_args()
    if args.action == 'prepare':
        prepare()
    else:
        check(Path(args.work).resolve())
