"""Isolated Elements count-jet proof development and audit; no registry writes."""
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
REPO = HERE.parent.parent
s = importlib.util.spec_from_file_location('count_support', HERE / 'support.py')
gate = importlib.util.module_from_spec(s)
s.loader.exec_module(gate)
ROOT = 'C.jet_elements_count_constructible'
FRESH = {ROOT, 'C.jet_elements_count_local', 'C.jet_elements_count_bridge', 'C.jet_elements_count_canonical',
         'C.jet_elements_executable_count'}


def write(path, value):
    gate.changed({path: json.dumps(value, indent=2) + '\n'})


def prepare(payload=False):
    work = Path(tempfile.mkdtemp(prefix='jet-elements-count.', dir='/tmp')).resolve()
    coq = work / 'Coq'
    shutil.copytree(REPO / 'Coq/Simplicity', coq / 'Simplicity')
    shutil.copy2(REPO / 'Coq/build-jets.sh', coq / 'build-jets.sh')
    prior = json.loads((gate.HERE / 'normal/REVIEW.json').read_text())
    prior_work = Path(prior['candidate'])
    entries, sources, seen, visiting = [], {}, set(), set()
    def visit(logical):
        if logical in seen:
            return
        if logical in visiting:
            raise ValueError('cycle')
        visiting.add(logical)
        name = logical[2:]
        archived = logical in [ROOT, 'C.jet_elements_count_payload']
        origin = ('proof-work/elements-count/source/' + name + '.v.source') if archived else ('Coq/C/' + name + '.v')
        raw = (REPO / origin).read_bytes()
        code = gate.safe_source(raw.decode(), origin)
        deps = sorted(set(re.findall(r"\b(C\.[\w']+)", code)) - {logical})
        for dep in deps:
            visit(dep)
        relative = 'C/' + name + '.v'
        sources[coq / relative] = raw.decode()
        entries.append({'logical': logical, 'relative': relative, 'origin': origin,
                        'sha256': gate.sha(raw), 'dependencies': deps, 'fresh': logical in FRESH or archived})
        visiting.remove(logical)
        seen.add(logical)
    visit(ROOT)
    if payload:
        visit('C.jet_elements_count_payload')
    sources[coq / '_CoqProject.jets'] = '-Q Simplicity Simplicity\n-Q C C\n' + '\n'.join(
        [str(p.relative_to(coq)) for p in sorted((coq / 'Simplicity').rglob('*.v'))]
        + [e['relative'] for e in entries]) + '\n'
    for n in ['regenerate-elements-jets.sh', 'jet_elements_translation_unit.c', 'clightgen-linux.ini.in']:
        sources[coq / 'C' / n] = (REPO / 'Coq/C' / n).read_text()
    (work / 'C').symlink_to(REPO / 'C', target_is_directory=True)
    gate.changed(sources)
    reused = {}
    for e in entries:
        if e['fresh']:
            continue
        relative = 'Coq/' + e['relative']
        source = prior_work / relative
        obj = source.with_suffix('.vo')
        key = str(obj.relative_to(prior_work))
        if (source.exists() and gate.sha(source.read_bytes()) == e['sha256'] and
                obj.exists() and prior['evidence_sha256'].get(key) == gate.sha(obj.read_bytes())):
            target = coq / e['relative']
            stamp = source.stat()
            os.utime(target, ns=(stamp.st_atime_ns, stamp.st_mtime_ns))
            for suffix in ['.vo', '.vos', '.vok', '.glob']:
                if source.with_suffix(suffix).exists():
                    shutil.copy2(source.with_suffix(suffix), target.with_suffix(suffix))
            reused[key] = prior['evidence_sha256'][key]
    meta = {'candidate': str(work), 'roots': [ROOT, 'C.jet_elements_count_local'] +
            (['C.jet_elements_count_payload'] if payload else []), 'group': 'payload' if payload else 'constructible',
            'modules': entries, 'reused_checked_objects': reused,
            'main_inputs_sha256': gate.inputs.fingerprint(REPO / 'Coq', REPO),
            'staged_patch_sha256': gate.index_hash(), 'coverage_added': 0,
            'normal_registration': False}
    write(work / 'ASSEMBLY.json', meta)
    print(json.dumps({'candidate': str(work), 'modules': len(entries)}), flush=True)


def check(work):
    meta = json.loads((work / 'ASSEMBLY.json').read_text())
    for e in meta['modules']:
        if gate.sha((REPO / e['origin']).read_bytes()) != e['sha256']:
            raise ValueError('main/archive source drift')
        if gate.sha((work / 'Coq' / e['relative']).read_bytes()) != e['sha256']:
            raise ValueError('candidate source drift')
    build = gate.run(work, ['bash', 'build-jets.sh', '-j2'], 'build')
    print('Count proof closure freshly built', flush=True)
    results = [e['logical'] + '.' + n for e in meta['modules'] if e['origin'].startswith('proof-work/elements-count/source/')
               for n in re.findall(r'^(?:Lemma|Theorem)\s+(\w+)', (work / 'Coq' / e['relative']).read_text(), re.M)]
    results += ['C.jet_elements_count_local.elements_num_inputs_local_spec',
                'C.jet_elements_count_local.elements_num_outputs_local_spec']
    prefix = ['Require ' + ' '.join(meta['roots']) + '.']
    a = prefix[:]
    for n in results:
        a += ['Goal True. idtac "JET_ASSUMPTIONS ' + n + '". exact I. Qed.', 'Print Assumptions ' + n + '.']
    c = prefix + ['Set Printing All.', 'Set Printing Width 120.', 'Set Printing Depth 1000000.']
    for n in results:
        c += ['Goal True. idtac "COUNT_TYPE ' + n + '". exact I. Qed.', 'Check ' + n + '.']
    gate.changed({work / 'assumptions.v': '\n'.join(a) + '\n', work / 'contracts.v': '\n'.join(c) + '\n'})
    ar = gate.run(work, ['bash', 'build-jets.sh', '--coqc', '-q', str(work / 'assumptions.v')], 'assumptions')
    deps = gate.reports.assumptions((work / 'assumptions.log').read_text())
    if set(deps) != set(results) or any(not d <= gate.SIX for d in deps.values()):
        raise ValueError('unreviewed assumptions')
    cr = gate.run(work, ['bash', 'build-jets.sh', '--coqc', '-q', str(work / 'contracts.v')], 'contracts')
    if '...' in (work / 'contracts.log').read_text():
        raise ValueError('truncated types')
    ast = gate.run(work, ['bash', 'C/regenerate-elements-jets.sh', str(work / 'regenerated.v')], 'AST', 120)
    if (work / 'regenerated.v').read_bytes() != (work / 'Coq/C/jets_elements.v').read_bytes():
        raise ValueError('production AST mismatch')
    print('Types/assumptions/AST passed; recursive kernel check starting', flush=True)
    kr = gate.run(work, ['bash', 'build-jets.sh', '--coqchk', '-o'] + meta['roots'], 'kernel', 10800)
    gate.kernel.kernel((work / 'kernel.log').read_text(), sorted((REPO / 'Coq/C/jet_coqchk_axioms.expected').read_text().split()))
    if gate.index_hash() != meta['staged_patch_sha256'] or gate.inputs.fingerprint(REPO / 'Coq', REPO) != meta['main_inputs_sha256']:
        raise ValueError('main inputs changed during audit')
    evidence = {str(p.relative_to(work)): gate.sha(p.read_bytes()) for p in work.rglob('*')
                if p.is_file() and p.suffix in ['.vo', '.log']}
    receipt = {'candidate': str(work), 'assembly_sha256': gate.sha((work / 'ASSEMBLY.json').read_bytes()),
               'build': build, 'assumptions': ar, 'contracts': cr, 'AST': ast, 'kernel': kr,
               'results': results, 'dependencies': {n: sorted(d) for n, d in deps.items()},
               'evidence_sha256': evidence, 'coverage_added': 0, 'normal_registration': False}
    write(work / 'REVIEW.json', receipt)
    destination = HERE / meta.get('group', 'constructible')
    gate.changed({destination / 'ASSEMBLY.json': (work / 'ASSEMBLY.json').read_text(),
                  destination / 'REVIEW.json': (work / 'REVIEW.json').read_text()})
    print('Count proof closure kernel-checked', flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(); p.add_argument('action', choices=['prepare', 'prepare-payload', 'check']); p.add_argument('work', nargs='?')
    args = p.parse_args()
    if args.action in ['prepare', 'prepare-payload']:
        prepare(args.action == 'prepare-payload')
    else:
        check(Path(args.work).resolve())
