"""Stage the actual Bitcoin taproot builder in an isolated derived C namespace.

The original SHA proof sources are recompiled for the generated environment
unit, never overwritten in main. New builder sources are frozen Git blobs.
"""
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
COMMIT = '30404face45383153528f36d915de6d7df11f3f4'
spec = importlib.util.spec_from_file_location('tapenv_patch', HERE.parent / 'nullable-admission/assemble.py')
patch = importlib.util.module_from_spec(spec); spec.loader.exec_module(patch)
spec = importlib.util.spec_from_file_location('tapenv_scanner', REPO / 'Coq/scan-jet-proofs.py')
scanner = importlib.util.module_from_spec(spec); spec.loader.exec_module(scanner)
ROOTS = ['jet_bitcoin_env_tapenv_link', 'jet_bitcoin_env_tapenv_describe', 'jet_bitcoin_env_tapenv_raw']


def blob(path): return subprocess.check_output(['git', 'show', COMMIT + ':' + path], cwd=REPO)


def stage():
    work = Path(tempfile.mkdtemp(prefix='jet-bitcoin-tapenv.', dir='/tmp')).resolve()
    coq = work / 'Coq'
    # Source/object copies, never symlinks to main compiler outputs. Recompile
    # every module transitively affected by the changed SHA program.
    shutil.copytree(REPO / 'Coq/Simplicity', coq / 'Simplicity')
    for name in ['build-jets.sh']:
        shutil.copy2(REPO / 'Coq' / name, coq / name)
    for name in ['C', 'Haskell']: (work / name).symlink_to(REPO / name, target_is_directory=True)
    paths = subprocess.check_output(['git', 'ls-tree', '-r', '--name-only', COMMIT, 'Coq/bitcoin-env/C'], cwd=REPO, text=True).splitlines()
    env_paths = {Path(p).stem: p for p in paths if p.endswith('.v')}
    visited, active, order, entries, inherited, changes, affected = set(), set(), [], [], {}, {}, {}
    def visit(name):
        if name in visited: return
        if name in active: raise ValueError('cyclic derived closure')
        active.add(name)
        origin = 'Coq/C/jets_bitcoin_env.v' if name == 'jets_sha' else env_paths.get(name, 'Coq/C/' + name + '.v')
        raw = blob(origin)
        if origin.startswith('Coq/C/') and name != 'jets_sha':
            main = REPO / origin
            if not main.exists() or main.read_bytes() != raw: raise ValueError('inherited source collision: ' + origin)
            inherited[origin] = patch.sha(raw)
        code = scanner.code_only(raw.decode())
        if re.search(r'\b(?:Axiom|Parameter|Admitted|admit|vm_cast_no_check|native_cast_no_check)\b', code):
            raise ValueError('forbidden proof construct: ' + name)
        deps = sorted(set(re.findall(r'\bC\.(\w+)', code)))
        for dep in deps: visit(dep)
        affected[name] = name == 'jets_sha' or origin.startswith('Coq/bitcoin-env/') or any(affected[d] for d in deps)
        changes[coq / 'C' / (name + '.v')] = raw.decode()
        order.append(name)
        entries.append({'name': name, 'origin': origin, 'sha256': patch.sha(raw),
                        'results': re.findall(r'^(?:Theorem|Lemma|Corollary)\s+(\w+)', code, re.M),
                        'definitions': re.findall(r'^(?:Definition|Fixpoint|Inductive)\s+(\w+)', code, re.M)})
        active.remove(name); visited.add(name)
    for name in ROOTS: visit(name)
    for name in ['jet_bitcoin_env_translation_unit.c', 'jet_sha_translation_unit.c', 'regenerate-bitcoin-env.sh', 'clightgen-linux.ini.in']:
        changes[coq / 'C' / name] = blob('Coq/C/' + name).decode()
    changes[coq / 'C/jets_bitcoin_env.v'] = blob('Coq/C/jets_bitcoin_env.v').decode()
    simp = [str(p.relative_to(coq)) for p in sorted((coq / 'Simplicity').rglob('*.v'))]
    changes[coq / '_CoqProject.jets'] = '-Q Simplicity Simplicity\n-R C C\n' + '\n'.join(simp + ['C/' + n + '.v' for n in order]) + '\n'
    meta = {'candidate': str(work), 'source_commit': COMMIT, 'roots': ROOTS, 'modules': entries,
            'inherited_sha256': inherited, 'affected': affected, 'normal_registration': False, 'coverage_added': 0,
            'scope': 'Actual Bitcoin mallocTapEnv and canonical cached-hash links in a distinct derived environment program; memcpy_model and startup/input premises remain explicit.'}
    changes[work / 'ASSEMBLY.json'] = json.dumps(meta, indent=2) + '\n'
    patch.patch_files(changes)
    for entry in entries:
        name = entry['name']; source = REPO / entry['origin']
        if not affected[name] and source.exists():
            stamp = source.stat()
            os.utime(coq / 'C' / (name + '.v'), ns=(stamp.st_atime_ns, stamp.st_mtime_ns))
            for suffix in ['.vo', '.vos', '.vok', '.glob']:
                compiled = source.with_suffix(suffix)
                if compiled.exists(): shutil.copy2(compiled, (coq / 'C' / (name + '.v')).with_suffix(suffix))
    print(json.dumps({'candidate': str(work), 'closure_modules': len(order),
                      'new_builder_modules': sum(e['origin'].startswith('Coq/bitcoin-env/') for e in entries), 'main_unchanged': True}, indent=2))


if __name__ == '__main__': stage()
