"""Stage the frozen SHA startup batch outside main during its acceptance audit.

Only namespace prefixes are transported to C. Existing main sources are
copied unchanged; no main Coq file or registry is modified by this script.
"""
import importlib.util
import json
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
NAMES = ['jet_sha_startup_globals', 'jet_sha_startup_state', 'jet_sha_startup_jets',
         'jet_sha_startup_env_jets', 'jet_sha_startup_setup', 'jet_sha_startup_env_callers',
         'jet_sha_startup_executable', 'jet_sha_startup_runs', 'jet_sha_startup_lifecycle',
         'jet_sha_startup_init', 'jet_sha_startup_env_runs']


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec); spec.loader.exec_module(mod)
    return mod


patch = load('startup_patch', HERE.parent / 'nullable-admission/assemble.py')
scanner = load('startup_scanner', REPO / 'Coq/scan-jet-proofs.py')


def main():
    originals = {}
    for name in ['jet_clight_forward', 'jet_sha_initial_globals']:
        originals[name] = (REPO / 'proof-work/sha-support' / (name + '.v.source')).read_text()
    for name in NAMES:
        originals[name] = subprocess.check_output(['git', 'show', COMMIT + ':Coq/startup/proofs/' + name + '.v'], cwd=REPO).decode()
    expected_prereqs = subprocess.check_output(['git', 'show', COMMIT + ':Coq/startup/PREREQUISITES.sha256'], cwd=REPO).decode()
    for line in expected_prereqs.splitlines():
        value, name = line.split()
        if patch.sha((REPO / 'proof-work/sha-support' / name).read_bytes()) != value:
            raise ValueError('startup archive prerequisite drift')
    transported = {n: s.replace('JetStartupReview.', 'C.').replace('JetStartup.', 'C.') for n, s in originals.items()}
    for name, text in transported.items():
        existing = REPO / 'Coq/C' / (name + '.v')
        if existing.exists() and existing.read_text() != text:
            raise ValueError('different startup source already exists in main: ' + name)
        code = scanner.code_only(text)
        if re.search(r'\b(?:admit|Admitted|Axiom|Parameter|Conjecture|vm_cast_no_check|native_cast_no_check)\b', code):
            raise ValueError('forbidden proof construct: ' + name)
    work = Path(tempfile.mkdtemp(prefix='jet-sha-startup-review.', dir='/tmp')).resolve()
    coq = work / 'Coq'
    shutil.copytree(REPO / 'Coq', coq, symlinks=True)
    for name in ['C', 'Haskell']:
        (work / name).symlink_to(REPO / name, target_is_directory=True)
    patch.patch_files({coq / 'C' / (name + '.v'): text for name, text in transported.items()})
    done, active, order, inherited = set(), set(), [], {}
    def visit(name):
        if name in done: return
        if name in active: raise ValueError('cyclic startup closure')
        active.add(name)
        path = coq / 'C' / (name + '.v')
        code = scanner.code_only(path.read_text())
        for dep in sorted(set(re.findall(r'\bC\.(\w+)', code))): visit(dep)
        if name not in transported:
            inherited['Coq/C/' + name + '.v'] = patch.sha(path.read_bytes())
        if name in transported or not path.with_suffix('.vo').exists(): order.append(name)
        active.remove(name); done.add(name)
    for name in transported: visit(name)
    inventory = (coq / '_CoqProject.jets').read_text()
    rows = set(inventory.splitlines())
    extra = ['C/' + name + '.v' for name in order if 'C/' + name + '.v' not in rows]
    modules = [{'name': name, 'path': 'Coq/C/' + name + '.v',
                'source_sha256': patch.sha(originals[name].encode()), 'sha256': patch.sha(text.encode()),
                'results': re.findall(r'^(?:Theorem|Lemma|Corollary)\s+(\w+)', scanner.code_only(text), re.M)}
               for name, text in transported.items()]
    meta = {'candidate': str(work), 'shared_commit': COMMIT, 'modules': modules,
            'compile_order': order, 'inherited_sha256': inherited,
            'namespace_only_transport': True, 'main_inputs_untouched': True,
            'full_acceptance': False, 'coverage_added': 0}
    patch.patch_files({coq / '_CoqProject.jets': inventory + '\n'.join(extra) + '\n',
                       work / 'ASSEMBLY.json': json.dumps(meta, indent=2) + '\n'})
    print(json.dumps({'candidate': str(work), 'new_modules': len(modules), 'results': sum(len(e['results']) for e in modules),
                      'explicit_compile_modules': len(order), 'main_untouched': True}, indent=2))


if __name__ == '__main__': main()
