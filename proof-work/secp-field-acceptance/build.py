"""Compile the unchanged normal project independently of failed acceptance.

make -k attempts independent modules after a failure. It neither suppresses
the final nonzero status nor skips the identity gate in an acceptance run.
No successful receipt is written unless the entire build exits zero.
"""
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('field_independent_build_runner', HERE / 'run.py')
r = importlib.util.module_from_spec(sp)
sp.loader.exec_module(r)
s = r.s


def main():
    work, preparation = r.identity()
    prior = json.loads((HERE / 'GENERATE-PROCESS.json').read_text())
    if not prior['terminal'] or prior['exit_code'] != 1:
        raise ValueError('expected recorded terminal full-gate failure, not a live generation run')
    if (HERE / 'BUILD-LAUNCH.json').exists():
        raise ValueError('normal build already launched; poll its existing live/terminal handle')
    command = ['bash', 'build-jets.sh', '-j2', '-k']
    s.changed({HERE / 'BUILD-LAUNCH.json': json.dumps(dict(candidate=str(work), command=command,
        preparation_sha256=s.sha((HERE / 'PREPARATION.json').read_bytes()),
        builder_sha256=s.sha(Path(__file__).read_bytes()), complete=False,
        accepted=False), indent=2) + '\n'})
    row = r.run_logged(work, command, 'build')
    r.identity()
    paths = [n for n in (work / 'Coq/_CoqProject.jets').read_text().splitlines() if n.endswith('.v')]
    modules = {n: dict(source_sha256=s.sha((work / 'Coq' / n).read_bytes()),
        object_sha256=s.sha((work / 'Coq' / n).with_suffix('.vo').read_bytes())) for n in paths}
    result = dict(candidate=str(work), build=row, modules=modules,
        input_sha256=preparation['input_sha256'], complete=True, accepted=False,
        accepted_coverage_added=0, unresolved_gate='Bitcoin base primitive name mismatch: LockTime')
    s.changed({HERE / 'BUILT.json': json.dumps(result, indent=2) + '\n',
        HERE / 'build.log': (work / 'build.log').read_text()})
    print('Complete normal project compiled; the identity/acceptance failure remains unresolved', flush=True)


if __name__ == '__main__':
    main()
