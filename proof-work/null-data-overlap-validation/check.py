"""Native API-aliasing validation using the actual complete C environment builders.

Exit zero means an aliasing discrepancy reproduced with two passing controls;
this is not a successful equivalence proof or a CompCert counterexample.
"""
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('overlap_validation_support', HERE.parent / 'elements-count/support.py')
s = importlib.util.module_from_spec(sp)
sp.loader.exec_module(s)
SOURCES = ['C/frame.c', 'C/elements/elementsJets.c', 'C/elements/env.c',
           'C/elements/txEnv.c', 'C/elements/ops.c', 'C/rsort.c', 'C/sha256.c']


def run(work, command, stem, env=None, timeout=120):
    log = work / (stem + '.log')
    with log.open('wb') as out:
        done = subprocess.run(command, cwd=s.REPO, stdout=out, stderr=subprocess.STDOUT,
                              env=env, timeout=timeout)
    if done.returncode:
        raise ValueError('failed native validation ' + stem + '; inspect ' + str(log))
    return dict(command=command, exit_code=done.returncode, log_sha256=s.sha(log.read_bytes()))


def main(work):
    if (HERE / 'VALIDATION.json').exists():
        raise ValueError('native validation already recorded; inspect its completed evidence')
    if (work == s.REPO or s.REPO in work.parents or
        (work / 'probe.c').is_symlink() or (work / 'probe.c').read_bytes() != (HERE / 'probe.c.source').read_bytes()):
        raise ValueError('distinct private tree and exact archived diagnostic required')
    before, index = s.input_map(), s.index_hash()
    commands = {'compiler': run(work, ['clang', '--version'], 'compiler')}
    env = dict(os.environ, ASAN_OPTIONS='halt_on_error=1:detect_leaks=0',
               UBSAN_OPTIONS='halt_on_error=1:print_stacktrace=1')
    cases = {}
    for width in ['native', 'word64']:
        for mode in ['debug', 'production']:
            for opt in ['0', '2']:
                stem = width + '-' + mode + '-O' + opt
                output = work / stem
                command = ['clang', '-std=c11', '-O' + opt, '-g', '-fno-omit-frame-pointer',
                    '-fsanitize=address,undefined', '-fno-sanitize-recover=all',
                    '-ffunction-sections', '-fdata-sections', '-IC', '-IC/include']
                if width == 'word64':
                    command += ['-DUWORD=uint64_t']
                if mode == 'production':
                    command += ['-DPRODUCTION']
                command += [str(work / 'probe.c'), *SOURCES, '-Wl,-dead_strip', '-o', str(output)]
                commands[stem + '-compile'] = run(work, command, stem + '-compile')
                commands[stem] = run(work, [str(output)], stem, env=env, timeout=30)
                text = (work / (stem + '.log')).read_text()
                if ('actual_builders=mallocTransaction,mallocTapEnv,build_txEnv numInputs=1 numOutputs=1 parsed_len=1' not in text or
                    'discrepancy_reproduced_with_real_builders_and_two_passing_controls=1\n' not in text or
                    re.search(r'AddressSanitizer|UndefinedBehaviorSanitizer|runtime error:|ERROR:', text)):
                    raise ValueError('wrong builder/discrepancy/sanitizer outcome: ' + stem)
                rows = re.findall(r'UWORD_BIT=(\d+) layout=(\d+) before=0,0 success=1 expected=1,1 actual=(\d),(\d) final_offset=0 source_after=(\d+),(\d+) matches=(\d)', text)
                if len(rows) != 3 or [r[1] for r in rows] != ['0', '1', '2']:
                    raise ValueError('incomplete original-input/layout controls: ' + stem)
                bits = int(rows[0][0])
                if bits not in [16, 64] or width == 'word64' and bits != 64:
                    raise ValueError('unexpected machine-word configuration')
                for r in rows:
                    if int(r[0]) != bits or r[2:4] != (('1', '0') if r[1] == '1' else ('1', '1')) or r[6] != ('0' if r[1] == '1' else '1'):
                        raise ValueError('mismatch or failed control not reproduced: ' + stem)
                cases[stem] = dict(uword_bits=bits, disjoint_controls_passed=2,
                    overlapping_original_input=[0, 0], overlapping_expected_tags=[1, 1],
                    overlapping_actual_tags=[1, 0], source_after_overlap=[int(rows[1][4]), int(rows[1][5])],
                    actual_environment_builders_used=True, sanitizers_reported_error=False)
                print('Reproduced with actual builders and two passing controls: ' + stem, flush=True)
    if s.input_map() != before or s.index_hash() != index:
        raise ValueError('native validation changed main semantic inputs or original staging')
    record = dict(candidate=str(work), commands=commands, cases=cases,
        compiler_sha256=s.sha((work / 'compiler.log').read_bytes()),
        probe_source_sha256=s.sha((work / 'probe.c').read_bytes()),
        source_sha256={n: d for n, d in before.items() if n.startswith('C/')},
        main_input_sha256=s.inputs.fingerprint(s.REPO / 'Coq', s.REPO), staged_patch_sha256=index,
        native_diagnostic=True, complete_environment_builders_used=True, actual_null_data_parser_used=True,
        passing_disjoint_controls=16, overlapping_discrepancies=8,
        sanitizers=['address', 'undefined'], leak_detection_enabled=False,
        compcert_execution_counterexample_proved=False, valid_bitmachine_layout_counterexample=False,
        c_or_header_changed=False, whole_jet_equivalence_proved=False, coverage_added=0)
    s.changed({HERE / 'VALIDATION.json': json.dumps(record, indent=2) + '\n',
        **{HERE / (n + '.log'): (work / (n + '.log')).read_text() for n in commands}})
    print('Native API overlap discrepancy validated; not an evaluator-valid or formal Clight counterexample', flush=True)


if __name__ == '__main__':
    if len(sys.argv) != 2:
        raise ValueError('usage: check.py PRIVATE_TREE')
    main(Path(sys.argv[1]).resolve())
