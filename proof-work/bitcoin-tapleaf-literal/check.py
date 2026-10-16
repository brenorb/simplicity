"""Fresh literal TapLeaf program and original-C getter checks, no admission."""
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('bitcoin_tapleaf_shared', HERE.parent / 'elements-tap-getters/check.py')
shared = importlib.util.module_from_spec(sp)
sp.loader.exec_module(shared)
s = shared.s
MODULE = 'C.jet_bitcoin_tapleaf_literal'
NEW = 'C/jet_bitcoin_tapleaf_literal.v'
ROOTS = ['C.jet_bitcoin_tapleaf_hash_spec', 'C.jet_bitcoin_tapleaf_hash_local', MODULE]
BASE = HERE.parent / 'elements-txid-admission'
PURE = [MODULE + '.' + n for n in ['tapleaf_ascii_string', 'tapleaf_literal_prefix_matches',
                                  'tapleaf_hash_literal_matches']]
ENDPOINT = MODULE + '.bitcoin_tapleaf_hash_literal_local_spec'
KERNEL = ['bash', '-c', 'ulimit -s 65520; exec bash build-jets.sh --coqchk -silent -o ' + MODULE]


def tree(work):
    installation = json.loads((BASE / 'INSTALLATION.json').read_text())
    actual = json.loads((BASE / 'MAIN-ACCEPTANCE.json').read_text())
    base = Path(installation['candidate'])
    if (work == base or work == s.REPO or s.REPO in work.parents or
        (work / 'Coq').is_symlink()):
        raise ValueError('use a distinct private proof tree')
    if (actual['actual_main_acceptance'] is not True or actual['exit_code'] != 0 or
        actual['installation_sha256'] != s.sha((BASE / 'INSTALLATION.json').read_bytes()) or
        actual['audit_input_sha256'] != installation['candidate_input_sha256'] or
        s.inputs.fingerprint(base / 'Coq', base) != actual['audit_input_sha256']):
        raise ValueError('completed actual418 baseline identity changed')
    inherited = shared.inventory(base / 'Coq')
    if shared.inventory(work / 'Coq') != inherited | {NEW}:
        raise ValueError('unexpected proof source/metadata inventory')
    for n in inherited:
        if (work / 'Coq' / n).read_bytes() != (base / 'Coq' / n).read_bytes():
            raise ValueError('inherited source changed: ' + n)
    p = work / 'Coq' / NEW
    if p.read_bytes() != (HERE / 'source' / (p.name + '.source')).read_bytes():
        raise ValueError('archive/private source differs')
    s.safe_source(p.read_text(), NEW)
    return base, actual


def main(work):
    if (HERE / 'RUN.json').exists():
        raise ValueError('checker already launched; inspect existing handle/receipt')
    base, actual = tree(work)
    before, index = s.input_map(), s.index_hash()
    fingerprint = s.inputs.fingerprint(work / 'Coq', work)
    commands = {}
    for m in ROOTS:
        commands[m] = s.run(work, ['bash', 'build-jets.sh', '--coqc', '-q', m.replace('.', '/') + '.v'], m, 300)
        print('Freshly compiled ' + m, flush=True)
    results, definitions, deps = shared.reports(work, [(MODULE, work / 'Coq' / NEW)],
                                                'bitcoin-tapleaf-literal', commands)
    if (len(results), len(definitions)) != (4, 6) or set(results) != set(PURE + [ENDPOINT]):
        raise ValueError('unexpected complete declaration inventory')
    if any(deps[n] for n in PURE) or deps[ENDPOINT] != s.SIX:
        raise ValueError('literal bridge not closed or C assumptions changed')
    record = dict(candidate=str(work), base_candidate=str(base),
        base_main_acceptance_sha256=s.sha((BASE / 'MAIN-ACCEPTANCE.json').read_bytes()),
        base_installation_sha256=s.sha((BASE / 'INSTALLATION.json').read_bytes()),
        base_input_sha256=actual['audit_input_sha256'], candidate_input_sha256=fingerprint,
        main_inputs=before, staged_patch_sha256=index, modules=[MODULE], fresh_modules=ROOTS,
        new_sources=[NEW], results=results, definitions=definitions, closed_results=PURE,
        endpoints=[ENDPOINT], dependencies={n: sorted(ds) for n, ds in deps.items()},
        source_sha256={m: s.sha((work / 'Coq' / (m.replace('.', '/') + '.v')).read_bytes()) for m in ROOTS},
        object_sha256={m: s.sha((work / 'Coq' / (m.replace('.', '/') + '.vo')).read_bytes()) for m in ROOTS},
        commands=commands, tools_sha256={'check.py': s.sha(Path(__file__).read_bytes())},
        canonical_source_gate_complete=False, c_environment_builder_establishment=False,
        recursive_kernel_check=False, normal_registration=False, coverage_added=0, full_acceptance=False)
    s.changed({HERE / 'RUN.json': json.dumps(record, indent=2) + '\n',
        **{HERE / (n + '.log'): (work / (n + '.log')).read_text() for n in commands}})
    print('Four complete results (three closed) freshly reported; AST/kernel checks next', flush=True)
    commands['ast'] = s.run(work, ['bash', 'C/check-bitcoin-jets-generation.sh'], 'ast', 180)
    print('Original Bitcoin AST matched; recursive kernel check next', flush=True)
    commands['kernel'] = s.run(work, KERNEL, 'kernel', 1800)
    s.kernel.kernel((work / 'kernel.log').read_text(), sorted((work / 'Coq/C/jet_coqchk_axioms.expected').read_text().split()))
    tree(work)
    if (s.input_map() != before or s.index_hash() != index or
        s.inputs.fingerprint(work / 'Coq', work) != fingerprint):
        raise ValueError('main/index/private source changed during checks')
    record.update(commands=commands, recursive_kernel_check=True)
    s.changed({HERE / 'CHECKED.json': json.dumps(record, indent=2) + '\n',
        **{HERE / (n + '.log'): (work / (n + '.log')).read_text() for n in ['ast', 'kernel']}})
    print('Literal TapLeaf program and original-C getter recursively kernel-checked; source/admission review remains', flush=True)


if __name__ == '__main__':
    main(Path(sys.argv[1]).resolve())
