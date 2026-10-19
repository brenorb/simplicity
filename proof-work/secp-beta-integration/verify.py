"""Fresh ordinary-module reports and recursive kernel audit, not acceptance."""
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('beta_integration_assembly', HERE / 'assemble.py')
a = importlib.util.module_from_spec(sp)
sp.loader.exec_module(a)
s = a.s
reporter = s.load('beta_integration_full_reports', HERE.parent / 'secp-field-integration/verify.py')
ENDPOINT = a.ROOT + '.fe_multiply_beta_initialized_local_spec'


def built():
    work, prep = a.identity()
    result = json.loads((HERE / 'BUILT.json').read_text())
    if not result['complete'] or result['preparation_sha256'] != s.sha((HERE / 'PREPARATION.json').read_bytes()):
        raise ValueError('normal beta build is not complete for these inputs')
    for stem, row in result['commands'].items():
        if row['exit_code'] or row['log_sha256'] != s.sha((work / (stem + '.log')).read_bytes()):
            raise ValueError('normal beta build log differs: ' + stem)
    if set(result['source_objects']) != set(prep['sources']):
        raise ValueError('normal beta source/object inventory differs')
    for name, digest in result['source_objects'].items():
        if s.sha((work / name).with_suffix('.vo').read_bytes()) != digest:
            raise ValueError('normal beta object differs: ' + name)
    return work, prep, result


def inherited_profiles():
    paths = ['proof-work/secp-borrowed-region/CHECKED.json', 'proof-work/secp-field-borrowed/RUN.json',
        'proof-work/secp-beta-global/RUN.json', 'proof-work/clight-internal-frame/RUN.json',
        'proof-work/secp-beta-public/RUN.json']
    profiles, inputs = {}, {}
    for path in paths:
        raw = a.blob(path)
        inputs[path] = s.sha(raw)
        for name, axioms in json.loads(raw)['dependencies'].items():
            module, short = name.rsplit('.', 1)
            if module not in a.MAPPING:
                continue
            normal = a.MAPPING[module] + '.' + short
            if normal in profiles and profiles[normal] != set(axioms):
                raise ValueError('inconsistent original assumption profile: ' + name)
            profiles[normal] = set(axioms)
    if len(profiles) != 107 or profiles[ENDPOINT] != s.SIX:
        raise ValueError('missing exact original beta-family assumption profiles')
    return profiles, inputs


def compare_contracts(work, prep):
    aliases = {}
    for name, row in prep['sources'].items():
        if not row['renamed']:
            continue
        normal = name.removeprefix('Coq/').removesuffix('.v').replace('/', '.')
        old = row['original_module']
        results, definitions = reporter.g.declarations((work / name).read_text(), normal)
        for declaration in results + definitions:
            short = declaration.rsplit('.', 1)[1]
            for module in [old, old.rsplit('.', 1)[-1], normal, normal.rsplit('.', 1)[-1]]:
                alias = module + '.' + short
                if alias in aliases and aliases[alias] != declaration:
                    raise ValueError('ambiguous printed module alias: ' + alias)
                aliases[alias] = declaration
    def chunks(raw):
        pieces = re.split(r'(?m)^TAP_(TYPE|DEF) (\S+)\n', raw)
        result = {}
        for kind, name, body in zip(pieces[1::3], pieces[2::3], pieces[3::3]):
            if name not in aliases:
                continue
            key = kind + ' ' + aliases[name]
            # Full names and the printer's unambiguous short module aliases
            # resolve to the same known declaration; no general term rewriting.
            body = re.sub(r'[A-Za-z_][\w\x27]*(?:\.[A-Za-z_][\w\x27]*)+',
                lambda match: aliases.get(match[0], match[0]), body)
            result[key] = re.sub(r'\s+', '', body)
        return result
    paths = ['proof-work/secp-borrowed-region/borrowed-contracts.log',
        'proof-work/secp-field-borrowed/borrowed-multiply-contracts.log',
        'proof-work/secp-beta-global/beta-audit-contracts.log',
        'proof-work/clight-internal-frame/internal-audit-contracts.log',
        'proof-work/secp-beta-public/beta-public-audit-contracts.log']
    expected, inputs = {}, {}
    for path in paths:
        raw = a.blob(path)
        inputs[path] = s.sha(raw)
        for key, value in chunks(raw.decode()).items():
            if key in expected and expected[key] != value:
                raise ValueError('original contract reports disagree: ' + key)
            expected[key] = value
    actual = chunks((work / 'integration-contracts.log').read_text())
    if len(expected) != 139 or set(actual) != set(expected):
        raise ValueError('missing original or ordinary full contract/definition')
    mismatches = [key for key in expected if expected[key] != actual[key]]
    if mismatches:
        raise ValueError('ordinary full types/definitions differ beyond module naming: ' + str(mismatches))
    return dict(original_report_inputs=inputs, compared_theorem_types=107, compared_definitions=32,
        module_alias_only=True, normalized_sha256=s.sha(json.dumps(actual, sort_keys=True).encode()))


def source_review(work):
    original = a.p.source_review()
    for name, digest in original['authority_inputs'].items():
        if s.sha((work / name).read_bytes()) != digest:
            raise ValueError('candidate canonical source differs: ' + name)
    source = (work / 'Coq/C/jet_secp_beta_local.v').read_text()
    a.p.contract_source(source)
    fixtures = [
        source.replace('(Word 8) (Word 8)', '(Word 7) (Word 8)', 1),
        source.replace('(Word 8) (Word 8)', '(Word 8) (Word 7)', 1),
        source.replace('f_simplicity_fe_multiply_beta (Word', 'f_secp256k1_fe_mul (Word', 1),
        source.replace('local_spec beta_initialized', 'local_spec (fun _ => True)', 1),
        source.replace('(@literal_fe_multiply_beta Alg.CoreFunSem).', '(@canonical_fe_normalize Alg.CoreFunSem).', 1),
        source.replace('  secp_jet_initialized_local_spec beta_initialized',
            '  False -> secp_jet_initialized_local_spec beta_initialized', 1)]
    for n, fixture in enumerate(fixtures):
        if fixture == source:
            raise ValueError('vacuous ordinary beta contract mutation: ' + str(n))
        try:
            a.p.contract_source(fixture)
        except ValueError:
            continue
        raise ValueError('ordinary beta contract mutation escaped: ' + str(n))
    # Assembly identity proves exact reverse module-only renaming for the
    # actual global/specification modules, not a newly substituted port.
    return dict(authority_inputs=original['authority_inputs'], ordinary_contract_mutations_rejected=len(fixtures),
        actual_ordinary_contract_source_sha256=s.sha(source.encode()), exact_reversible_proof_renaming=True)


def reports():
    work, prep, build = built()
    if (HERE / 'REPORT-LAUNCH.json').exists():
        raise ValueError('beta integration reports already launched; poll original process')
    expected, inputs = inherited_profiles()
    modules = [(new, work / 'Coq' / (new.replace('.', '/') + '.v')) for new in a.MAPPING.values()]
    declarations = {name for module, path in modules for name in reporter.g.declarations(path.read_text(), module)[0]}
    if declarations != set(expected):
        raise ValueError('ordinary beta theorem inventory differs from checked originals')
    s.changed({HERE / 'REPORT-LAUNCH.json': json.dumps(dict(complete=False, candidate=str(work),
        built_sha256=s.sha((HERE / 'BUILT.json').read_bytes()), verifier_sha256=s.sha(Path(__file__).read_bytes()),
        whole_report_deadline_seconds=600), indent=2) + '\n'})
    commands = {}
    results, definitions, deps = reporter.full_reports(work, modules, commands)
    if deps != expected or len(definitions) != 32:
        raise ValueError('ordinary beta assumptions or definition inventory changed')
    compared = compare_contracts(work, prep)
    query = subprocess.run(['bash', 'build-jets.sh', '--coqtop', '-quiet'],
        input='Require ' + a.ROOT + '.\nPrint Libraries.\n', cwd=work / 'Coq', env=s.ENV,
        text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=60)
    loaded = set(re.findall(r'^\s+((?:C|Simplicity|Util)\.[\w.]+)\s*$', query.stdout, re.M))
    wanted = {name.removeprefix('Coq/').removesuffix('.v').replace('/', '.') for name in prep['sources']}
    if query.returncode or re.search(r'(?m)^(?:Error|Anomaly):', query.stdout) or loaded != wanted:
        raise ValueError('ordinary beta loaded source closure differs: ' + str(loaded ^ wanted))
    if any(name in query.stdout for name in a.MAPPING):
        raise ValueError('private beta proof namespace leaked into ordinary build')
    commands['beta-integration-original-targets'] = s.run(work,
        [sys.executable, '-B', 'check-jet-source-target.py'], 'beta-integration-original-targets', 60)
    review = source_review(work)
    built()
    r = dict(candidate=str(work), built_sha256=s.sha((HERE / 'BUILT.json').read_bytes()),
        verifier_sha256=s.sha(Path(__file__).read_bytes()), report_helper_sha256=s.sha(Path(reporter.__file__).read_bytes()),
        inherited_profile_inputs=inputs, results=results, definitions=definitions,
        dependencies={n: sorted(ds) for n, ds in deps.items()}, commands=commands,
        loaded_source_modules=sorted(loaded), endpoint=ENDPOINT, source_review=review,
        exact_original_type_definition_comparison=compared,
        normal_registration=False, coverage_added=0, recursive_kernel_check=False)
    s.changed({HERE / 'REPORTED.json': json.dumps(r, indent=2) + '\n', HERE / 'loaded-libraries.log': query.stdout,
        HERE / 'integration-assumptions.log': (work / 'integration-assumptions.log').read_text(),
        HERE / 'integration-contracts.log': (work / 'integration-contracts.log').read_text(),
        HERE / 'original-targets.log': (work / 'beta-integration-original-targets.log').read_text()})
    print('Ordinary beta reports: 107 unchanged assumption profiles, 32 definitions, 249 fresh local modules', flush=True)


def reported():
    work, prep, build = built()
    r = json.loads((HERE / 'REPORTED.json').read_text())
    expected, inputs = inherited_profiles()
    if (r['built_sha256'] != s.sha((HERE / 'BUILT.json').read_bytes()) or
            r['verifier_sha256'] != s.sha(Path(__file__).read_bytes()) or
            r['report_helper_sha256'] != s.sha(Path(reporter.__file__).read_bytes()) or
            r['inherited_profile_inputs'] != inputs or r['source_review'] != source_review(work) or
            r['exact_original_type_definition_comparison'] != compare_contracts(work, prep) or
            {name: set(ds) for name, ds in r['dependencies'].items()} != expected):
        raise ValueError('ordinary beta report identities differ')
    for stem, row in r['commands'].items():
        if row['exit_code'] or row['log_sha256'] != s.sha((work / (stem + '.log')).read_bytes()):
            raise ValueError('ordinary beta report log differs: ' + stem)
    for name in ['integration-assumptions.log', 'integration-contracts.log']:
        if (HERE / name).read_bytes() != (work / name).read_bytes():
            raise ValueError('archived ordinary beta report differs: ' + name)
    return work, r


def kernel_command():
    return ['bash', '-c', 'ulimit -s 65520; exec bash build-jets.sh --coqchk -silent -o ' + a.ROOT]


def kernel():
    work, report = reported()
    if (HERE / 'KERNEL-LAUNCH.json').exists():
        raise ValueError('ordinary beta kernel already launched; poll original process')
    s.changed({HERE / 'KERNEL-LAUNCH.json': json.dumps(dict(candidate=str(work), command=kernel_command(),
        reported_sha256=s.sha((HERE / 'REPORTED.json').read_bytes()), complete=False), indent=2) + '\n'})
    row = s.run(work, kernel_command(), 'beta-integration-kernel', 900)
    log = (work / 'beta-integration-kernel.log').read_text()
    s.kernel.kernel(log, sorted((work / 'Coq/C/jet_coqchk_axioms.expected').read_text().split()))
    reported()
    s.changed({HERE / 'CHECKED.json': json.dumps(dict(candidate=str(work), kernel=row,
        reported_sha256=s.sha((HERE / 'REPORTED.json').read_bytes()), recursive_kernel_check=True,
        endpoint=ENDPOINT, normal_registration=False, coverage_added=0), indent=2) + '\n',
        HERE / 'beta-integration-kernel.log': log})
    print('Ordinary-module complete original beta jet recursively kernel-checked', flush=True)


def check():
    work, report = reported()
    r = json.loads((HERE / 'CHECKED.json').read_text())
    if (not r['recursive_kernel_check'] or r['kernel']['exit_code'] or r['kernel']['command'] != kernel_command() or
            r['reported_sha256'] != s.sha((HERE / 'REPORTED.json').read_bytes()) or
            r['kernel']['log_sha256'] != s.sha((HERE / 'beta-integration-kernel.log').read_bytes()) or
            (HERE / 'beta-integration-kernel.log').read_bytes() != (work / 'beta-integration-kernel.log').read_bytes()):
        raise ValueError('ordinary beta kernel evidence differs')
    s.kernel.kernel((HERE / 'beta-integration-kernel.log').read_text(),
        sorted((work / 'Coq/C/jet_coqchk_axioms.expected').read_text().split()))
    print('Exact ordinary beta integration source/build/report/kernel identities verified')


if __name__ == '__main__':
    if len(sys.argv) != 2 or sys.argv[1] not in {'reports', 'kernel', 'check'}:
        raise SystemExit('usage: verify.py reports|kernel|check')
    {'reports': reports, 'kernel': kernel, 'check': check}[sys.argv[1]]()
