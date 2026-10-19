"""Audit the freshly built ordinary square closure and compare exact reports."""
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('square_ordinary_assembly', HERE / 'assemble.py')
a = importlib.util.module_from_spec(sp)
sp.loader.exec_module(a)
s = a.s
reporter = s.load('square_ordinary_report_queries', HERE.parent / 'secp-field-integration/verify.py')
square_source = s.load('square_original_authority', HERE.parent / 'secp-square-execution/verify.py')
ENDPOINT = a.ROOT + '.fe_square_local_spec'
REPORT_PATHS = [
    'proof-work/secp-square-execution/square-audit-contracts.log',
    'proof-work/secp-square-values/square-values-contracts.log',
    'proof-work/secp-square-caller/square-caller-contracts.log',
    'proof-work/secp-square-public/square-public-contracts.log',
]
PROFILE_PATHS = [
    'proof-work/secp-square-execution/RUN.json',
    'proof-work/secp-square-values/RUN.json',
    'proof-work/secp-square-caller/CHECKED.json',
    'proof-work/secp-square-public/RUN.json',
]


def built():
    work, prep = a.identity()
    r = json.loads((HERE / 'BUILT.json').read_text())
    if not r['complete'] or not r['no_local_objects_copied'] or r['preparation_sha256'] != s.sha((HERE / 'PREPARATION.json').read_bytes()):
        raise ValueError('ordinary square build is not complete for these inputs')
    if set(r['source_objects']) != set(prep['sources']):
        raise ValueError('ordinary square built source/object inventory differs')
    for stem, row in r['commands'].items():
        if row['exit_code'] or row['log_sha256'] != s.sha((work / (stem + '.log')).read_bytes()):
            raise ValueError('ordinary square build command/log differs: ' + stem)
    for name, digest in r['source_objects'].items():
        if s.sha((work / name).with_suffix('.vo').read_bytes()) != digest:
            raise ValueError('ordinary square built object differs: ' + name)
    return work, prep, r


def inherited_profiles():
    profiles, inputs = {}, {}
    for path in PROFILE_PATHS:
        raw = a.blob(path)
        inputs[path] = s.sha(raw)
        for name, ds in json.loads(raw)['dependencies'].items():
            module, short = name.rsplit('.', 1)
            if module not in a.MAPPING:
                raise ValueError('unexpected original square report module: ' + module)
            normal = a.MAPPING[module] + '.' + short
            if normal in profiles:
                raise ValueError('duplicate original square result: ' + normal)
            profiles[normal] = set(ds)
    if len(profiles) != 90 or profiles[ENDPOINT] != s.SIX:
        raise ValueError('missing original square result/profile')
    return profiles, inputs


def compare_contracts(work, prep):
    aliases = {}
    for name, row in prep['sources'].items():
        if not row['renamed']:
            continue
        normal = name.removeprefix('Coq/').removesuffix('.v').replace('/', '.')
        old = row['original_module']
        rs, ds = reporter.g.declarations((work / name).read_text(), normal)
        for declaration in rs + ds:
            short = declaration.rsplit('.', 1)[1]
            for module in [old, old.rsplit('.', 1)[-1], normal, normal.rsplit('.', 1)[-1]]:
                alias = module + '.' + short
                if alias in aliases and aliases[alias] != declaration:
                    raise ValueError('ambiguous square printed module alias: ' + alias)
                aliases[alias] = declaration

    def chunks(raw):
        pieces = re.split(r'(?m)^TAP_(TYPE|DEF) (\S+)\n', raw)
        result = {}
        for kind, name, body in zip(pieces[1::3], pieces[2::3], pieces[3::3]):
            if name not in aliases:
                continue
            key = kind + ' ' + aliases[name]
            body = re.sub(r'[A-Za-z_][\w\x27]*(?:\.[A-Za-z_][\w\x27]*)+',
                lambda match: aliases.get(match[0], match[0]), body)
            if key in result:
                raise ValueError('duplicate square full report entry: ' + key)
            result[key] = re.sub(r'\s+', '', body)
        return result

    expected, inputs = {}, {}
    for path in REPORT_PATHS:
        raw = a.blob(path)
        inputs[path] = s.sha(raw)
        for key, value in chunks(raw.decode()).items():
            if key in expected:
                raise ValueError('duplicate original square full report: ' + key)
            expected[key] = value
    actual = chunks((work / 'integration-contracts.log').read_text())
    if len(expected) != 145 or set(actual) != set(expected):
        raise ValueError('missing original/ordinary square complete type or definition')
    differences = [key for key in expected if expected[key] != actual[key]]
    if differences:
        raise ValueError('square types/definitions changed beyond module naming: ' + str(differences))
    return dict(original_report_inputs=inputs, compared_theorem_types=90, compared_definitions=55,
        module_alias_only=True, normalized_sha256=s.sha(json.dumps(actual, sort_keys=True).encode()))


def source_review(work):
    authority = square_source.source_review()
    for name, digest in authority.items():
        if s.sha((work / name).read_bytes()) != digest:
            raise ValueError('ordinary square canonical source differs: ' + name)
    texts = {n: (work / 'Coq' / (a.MAPPING['SquarePublic.' + n].replace('.', '/') + '.v')).read_text()
        for n in a.p.NAMES}
    a.p.review_source(texts)
    mutations = a.p.source_tests(texts)
    return dict(authority_inputs=authority, ordinary_contract_mutations_rejected=mutations,
        exact_reversible_proof_renaming=True)


def reports():
    work, prep, build = built()
    if (HERE / 'REPORT-LAUNCH.json').exists():
        raise ValueError('ordinary square reports already launched; poll original process')
    expected, inputs = inherited_profiles()
    modules = [(new, work / 'Coq' / (new.replace('.', '/') + '.v')) for new in a.MAPPING.values()]
    results_wanted = {name for module, path in modules for name in reporter.g.declarations(path.read_text(), module)[0]}
    if results_wanted != set(expected):
        raise ValueError('ordinary square result inventory differs from checked originals')
    s.changed({HERE / 'REPORT-LAUNCH.json': json.dumps(dict(candidate=str(work), complete=False,
        built_sha256=s.sha((HERE / 'BUILT.json').read_bytes()), verifier_sha256=s.sha(Path(__file__).read_bytes()),
        whole_report_deadline_seconds=600), indent=2) + '\n'})
    commands = {}
    results, definitions, deps = reporter.full_reports(work, modules, commands)
    if deps != expected or len(definitions) != 55:
        raise ValueError('ordinary square exact assumption profiles or definitions differ')
    compared = compare_contracts(work, prep)
    query = subprocess.run(['bash', 'build-jets.sh', '--coqtop', '-quiet'],
        input='Require ' + a.ROOT + '.\nPrint Libraries.\n', cwd=work / 'Coq', env=s.ENV,
        text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=60)
    loaded = set(re.findall(r'^\s+((?:C|Simplicity|Util)\.[\w.]+)\s*$', query.stdout, re.M))
    wanted = {name.removeprefix('Coq/').removesuffix('.v').replace('/', '.') for name in prep['sources']}
    if (query.returncode or re.search(r'(?m)^(?:Error|Anomaly):', query.stdout) or loaded != wanted or
            any(n in query.stdout for n in a.MAPPING)):
        raise ValueError('ordinary square loaded closure/private namespace differs: ' + str(loaded ^ wanted))
    for stem, command, deadline in [
            ('square-integration-original-targets', [sys.executable, '-B', 'check-jet-source-target.py'], 60),
            ('square-integration-ast', ['bash', 'C/check-secp-jets-generation.sh'], 180)]:
        commands[stem] = s.run(work, command, stem, deadline)
    review = source_review(work)
    built()
    r = dict(candidate=str(work), built_sha256=s.sha((HERE / 'BUILT.json').read_bytes()),
        verifier_sha256=s.sha(Path(__file__).read_bytes()), report_helper_sha256=s.sha(Path(reporter.__file__).read_bytes()),
        inherited_profile_inputs=inputs, results=results, definitions=definitions,
        dependencies={n: sorted(ds) for n, ds in deps.items()}, commands=commands, loaded_source_modules=sorted(loaded),
        endpoint=ENDPOINT, source_review=review, exact_original_type_definition_comparison=compared,
        normal_registration=False, coverage_added=0, recursive_kernel_check=False)
    changes = {HERE / 'REPORTED.json': json.dumps(r, indent=2) + '\n', HERE / 'loaded-libraries.log': query.stdout}
    for stem in ['integration-assumptions', 'integration-contracts', 'square-integration-original-targets', 'square-integration-ast']:
        changes[HERE / (stem + '.log')] = (work / (stem + '.log')).read_text()
    s.changed(changes)
    print('Ordinary square: 90 unchanged result types/profiles, 55 definitions, 239 fresh source-built modules; original AST regenerated', flush=True)


def reported():
    work, prep, build = built()
    r = json.loads((HERE / 'REPORTED.json').read_text())
    expected, inputs = inherited_profiles()
    if (r['built_sha256'] != s.sha((HERE / 'BUILT.json').read_bytes()) or
            r['verifier_sha256'] != s.sha(Path(__file__).read_bytes()) or
            r['report_helper_sha256'] != s.sha(Path(reporter.__file__).read_bytes()) or
            r['inherited_profile_inputs'] != inputs or r['source_review'] != source_review(work) or
            r['exact_original_type_definition_comparison'] != compare_contracts(work, prep) or
            {n: set(ds) for n, ds in r['dependencies'].items()} != expected):
        raise ValueError('ordinary square report identities differ')
    for stem, row in r['commands'].items():
        if (row['exit_code'] or row['log_sha256'] != s.sha((work / (stem + '.log')).read_bytes()) or
                (HERE / (stem + '.log')).read_bytes() != (work / (stem + '.log')).read_bytes()):
            raise ValueError('ordinary square completed report log differs: ' + stem)
    return work, r


def kernel_command():
    return ['bash', '-c', 'ulimit -s 65520; exec bash build-jets.sh --coqchk -silent -o ' + a.ROOT]


def kernel():
    work, report = reported()
    if (HERE / 'KERNEL-LAUNCH.json').exists():
        raise ValueError('ordinary square kernel already launched; poll original process')
    s.changed({HERE / 'KERNEL-LAUNCH.json': json.dumps(dict(candidate=str(work), command=kernel_command(), complete=False,
        reported_sha256=s.sha((HERE / 'REPORTED.json').read_bytes())), indent=2) + '\n'})
    row = s.run(work, kernel_command(), 'square-integration-kernel', 1200)
    log = (work / 'square-integration-kernel.log').read_text()
    s.kernel.kernel(log, sorted((work / 'Coq/C/jet_coqchk_axioms.expected').read_text().split()))
    reported()
    s.changed({HERE / 'CHECKED.json': json.dumps(dict(candidate=str(work), kernel=row,
        reported_sha256=s.sha((HERE / 'REPORTED.json').read_bytes()), recursive_kernel_check=True,
        endpoint=ENDPOINT, normal_registration=False, coverage_added=0), indent=2) + '\n',
        HERE / 'square-integration-kernel.log': log})
    print('Ordinary-module complete original square jet recursively kernel-checked', flush=True)


def check():
    work, _ = reported()
    r = json.loads((HERE / 'CHECKED.json').read_text())
    if (not r['recursive_kernel_check'] or r['kernel']['exit_code'] or r['kernel']['command'] != kernel_command() or
            r['reported_sha256'] != s.sha((HERE / 'REPORTED.json').read_bytes()) or
            r['kernel']['log_sha256'] != s.sha((HERE / 'square-integration-kernel.log').read_bytes()) or
            (HERE / 'square-integration-kernel.log').read_bytes() != (work / 'square-integration-kernel.log').read_bytes()):
        raise ValueError('ordinary square completed kernel evidence differs')
    s.kernel.kernel((HERE / 'square-integration-kernel.log').read_text(),
        sorted((work / 'Coq/C/jet_coqchk_axioms.expected').read_text().split()))
    print('Exact ordinary square integration source/build/report/kernel inputs verified')


if __name__ == '__main__':
    if len(sys.argv) != 2 or sys.argv[1] not in {'reports', 'kernel', 'check'}:
        raise SystemExit('usage: verify.py reports|kernel|check')
    {'reports': reports, 'kernel': kernel, 'check': check}[sys.argv[1]]()
