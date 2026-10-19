"""Audit ordinary names without altering the checked scalar-lambda theorem.

Compare every new type, definition and dependency profile with the checked
private proof. Compilation, recursive checking and normal acceptance remain
distinct evidence; this packet does not register or accept any jet.
"""
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('lambda_ordinary_assembly', HERE / 'assemble.py')
a = importlib.util.module_from_spec(sp)
sp.loader.exec_module(a)
s, g = a.s, a.p.g
PREFIX = 'lambda-ordinary'
ENDPOINT = a.ROOTS[0] + '.scalar_lambda_initialized_local_spec_internal'


def built():
    work, prep = a.identity()
    b = json.loads((HERE / 'BUILT.json').read_text())
    if (not b['complete'] or not b['no_local_objects_copied'] or
            b['preparation_sha256'] != s.sha((HERE / 'PREPARATION.json').read_bytes()) or
            set(b['source_objects']) != set(prep['sources'])):
        raise ValueError('ordinary lambda dependency build is not complete for these inputs')
    for stem, row in b['commands'].items():
        if row['exit_code'] or row['log_sha256'] != s.sha((work / (stem + '.log')).read_bytes()):
            raise ValueError('ordinary lambda build command/log differs: ' + stem)
    for n, digest in b['source_objects'].items():
        if s.sha((work / n).with_suffix('.vo').read_bytes()) != digest:
            raise ValueError('ordinary lambda built object differs: ' + n)
    return work, prep, b


def parent_profiles():
    r = json.loads((a.p.HERE / 'RUN.json').read_text())
    profiles = {}
    for n, ds in r['dependencies'].items():
        module, short = n.rsplit('.', 1)
        profiles[a.MAPPING[module] + '.' + short] = set(ds)
    if len(profiles) != 19 or profiles[ENDPOINT] != s.SIX:
        raise ValueError('checked parent result/profile inventory differs')
    return profiles


def compare_contracts(work):
    aliases = {}
    for old, new in a.MAPPING.items():
        source = work / 'Coq' / (new.replace('.', '/') + '.v')
        rs, ds = g.declarations(source.read_text(), new)
        for name in rs + ds:
            short = name.rsplit('.', 1)[1]
            for module in [old, old.rsplit('.', 1)[1], new, new.removeprefix('C.')]:
                alias = module + '.' + short
                if alias in aliases and aliases[alias] != name:
                    raise ValueError('ambiguous ordinary lambda module alias: ' + alias)
                aliases[alias] = name
    def chunks(raw):
        parts = re.split(r'(?m)^TAP_(TYPE|DEF) (\S+)\n', raw)
        result = {}
        for kind, name, body in zip(parts[1::3], parts[2::3], parts[3::3]):
            if name not in aliases:
                raise ValueError('unreviewed ordinary/private declaration: ' + name)
            key = kind + ' ' + aliases[name]
            if key in result:
                raise ValueError('duplicate complete lambda contract: ' + key)
            body = re.sub(r'[A-Za-z_][\w\x27]*(?:\.[A-Za-z_][\w\x27]*)+',
                lambda m: aliases.get(m[0], m[0]), body)
            result[key] = re.sub(r'\s+', '', body)
        return result
    original = a.p.HERE / (a.p.PREFIX + '-contracts.log')
    expected = chunks(original.read_text())
    actual = chunks((work / (PREFIX + '-contracts.log')).read_text())
    if len(expected) != 20 or set(actual) != set(expected) or actual != expected:
        raise ValueError('ordinary lambda complete types/definitions changed beyond modules: ' +
            str([n for n in expected if expected[n] != actual.get(n)]))
    return dict(compared_theorem_types=19, compared_definitions=1, module_alias_only=True,
        original_report_sha256=s.sha(original.read_bytes()), normalized_sha256=s.sha(json.dumps(actual, sort_keys=True).encode()))


def kernel_command():
    return ['bash', '-c', 'ulimit -s 65520; exec bash build-jets.sh --coqchk -silent -o ' + ' '.join(a.ROOTS)]


def reports():
    work, prep, build = built()
    if (HERE / 'REPORT-LAUNCH.json').exists():
        raise ValueError('ordinary lambda report audit already launched; poll original process')
    before, index = s.input_map(), s.index_hash()
    driver = s.sha(Path(__file__).read_bytes())
    s.changed({HERE / 'REPORT-LAUNCH.json': json.dumps(dict(candidate=str(work), complete=False,
        built_sha256=s.sha((HERE / 'BUILT.json').read_bytes()), verifier_sha256=driver), indent=2) + '\n'})
    commands = {}
    modules = [(new, work / 'Coq' / (new.replace('.', '/') + '.v')) for new in a.MAPPING.values()]
    results, definitions, deps = g.reports(work, modules, PREFIX, commands)
    if deps != parent_profiles() or len(definitions) != 1:
        raise ValueError('ordinary lambda exact profiles/definition inventory differ')
    compared = compare_contracts(work)
    review = a.p.source_review(work)
    query = subprocess.run(['bash', 'build-jets.sh', '--coqtop', '-quiet'],
        input='Require ' + ' '.join(a.ROOTS) + '.\nPrint Libraries.\n', cwd=work / 'Coq', env=s.ENV,
        text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=60)
    libraries = set(re.findall(r'^\s+([A-Za-z_][\w]*(?:\.[\w]+)+)\s*$', query.stdout, re.M))
    loaded = {'Coq/' + n.replace('.', '/') + '.v' for n in libraries if n.startswith(('C.', 'Simplicity.', 'Util.'))}
    unknown = {n for n in libraries if not n.startswith(('C.', 'Simplicity.', 'Util.', 'Coq.', 'compcert.', 'Flocq.', 'VST.', 'sha.'))}
    if query.returncode or re.search(r'(?m)^(?:Error|Anomaly):', query.stdout) or unknown or loaded != set(prep['sources']):
        raise ValueError('ordinary lambda loaded closure or namespace differs: ' + str(loaded ^ set(prep['sources'])))
    for stem, command, deadline in [
            (PREFIX + '-original-targets', [sys.executable, '-B', 'check-jet-source-target.py'], 60),
            (PREFIX + '-ast', ['bash', 'C/check-secp-jets-generation.sh'], 180)]:
        commands[stem] = s.run(work, command, stem, deadline)
    built()
    if before != s.input_map() or index != s.index_hash() or driver != s.sha(Path(__file__).read_bytes()):
        raise ValueError('ordinary lambda main/staged/verifier inputs changed')
    record = dict(candidate=str(work), endpoint=ENDPOINT, roots=a.ROOTS, results=results, definitions=definitions,
        dependencies={n: sorted(ds) for n, ds in deps.items()}, commands=commands, source_review=review,
        exact_private_type_definition_comparison=compared, loaded_local_modules=sorted(loaded),
        built_sha256=s.sha((HERE / 'BUILT.json').read_bytes()), parent_checked_sha256=s.sha((a.p.HERE / 'CHECKED.json').read_bytes()),
        verifier_sha256=driver, main_inputs=before, staged_patch_sha256=index,
        recursive_kernel_check=False, whole_initialized_lambda_C_to_literal_spec=True, accepted=False, coverage_added=0)
    changes = {HERE / 'RUN.json': json.dumps(record, indent=2) + '\n', HERE / 'loaded-libraries.log': query.stdout}
    for stem in commands:
        changes[HERE / (stem + '.log')] = (work / (stem + '.log')).read_text()
    s.changed(changes)
    print('Ordinary lambda: 19 identical complete types, one identical definition, exact six-dependency endpoints', flush=True)


def bound():
    work, prep, build = built()
    r = json.loads((HERE / 'RUN.json').read_text())
    if (r['verifier_sha256'] != s.sha(Path(__file__).read_bytes()) or
            r['built_sha256'] != s.sha((HERE / 'BUILT.json').read_bytes()) or
            r['parent_checked_sha256'] != s.sha((a.p.HERE / 'CHECKED.json').read_bytes()) or
            r['main_inputs'] != s.input_map() or r['staged_patch_sha256'] != s.index_hash() or
            {n: set(ds) for n, ds in r['dependencies'].items()} != parent_profiles() or
            r['exact_private_type_definition_comparison'] != compare_contracts(work) or
            set(r['loaded_local_modules']) != set(prep['sources']) or r['source_review'] != a.p.source_review(work)):
        raise ValueError('ordinary lambda exact audited inputs differ')
    for stem, row in r['commands'].items():
        if (row['exit_code'] or row['log_sha256'] != s.sha((work / (stem + '.log')).read_bytes()) or
                (HERE / (stem + '.log')).read_bytes() != (work / (stem + '.log')).read_bytes()):
            raise ValueError('ordinary lambda audit command/log differs: ' + stem)
    return work, r


def kernel():
    work, r = bound()
    if (HERE / 'KERNEL-LAUNCH.json').exists():
        raise ValueError('ordinary lambda kernel already launched; poll original process')
    s.changed({HERE / 'KERNEL-LAUNCH.json': json.dumps(dict(complete=False, command=kernel_command(),
        run_sha256=s.sha((HERE / 'RUN.json').read_bytes())), indent=2) + '\n'})
    row = s.run(work, kernel_command(), PREFIX + '-kernel', 1800)
    log = (work / (PREFIX + '-kernel.log')).read_text()
    s.kernel.kernel(log, sorted((work / 'Coq/C/jet_coqchk_axioms.expected').read_text().split()))
    bound()
    s.changed({HERE / 'CHECKED.json': json.dumps(dict(recursive_kernel_check=True, kernel=row,
        run_sha256=s.sha((HERE / 'RUN.json').read_bytes()), accepted=False, coverage_added=0), indent=2) + '\n',
        HERE / (PREFIX + '-kernel.log'): log})
    print('Ordinary scalar-lambda public contract and actual-init witness recursively kernel-checked', flush=True)


def check():
    work, r = bound()
    k = json.loads((HERE / 'CHECKED.json').read_text())
    if (not k['recursive_kernel_check'] or k['kernel']['exit_code'] or k['kernel']['command'] != kernel_command() or
            k['run_sha256'] != s.sha((HERE / 'RUN.json').read_bytes()) or
            k['kernel']['log_sha256'] != s.sha((work / (PREFIX + '-kernel.log')).read_bytes()) or
            (HERE / (PREFIX + '-kernel.log')).read_bytes() != (work / (PREFIX + '-kernel.log')).read_bytes()):
        raise ValueError('ordinary lambda completed kernel evidence differs')
    print('Exact ordinary scalar-lambda sources, build, type/definition/profile comparisons and kernel receipt match')


if __name__ == '__main__':
    if len(sys.argv) != 2 or sys.argv[1] not in {'reports', 'kernel', 'check'}:
        raise SystemExit('usage: verify.py reports|kernel|check')
    {'reports': reports, 'kernel': kernel, 'check': check}[sys.argv[1]]()
