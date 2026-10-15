"""Independently inspect complete lbtc_asset source, types and terminal evidence."""
import importlib.util
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('lbtc_completed_check', HERE / 'check.py')
g = importlib.util.module_from_spec(sp)
sp.loader.exec_module(g)
s = g.s


def review():
    r = json.loads((HERE / 'PREPARATION.json').read_text())
    work, coq = Path(r['candidate']), Path(r['candidate']) / 'Coq'
    base_path, baseline, inherited = g.tree(work)
    if (r['base_candidate'] != baseline['review']['candidate'] or
        r['base_review_sha256'] != s.sha(base_path.read_bytes()) or
        r['base_input_sha256'] != baseline['candidate_input_sha256'] or
        r['new_sources'] != g.NEW or r['fresh_modules'] != g.MODULES or
        r['endpoint'] != g.ENDPOINT or r['closed_shared_lemmas'] != g.PURE or
        r['normal_registration'] is not False or r['coverage_added'] != 0 or r['full_acceptance'] is not False):
        raise ValueError('wrong proof/base/registration scope')
    if (s.inputs.fingerprint(coq, work) != r['candidate_input_sha256'] or
        s.input_map() != r['main_inputs'] or s.index_hash() != r['staged_patch_sha256']):
        raise ValueError('private/main/index drift')
    results, definitions = [], []
    for m in g.MODULES:
        path = coq / (m.replace('.', '/') + '.v')
        a, b = g.shared.declarations(path.read_text(), m)
        results += a
        definitions += b
        if path.with_suffix('.vo').is_symlink():
            raise ValueError('shared mutable compiler object')
    if ((len(results), len(definitions)) != (13, 12) or r['results'] != results or r['definitions'] != definitions or
        r['source_sha256'] != {m: s.sha((coq / (m.replace('.', '/') + '.v')).read_bytes()) for m in g.MODULES} or
        r['object_sha256'] != {m: s.sha((coq / (m.replace('.', '/') + '.vo')).read_bytes()) for m in g.MODULES}):
        raise ValueError('incomplete/changed source/object/declaration evidence')
    deps = s.reports.assumptions((work / 'lbtc-assumptions.log').read_text())
    if (set(deps) != set(results) or {n: sorted(ds) for n, ds in deps.items()} != r['dependencies'] or
        any(not ds <= s.SIX for ds in deps.values()) or any(deps[n] for n in g.PURE) or deps[g.ENDPOINT] != s.SIX):
        raise ValueError('unreviewed assumptions or nonclosed constant/byte bridge')
    text = (work / 'lbtc-contracts.log').read_text()
    if ('...' in text or re.search(r'\?[A-Za-z]', text) or
        re.findall(r'(?m)^TAP_(TYPE|DEF) (\S+)$', text) != [('TYPE', n) for n in results] + [('DEF', n) for n in definitions]):
        raise ValueError('incomplete full type/definition report')
    commands = {m: ['bash', 'build-jets.sh', '--coqc', '-q', m.replace('.', '/') + '.v'] for m in g.MODULES}
    for stem in ['lbtc-assumptions', 'lbtc-contracts']:
        commands[stem] = ['bash', 'build-jets.sh', '--coqc', '-q', str(work / (stem.replace('-', '_') + '.v'))]
    commands.update(source=[sys.executable, '-B', str(HERE / 'check-source.py'), str(work)],
        **{'source-negative': [sys.executable, '-B', str(HERE / 'test-source.py'), str(work)],
           'ast': ['bash', 'C/check-elements-jets-generation.sh'],
           'kernel': ['bash', 'build-jets.sh', '--coqchk', '-silent', '-o', *g.MODULES]})
    if set(r['commands']) != set(commands):
        raise ValueError('missing checker/compiler stage')
    for name, command in commands.items():
        row = r['commands'][name]
        if row['command'] != command or row['exit_code'] != 0 or row['log_sha256'] != s.sha((work / (name + '.log')).read_bytes()):
            raise ValueError('changed command/flags/exit/log')
    if r['tools_sha256'] != {n: s.sha((HERE / n).read_bytes()) for n in ['check.py', 'check-source.py', 'test-source.py']}:
        raise ValueError('checked tool drift')
    for name in ['lbtc-assumptions', 'lbtc-contracts', 'source', 'source-negative', 'ast', 'kernel']:
        if (HERE / (name + '.log')).read_bytes() != (work / (name + '.log')).read_bytes():
            raise ValueError('archived evidence differs')
    s.kernel.kernel((work / 'kernel.log').read_text(), sorted((coq / 'C/jet_coqchk_axioms.expected').read_text().split()))
    gate = s.load('lbtc_review_source', HERE / 'check-source.py')
    gate.check(work)
    return dict(candidate=str(work), candidate_input_sha256=r['candidate_input_sha256'], jets_checked=1,
        fresh_modules=3, result_types=13, definitions=12, inherited_sources_byte_identical=len(inherited),
        closed_constant_and_byte_lemmas=4, environment_or_global_value_premise=False,
        complete_call_output_prefix_cursor_framing=True, normal_registration=False,
        coverage_added=0, full_acceptance=False)


if __name__ == '__main__':
    result = review()
    s.changed({HERE / 'REVIEW.json': json.dumps(result, indent=2) + '\n'})
    print(json.dumps(result, indent=2))
