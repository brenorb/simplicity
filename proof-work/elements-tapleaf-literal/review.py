"""Validate the sealed byte-getter C-to-literal proof, without recompiling."""
import importlib.util
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
spec = importlib.util.spec_from_file_location('sealed_tapleaf_support', HERE.parent / 'elements-count/support.py')
support = importlib.util.module_from_spec(spec)
spec.loader.exec_module(support)


def review(record=None):
    if record is None:
        record = json.loads((HERE / 'REVIEW.json').read_text())
    work, base = Path(record['candidate']), Path(record['base_candidate'])
    coq, proof = work / 'Coq', work / 'Proof'
    source = proof / 'jet_elements_tapleaf_literal.v'
    prefix = 'TapleafReview.jet_elements_tapleaf_literal.'
    results = [prefix + n for n in ['elements_tapleaf_version_literal_matches', 'elements_tapleaf_version_literal_local_spec']]
    original = 'C.jet_elements_tapleaf_version_local.elements_tapleaf_version_local_spec'
    definitions = [prefix + 'elements_tapleaf_version_literal_spec',
                   'C.jet_elements_tapleaf_version_local.elements_tapleaf_version_spec',
                   'C.jet_elements_tapleaf_version_local.elements_tapleaf_version_env_rep',
                   'C.jet_application_sep.application_jet_local_spec_sep']
    if (record['namespace'] != 'TapleafReview' or record['results'] != results or record['original'] != original or
            record['definitions'] != definitions or record['normal_registration'] is not False or record['coverage_added'] != 0):
        raise ValueError('wrong tapleaf scope')
    if (source.read_bytes() != (HERE / 'source/jet_elements_tapleaf_literal.v.source').read_bytes() or
            support.sha(source.read_bytes()) != record['source_sha256']):
        raise ValueError('literal proof source/archive drift')
    support.safe_source(source.read_text(), str(source))
    if set(record['tools_sha256']) != {'finish.py', 'check-source.py', 'test-source.py'}:
        raise ValueError('missing tool bindings')
    for name, digest in record['tools_sha256'].items():
        if support.sha((HERE / name).read_bytes()) != digest:
            raise ValueError('checked tool drift')
    for name, digest in record['evidence_sha256'].items():
        path = work / name
        if path.parent not in [work, proof] or path.is_symlink() or support.sha(path.read_bytes()) != digest:
            raise ValueError('source/object/terminal evidence drift')
    required = {'Proof/jet_elements_tapleaf_literal.v', 'Proof/jet_elements_tapleaf_literal.vo',
                'Proof/contracts.v', 'Proof/assumptions.v', 'contracts.log', 'assumptions.log',
                'compile.log', 'kernel.log', 'source.log', 'source-tests.log', 'AST.log', 'regenerated.v'}
    if not required <= set(record['evidence_sha256']):
        raise ValueError('incomplete evidence inventory')
    if support.inputs.fingerprint(coq, REPO) != record['coq_input_sha256']:
        raise ValueError('checked dependency source drift')
    prior = json.loads((HERE.parent / 'elements-sequence-normal/PREPARATION.json').read_text())
    if str(base) != prior['candidate'] or support.inputs.fingerprint(base / 'Coq', REPO) != prior['candidate_input_sha256']:
        raise ValueError('wrong sealed source base')
    for module, digest in prior['objects_sha256'].items():
        path = coq / (module.replace('.', '/') + '.v')
        if support.sha(path.read_bytes()) != prior['sources_sha256'][module] or support.sha(path.with_suffix('.vo').read_bytes()) != digest:
            raise ValueError('sealed shared dependency changed')
    modules = record['fresh_modules']
    if set(modules) != set(record['fresh_source_sha256']) or set(modules) != set(record['fresh_object_sha256']):
        raise ValueError('incomplete fresh source/object binding')
    for module in modules:
        path = coq / (module.replace('.', '/') + '.v')
        if support.sha(path.read_bytes()) != record['fresh_source_sha256'][module] or support.sha(path.with_suffix('.vo').read_bytes()) != record['fresh_object_sha256'][module]:
            raise ValueError('fresh source/object drift')
    flags = ['-Q', str(proof), 'TapleafReview']
    def coqc(path):
        return ['bash', 'build-jets.sh', '--coqc', '-q'] + flags + [str(path)]
    commands = {m: ['bash', 'build-jets.sh', '--coqc', '-q', m.replace('.', '/') + '.v'] for m in modules}
    commands.update({'compile': coqc(source), 'contracts': coqc(proof / 'contracts.v'),
                     'assumptions': coqc(proof / 'assumptions.v'),
                     'kernel': ['bash', 'build-jets.sh', '--coqchk', '-silent', '-o'] + flags + ['TapleafReview.jet_elements_tapleaf_literal'],
                     'AST': ['bash', str(REPO / 'Coq/C/regenerate-elements-jets.sh'), str(work / 'regenerated.v')],
                     'source': [sys.executable, '-B', str(HERE / 'check-source.py'), '--repo', str(REPO), '--coq', str(coq), '--literal', str(source)],
                     'source-tests': [sys.executable, '-B', str(HERE / 'test-source.py'), str(REPO), str(coq), str(source)]})
    if set(commands) != set(record['commands']):
        raise ValueError('incomplete verification stages')
    for name, command in commands.items():
        row = record['commands'][name]
        if row['command'] != command or row['exit_code'] != 0 or row['log_sha256'] != support.sha((work / (name + '.log')).read_bytes()):
            raise ValueError('command/exit/terminal evidence mismatch')
    deps = support.reports.assumptions((work / 'assumptions.log').read_text())
    if (set(deps) != set(results + [original]) or {n: sorted(ds) for n, ds in deps.items()} != record['dependencies'] or
            any(not ds <= support.SIX for ds in deps.values()) or deps[results[-1]] != deps[original]):
        raise ValueError('new or unreviewed dependencies')
    contracts = (work / 'contracts.log').read_text()
    if ('...' in contracts or re.search(r'\?[A-Za-z]', contracts) or
            re.findall(r'(?m)^TAPLEAF_(TYPE|DEF) (\S+)$', contracts) !=
            [('TYPE', n) for n in results + [original]] + [('DEF', n) for n in definitions] or
            (HERE / 'contracts.log').read_text() != contracts or
            (HERE / 'assumptions.log').read_text() != (work / 'assumptions.log').read_text()):
        raise ValueError('incomplete/changed full reports')
    support.kernel.kernel((work / 'kernel.log').read_text(), sorted((base / 'Coq/C/jet_coqchk_axioms.expected').read_text().split()))
    if (work / 'regenerated.v').read_bytes() != (coq / 'C/jets_elements.v').read_bytes():
        raise ValueError('original C program drift')
    support.load('sealed_tapleaf_source', HERE / 'check-source.py').check(REPO, coq, source)
    print('TapleafVersion actual-C contract, shared width-8 conversion, source correspondence and kernel evidence validated')


if __name__ == '__main__':
    review()
