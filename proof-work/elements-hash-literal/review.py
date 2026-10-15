"""Read-only verification of the literal digest bridge and both C contracts."""
import importlib.util
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
spec = importlib.util.spec_from_file_location('sealed_hash_support', HERE.parent / 'elements-count/support.py')
support = importlib.util.module_from_spec(spec)
spec.loader.exec_module(support)


def review(record=None):
    if record is None:
        record = json.loads((HERE / 'REVIEW.json').read_text())
    work, base = Path(record['candidate']), Path(record['base_candidate'])
    coq, proof = work / 'Coq', work / 'Proof'
    modules = ['jet_haskell_hash_word', 'jet_elements_hash_literal']
    old_modules = ['jet_elements_script_cmr_local', 'jet_elements_genesis_hash_local']
    originals = ['C.jet_elements_script_cmr_local.elements_script_cmr_local_spec',
                 'C.jet_elements_genesis_hash_local.elements_genesis_block_hash_local_spec']
    if (record['namespace'] != 'HashLiteral' or record['modules'] != modules or record['original_modules'] != old_modules or
            record['originals'] != originals or record['normal_registration'] is not False or record['coverage_added'] != 0):
        raise ValueError('wrong hash getter proof scope')
    results, definitions, pure = [], [], []
    for module in modules:
        path = proof / (module + '.v')
        code = support.safe_source(path.read_text(), str(path))
        if (path.read_bytes() != (HERE / 'source' / (module + '.v.source')).read_bytes() or
                support.sha(path.read_bytes()) != record['source_sha256'][module]):
            raise ValueError('proof/archive drift')
        names = ['HashLiteral.' + module + '.' + n for n in re.findall(r'^(?:Lemma|Theorem)\s+(\w+)', code, re.M)]
        results += names
        if module == modules[0]:
            pure = names
        definitions += ['HashLiteral.' + module + '.' + n for n in re.findall(r'^(?:Definition|Fixpoint|Record)\s+(\w+)', code, re.M)]
    definitions += ['C.jet_elements_script_cmr_local.elements_script_cmr_env_rep',
                    'C.jet_elements_genesis_hash_local.elements_genesis_hash_env_rep',
                    'C.jet_elements_script_cmr_local.elements_script_cmr_spec',
                    'C.jet_elements_genesis_hash_local.elements_genesis_hash_spec',
                    'C.jet_application_sep.application_jet_local_spec_sep']
    if record['results'] != results or record['pure_results'] != pure or record['definitions'] != definitions:
        raise ValueError('incomplete result/definition inventory')
    if set(record['tools_sha256']) != {'finish.py', 'check-source.py', 'test-source.py'}:
        raise ValueError('missing tool binding')
    for name, digest in record['tools_sha256'].items():
        if support.sha((HERE / name).read_bytes()) != digest:
            raise ValueError('checked tool drift')
    for name, digest in record['evidence_sha256'].items():
        path = work / name
        if path.parent not in [work, proof] or path.is_symlink() or support.sha(path.read_bytes()) != digest:
            raise ValueError('source/object/terminal evidence drift')
    required = {'Proof/' + m + suffix for m in modules for suffix in ['.v', '.vo']}
    required |= {'Proof/contracts.v', 'Proof/assumptions.v', 'contracts.log', 'assumptions.log',
                 'kernel.log', 'source.log', 'source-tests.log', 'AST.log', 'regenerated.v'}
    if not required <= set(record['evidence_sha256']):
        raise ValueError('missing proof/object/terminal evidence')
    if support.inputs.fingerprint(coq, REPO) != record['coq_input_sha256']:
        raise ValueError('checked source drift')
    prior = json.loads((HERE.parent / 'elements-tapleaf-literal/REVIEW.json').read_text())
    if str(base) != prior['candidate']:
        raise ValueError('wrong source dependency base')
    for receipt, skey, okey in [(prior, 'fresh_source_sha256', 'fresh_object_sha256'),
                               (json.loads((HERE.parent / 'elements-sequence-normal/PREPARATION.json').read_text()),
                                'sources_sha256', 'objects_sha256')]:
        for module, digest in receipt[okey].items():
            path = coq / (module.replace('.', '/') + '.v')
            if support.sha(path.read_bytes()) != receipt[skey][module] or support.sha(path.with_suffix('.vo').read_bytes()) != digest:
                raise ValueError('sealed shared dependency drift')
    flags = ['-Q', str(proof), 'HashLiteral']
    def coqc(path):
        return ['bash', 'build-jets.sh', '--coqc', '-q'] + flags + [str(path)]
    commands = {m: coqc(Path('C') / (m + '.v')) for m in old_modules}
    commands.update({m: coqc(proof / (m + '.v')) for m in modules})
    commands.update({n: coqc(proof / (n + '.v')) for n in ['assumptions', 'contracts']})
    commands.update({'kernel': ['bash', 'build-jets.sh', '--coqchk', '-silent', '-o'] + flags + ['HashLiteral.jet_elements_hash_literal'],
                     'AST': ['bash', str(REPO / 'Coq/C/regenerate-elements-jets.sh'), str(work / 'regenerated.v')],
                     'source': [sys.executable, '-B', str(HERE / 'check-source.py'), '--repo', str(REPO), '--coq', str(coq),
                         '--helper', str(proof / (modules[0] + '.v')), '--endpoint', str(proof / (modules[1] + '.v'))],
                     'source-tests': [sys.executable, '-B', str(HERE / 'test-source.py'), str(REPO), str(coq),
                         str(proof / (modules[0] + '.v')), str(proof / (modules[1] + '.v'))]})
    if set(commands) != set(record['commands']):
        raise ValueError('missing compiler/checker stage')
    for name, command in commands.items():
        row = record['commands'][name]
        if row['command'] != command or row['exit_code'] != 0 or row['log_sha256'] != support.sha((work / (name + '.log')).read_bytes()):
            raise ValueError('command/exit/log mismatch')
    for module in old_modules:
        path = coq / 'C' / (module + '.v')
        if support.sha(path.read_bytes()) != record['original_source_sha256'][module] or support.sha(path.with_suffix('.vo').read_bytes()) != record['original_object_sha256'][module]:
            raise ValueError('fresh original-C proof drift')
    deps = support.reports.assumptions((work / 'assumptions.log').read_text())
    if (set(deps) != set(results + originals) or {n: sorted(ds) for n, ds in deps.items()} != record['dependencies'] or
            any(not ds <= support.SIX for ds in deps.values()) or any(deps[n] for n in pure) or
            any(deps[n] != deps[o] for n, o in zip(results[-2:], originals))):
        raise ValueError('new/unreviewed assumptions')
    report = (work / 'contracts.log').read_text()
    if ('...' in report or re.search(r'\?[A-Za-z]', report) or
            re.findall(r'(?m)^HASH_LITERAL_(TYPE|DEF) (\S+)$', report) !=
            [('TYPE', n) for n in results + originals] + [('DEF', n) for n in definitions] or
            (HERE / 'contracts.log').read_text() != report or
            (HERE / 'assumptions.log').read_text() != (work / 'assumptions.log').read_text()):
        raise ValueError('incomplete/altered full reports')
    support.kernel.kernel((work / 'kernel.log').read_text(), sorted((coq / 'C/jet_coqchk_axioms.expected').read_text().split()))
    if (work / 'regenerated.v').read_bytes() != (coq / 'C/jets_elements.v').read_bytes():
        raise ValueError('production AST differs')
    support.load('sealed_hash_source', HERE / 'check-source.py').check(REPO, coq, proof / (modules[0] + '.v'), proof / (modules[1] + '.v'))
    print(str(len(pure)) + ' closed digest lemmas and both full original-C getter contracts validated; normal admission remains pending')


if __name__ == '__main__':
    review()
