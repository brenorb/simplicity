"""Verify frozen helper evidence; never registers or accepts a public jet."""
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import sys
sys.dont_write_bytecode = True
ARCHIVE = Path(__file__).resolve().parent
REPO = ARCHIVE.parent.parent


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def assumptions(text, expected):
    records = {}
    current = None
    in_axioms = False
    for line in text.splitlines():
        if line.startswith('JET_ASSUMPTIONS '):
            current = line.split()[1]
            if current in records:
                raise ValueError('duplicate dependency record')
            records[current] = set()
            in_axioms = False
        elif line == 'Axioms:':
            in_axioms = True
        elif line == 'Closed under the global context':
            in_axioms = False
        elif in_axioms and line and not line[0].isspace():
            records[current].add(line.split()[0])
    if records != expected:
        raise ValueError('helper dependencies differ from reviewed sets')
    return records


def contracts(text, expected):
    if '...' in text:
        raise ValueError('truncated contract report')
    markers = re.findall(r'(?m)^MUL_(TYPE|DEF) (\S+)$', text)
    if markers != expected:
        raise ValueError('contract inventory missing/reordered/duplicated')


def kernel(text, expected):
    if 'CONTEXT SUMMARY' not in text:
        raise ValueError('missing kernel context')
    for flag in ['Constants/Inductives relying on type-in-type',
                 'Constants/Inductives relying on unsafe (co)fixpoints',
                 'Inductives whose positivity is assumed']:
        if '* ' + flag + ': <none>' not in text:
            raise ValueError('unsafe/incomplete kernel context')
    axioms = text.split('* Axioms:\n', 1)[1].split('* Constants/Inductives', 1)[0]
    if sorted(axioms.split()) != expected:
        raise ValueError('kernel axiom context changed')


def review():
    manifest = json.loads((ARCHIVE / 'manifest.json').read_text())
    receipt = json.loads((ARCHIVE / 'REVIEW.json').read_text())
    work = Path(manifest['scratch'])
    base = Path(manifest['dependency_coq'])
    results, definitions = [], []
    for entry in manifest['modules']:
        source = ARCHIVE / (entry['file'] + '.source')
        if digest(source) != entry['sha256'] or (work / entry['file']).read_bytes() != source.read_bytes():
            raise ValueError('archive/compiled source drift: ' + entry['file'])
        text = source.read_text()
        if re.findall(r'^(?:Lemma|Theorem)\s+(\w+)', text, re.M) != entry['results']:
            raise ValueError('result source inventory drift')
        if re.findall(r'^Definition\s+(\w+)', text, re.M) != entry['definitions']:
            raise ValueError('definition source inventory drift')
        results += [entry['module'] + '.' + n for n in entry['results']]
        definitions += [entry['module'] + '.' + n for n in entry['definitions']]
    if (len(results), len(definitions)) != (17, 19):
        raise ValueError('unexpected closure')
    for name, value in receipt['evidence_sha256'].items():
        if digest(work / name) != value:
            raise ValueError('evidence drift: ' + name)
    for name in ['umul128_assumptions.v', 'umul128_contracts.v']:
        if (ARCHIVE / (name + '.source')).read_bytes() != (work / name).read_bytes():
            raise ValueError('driver drift')
    for name in ['umul128_assumptions.err', 'umul128_contracts.err']:
        if (work / name).read_bytes():
            raise ValueError('compiler diagnostics')
    expected = {n: set(receipt['execution_dependencies']) if n in receipt['execution_results'] else set()
                for n in results}
    checked = assumptions((work / 'umul128_assumptions.out').read_text(), expected)
    contracts((work / 'umul128_contracts.out').read_text(),
              [('TYPE', n) for n in results] + [('DEF', n) for n in definitions])
    context = (base / 'C/jet_coqchk_axioms.expected').read_text().split()
    for evidence in receipt['kernel']:
        if evidence['exit_code'] != 0 or digest(work / evidence['log']) != evidence['sha256']:
            raise ValueError('kernel failure/evidence drift')
        kernel((work / evidence['log']).read_text(), sorted(context))
    if (any(e['exit_code'] != 0 for e in receipt['builds'])
            or receipt['assumptions_exit_code'] != 0 or receipt['contracts_exit_code'] != 0):
        raise ValueError('nonterminal/failed verification')
    spec = importlib.util.spec_from_file_location('audit_inputs', base / 'jet-audit-inputs.py')
    audit = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(audit)
    if audit.fingerprint(base, REPO) != manifest['dependency_fingerprint']:
        raise ValueError('dependency source fingerprint changed')
    return {'modules': 3, 'results': len(results), 'closed_results': sum(not x for x in checked.values()),
            'definitions': len(definitions), 'kernel_context_matches': len(context),
            'untruncated_types_definitions': True, 'exact_dependencies_match': True,
            'source_hashes_match': True, 'full_acceptance': False, 'checkout_coverage_added': 0}


if __name__ == '__main__':
    print(json.dumps(review(), indent=2))
