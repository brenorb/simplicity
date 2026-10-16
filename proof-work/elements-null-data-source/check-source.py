"""Selected null-data source correspondence, not a proof or host-runtime checker.

The reviewed model pins complete active declarations/clauses, not fragments
which could also occur in comments or an unrelated theorem.
"""
import importlib.util
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent


def load(name, path):
    sp = importlib.util.spec_from_file_location(name, path)
    m = importlib.util.module_from_spec(sp)
    sp.loader.exec_module(m)
    return m


def extract(code, kind, name):
    if kind == 'declaration':
        pattern = r'\b(?:Definition|Fixpoint|Let|Inductive)\s+' + re.escape(name) + r"(?![\w']).*?\.\s*(?=\n|$)"
    elif kind == 'statement':
        pattern = r'\b(?:Lemma|Theorem)\s+' + re.escape(name) + r"(?![\w']).*?(?=\bProof\.)"
    else:
        raise ValueError('unknown declaration kind')
    found = re.findall(pattern, code, re.S)
    if len(found) != 1:
        raise ValueError('missing/ambiguous null-data declaration: ' + name)
    return found[0]


def between(code, start, stop):
    if code.count(start) != 1 or code.count(stop) != 1:
        raise ValueError('missing/ambiguous null-data source boundary: ' + start)
    return code.split(start, 1)[1].split(stop, 1)[0]


def check(repo):
    repo = Path(repo)
    coq = repo / 'Coq'
    shared = load('null_data_hash_source', HERE.parent / 'elements-hash-literal/check-source.py')
    result = shared.check(repo, coq, coq / 'C/jet_haskell_hash_word.v', coq / 'C/jet_elements_hash_literal.v')
    p = load('null_data_source_parser', coq / 'check-secp-predicates-specification.py')
    model = load('null_data_reviewed_source_model', HERE / 'source-model.py')
    paths = set()

    def read(name):
        path = repo / name
        paths.add(path)
        if path.suffix == '.c':
            return re.sub(r'/\*.*?\*/|//[^\n]*', ' ', path.read_text(), flags=re.S)
        return p.read_code(path)

    def equal(a, b, label):
        if p.compact(a) != p.compact(b):
            raise ValueError('null-data selected source differs: ' + label)

    for path, kind, name, expected in model.DECLARATIONS:
        equal(extract(read(path), kind, name), expected, path + ':' + name)
    for path, start, stop, expected in model.BLOCKS:
        equal(between(read(path), start, stop), expected, path + ':' + start)
    for path, start, expected in model.LINES:
        found = re.findall(r'(?m)^\s*' + re.escape(start) + r'\s*=([^\n]*)$', read(path))
        if len(found) != 1:
            raise ValueError('missing/ambiguous null-data source line: ' + start)
        equal(found[0], expected, start)
    for path, fragment in model.FRAGMENTS:
        p.require(read(path), fragment, 'null-data carrier/namespace: ' + path)
    # Do not accept a new local binding which shadows a reviewed Get primitive.
    data = read('Haskell/Elements/Simplicity/Elements/DataTypes.hs')
    for name in ['runGetLazy', 'getWord8', 'getWord16le', 'getWord32le', 'getLazyByteString', 'isEmpty']:
        if re.search(r'(?m)^\s*(?:let\s+)?' + name + r'\b[^\n]*=', data):
            raise ValueError('shadowed null-data parser primitive: ' + name)
    import hashlib
    result['source_sha256'].update({str(path): hashlib.sha256(path.read_bytes()).hexdigest() for path in sorted(paths)})
    result.update(selected_primitives=['Elements.OutputNullDatum'],
        canonical_null_data_source_review_complete=True, whole_contracts_reviewed=True,
        parser_relation_source_reviewed=True, encoded_constructors=22,
        caller_environment_construction_proved=False, formal_host_library_equivalence=False,
        normal_registration=False, coverage_added=0,
        domain='represented-separated Bit Machine frames; not arbitrary overlapping buffers')
    return result


if __name__ == '__main__':
    print(json.dumps(check(Path(sys.argv[1]).resolve()), indent=2))
