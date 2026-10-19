"""Freeze the scoped recursive port review; no snapshot-update mode.

Source comparison supplements formal Coq proofs, not formal Haskell translation.
Uncovered bit/arithmetic/type/encoding dependencies remain separate obligations.
"""
import argparse
import hashlib
import importlib.util
import json
import re
import sys
from pathlib import Path
from types import SimpleNamespace

sys.dont_write_bytecode = True


def parser(repo):
    spec = importlib.util.spec_from_file_location('active_source_parser',
        Path(repo)/'Coq/check-secp-predicates-specification.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def active(module, path, text):
    return module.read_code(SimpleNamespace(suffix=Path(path).suffix,
        read_text=lambda: text))


def declaration(code, name):
    matches = list(re.finditer(r'\b(?:Definition|Fixpoint)\s+'+re.escape(name)+
        r'\b.*?\.\s*(?:\n|$)', code, re.S))
    if len(matches) != 1:
        raise ValueError('missing or duplicate Coq declaration '+name)
    return matches[0][0]


def load(repo, directory):
    reviewed = Path(directory)/'recursive-ports-review.json'
    if hashlib.sha256(reviewed.read_bytes()).hexdigest() != '6627e8c702c954d8401f5d0a502e9c092f215eb51a9667340e0a2484ee5c30b7':
        raise ValueError('reviewed recursive source reference changed')
    reference = json.loads((Path(directory)/'recursive-ports-review.json').read_text())
    paths = {'Coq/'+r['path'] for r in reference['coq']}
    paths.update(r['path'] for r in reference['haskell'])
    sources = {p: (Path(repo)/p).read_text() for p in paths}
    return reference, sources


def check(module, reference, sources):
    code = {p: active(module, p, text) for p, text in sources.items()}
    for r in reference['coq']:
        if module.compact(declaration(code['Coq/'+r['path']], r['name'])) != module.compact(r['declaration']):
            raise ValueError('typed recursive Coq port changed '+r['name'])
    for r in reference['haskell']:
        text = code[r['path']]
        if text.count(r['start']) != 1 or (r['end'] is not None and text.count(r['end']) != 1):
            raise ValueError('missing/duplicate canonical implementation boundary')
        begin, end = text.index(r['start']), (len(text) if r['end'] is None else text.index(r['end']))
        if begin >= end or module.compact(text[begin:end]) != module.compact(r['text']):
            raise ValueError('canonical recursive implementation changed '+r['start'])
    return len(reference['coq']), len(reference['haskell'])


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--repo', required=True)
    p.add_argument('--candidates', required=True)
    args = p.parse_args()
    reference, sources = load(args.repo, args.candidates)
    print('Scoped recursive ports match:', check(parser(args.repo), reference, sources))
