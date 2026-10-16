"""Canonical Elements inputsHash composition, three component programs and C."""
import hashlib
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


outpoints = load('elements_inputs_component_source', HERE.parent / 'elements-outpoints-source/check-source.py')
compact, extract = outpoints.compact, outpoints.extract


def check(repo):
    repo = Path(repo)
    result = outpoints.check(repo)
    parser = load('elements_inputs_parser', repo / 'Coq/check-secp-predicates-specification.py')
    model = load('elements_inputs_fixed_model', HERE / 'source-model.py').MODEL
    paths, cache = set(), {}

    def read(name):
        path = repo / name
        paths.add(path)
        if path not in cache:
            cache[path] = (re.sub(r'/\*.*?\*/|//[^\n]*', ' ', path.read_text(), flags=re.S)
                           if path.suffix == '.c' else parser.read_code(path))
        return cache[path]

    def equal(actual, expected, label):
        if compact(actual) != compact(expected):
            raise ValueError('Elements inputs selected source differs: ' + label)

    def line(path, name, expected):
        found = re.findall(r'(?m)^\s*' + re.escape(name) + r'\s*=([^\n]*)$', read(path))
        if len(found) != 1:
            raise ValueError('missing/ambiguous Elements inputs clause: ' + name)
        equal(found[0], expected, path + ':' + name)

    for path, kind, name, expected in model['declarations']:
        equal(extract(read(path), kind, name), expected, path + ':' + name)
    for path, start, stop, expected in model['blocks']:
        code = read(path)
        if code.count(start) != 1 or code.count(stop) != 1:
            raise ValueError('missing/ambiguous Elements inputs composition block')
        equal(code.split(start, 1)[1].split(stop, 1)[0], expected, path + ':' + start)
    catalog = 'Haskell/Simplicity/Elements/Jets.hs'
    wrapper = 'Haskell/Simplicity/Elements/Programs/SigHash/Lib.hs'
    line(catalog, 'specificationSigHash InputsHash', 'SigHash.inputsHash')
    line(wrapper, 'inputsHash', 'SigHash.inputsHash SigHash.lib')
    if compact('InputsHash :: SigHashJet () Word256') not in compact(read(catalog)):
        raise ValueError('Elements inputs catalog type differs')
    c = read('C/elements/elementsJets.c')
    found = re.findall(r'\bbool\s+simplicity_inputs_hash\s*'
        r'\(frameItem\* dst, frameItem src, const txEnv\* env\)\s*\{([^{}]*)\}', c, re.S)
    if len(found) != 1:
        raise ValueError('missing/ambiguous complete original Elements inputs getter')
    equal(found[0], '(void) src; writeHash(dst, &env->tx->inputsHash); return true;', 'C getter')
    result['source_sha256'].update({str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(paths)})
    result.update(selected_jets=['Elements.InputsHash'],
        selected_primitives=['Elements.InputPegin', 'Elements.InputPrevOutpoint',
                             'Elements.InputSequence', 'Elements.InputAnnexHash'],
        canonical_inputs_source_review_complete=True, literal_composite_program_reviewed=True,
        component_program_sources_reviewed=True, whole_contracts_reviewed=True, original_c_getters=1,
        caller_cached_hashes_established=False, formal_host_library_equivalence=False,
        kernel_checked_by_this_tool=False, normal_registration=False, coverage_added=0)
    return result


if __name__ == '__main__':
    print(json.dumps(check(Path(sys.argv[1]).resolve()), indent=2))
