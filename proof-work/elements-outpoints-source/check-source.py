"""Canonical Elements pegin/outpoint loop, primitive, word and C fidelity."""
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


annex = load('elements_outpoints_annex_source', HERE.parent / 'elements-annexes-source/check-source.py')
compact, extract = annex.compact, annex.extract


def check(repo):
    repo = Path(repo)
    result = annex.check(repo)
    parser = load('elements_outpoints_parser', repo / 'Coq/check-secp-predicates-specification.py')
    model = load('elements_outpoints_fixed_model', HERE / 'source-model.py').MODEL
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
            raise ValueError('Elements outpoints selected source differs: ' + label)

    def require(path, fragment):
        if compact(fragment) not in compact(read(path)):
            raise ValueError('Elements outpoints binding/carrier differs: ' + path + ':' + fragment)

    def line(path, name, expected):
        found = re.findall(r'(?m)^\s*' + re.escape(name) + r'\s*=([^\n]*)$', read(path))
        if len(found) != 1:
            raise ValueError('missing/ambiguous Elements outpoints clause: ' + name)
        equal(found[0], expected, path + ':' + name)

    for path, kind, name, expected in model['declarations']:
        equal(extract(read(path), kind, name), expected, path + ':' + name)
    for path, start, stop, expected in model['blocks']:
        code = read(path)
        if code.count(start) != 1 or code.count(stop) != 1:
            raise ValueError('missing/ambiguous Elements outpoints block: ' + start)
        equal(code.split(start, 1)[1].split(stop, 1)[0], expected, path + ':' + start)

    catalog = 'Haskell/Simplicity/Elements/Jets.hs'
    wrapper = 'Haskell/Simplicity/Elements/Programs/SigHash/Lib.hs'
    prim = 'Haskell/Elements/Simplicity/Elements/Primitive.hs'
    elements = 'Haskell/Core/Simplicity/Programs/Elements.hs'
    for path, name, expected in [
        (catalog, 'specificationSigHash InputOutpointsHash', 'SigHash.inputOutpointsHash'),
        (wrapper, 'inputOutpointsHash', 'SigHash.inputOutpointsHash SigHash.lib'),
        (prim, 'primName InputPegin', '"inputPegin"'),
        (prim, 'primName InputPrevOutpoint', '"inputPrevOutpoint"'),
        (prim, 'interpret InputPegin', 'return . (atInput $ cast . fmap encodeHash . sigTxiPegin)'),
        (prim, 'interpret InputPrevOutpoint', 'return . (atInput $ encodeOutpoint . sigTxiPreviousOutpoint)'),
        (prim, 'encodeOutpoint op', '(encodeHash $ opHash op, toWord32 . fromIntegral $ opIndex op)'),
        ('Haskell/Core/Simplicity/Programs/Elements/Lib.hs', 'outpointHash', 'Elements.outpointHash Elements.libAssert'),
        (elements, 'ctx8Add4', 'ctx8Addn vector4'),
    ]:
        line(path, name, expected)
    for path, fragment in [
        (catalog, 'InputOutpointsHash :: SigHashJet () Word256'),
        (prim, 'InputPegin :: Prim Word32 (S (S Word256))'),
        (prim, 'InputPrevOutpoint :: Prim Word32 (S (Word256,Word32))'),
        ('Haskell/Bitcoin/Simplicity/Bitcoin/DataTypes.hs', ', opIndex :: Word32'),
        ('Coq/C/jet_elements_prim.v', '| InputPegin : prim Word32 (S (S Word256))'),
        ('Coq/C/jet_elements_prim.v', '| InputPrevOutpoint : prim Word32 (S (Prod Word256 Word32))'),
    ]:
        require(path, fragment)
    c = read('C/elements/elementsJets.c')
    found = re.findall(r'\bbool\s+simplicity_input_outpoints_hash\s*'
        r'\(frameItem\* dst, frameItem src, const txEnv\* env\)\s*\{([^{}]*)\}', c, re.S)
    if len(found) != 1:
        raise ValueError('missing/ambiguous complete original Elements outpoints getter')
    equal(found[0], '(void) src; writeHash(dst, &env->tx->inputOutpointsHash); return true;', 'C getter')
    result['source_sha256'].update({str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(paths)})
    result.update(selected_jets=['Elements.InputOutpointsHash'],
        selected_primitives=['Elements.InputPegin', 'Elements.InputPrevOutpoint'],
        canonical_outpoints_source_review_complete=True, literal_two_primitive_body_reviewed=True,
        generic_body_bridge_source_reviewed=True, whole_contracts_reviewed=True, original_c_getters=1,
        caller_cached_hashes_established=False, formal_host_library_equivalence=False,
        kernel_checked_by_this_tool=False, normal_registration=False, coverage_added=0)
    return result


if __name__ == '__main__':
    print(json.dumps(check(Path(sys.argv[1]).resolve()), indent=2))
