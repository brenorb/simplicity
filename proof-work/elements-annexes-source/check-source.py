"""Canonical annex-loop source correspondence; not a host-library proof."""
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


stream = load('elements_annexes_inherited_source', HERE.parent / 'elements-stream-source/check-source.py')
compact, extract = stream.compact, stream.extract


def check(repo):
    repo = Path(repo)
    result = stream.check(repo)
    parser = load('elements_annexes_parser', repo / 'Coq/check-secp-predicates-specification.py')
    model = load('elements_annexes_fixed_model', HERE / 'source-model.py').MODEL
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
            raise ValueError('Elements annex-loop selected source differs: ' + label)

    def require(path, fragment):
        if compact(fragment) not in compact(read(path)):
            raise ValueError('Elements annex-loop binding/carrier differs: ' + path + ':' + fragment)

    def line(path, name, expected):
        found = re.findall(r'(?m)^\s*' + re.escape(name) + r'\s*=([^\n]*)$', read(path))
        if len(found) != 1:
            raise ValueError('missing/ambiguous Elements annex-loop clause: ' + name)
        equal(found[0], expected, path + ':' + name)

    for path, kind, name, expected in model['declarations']:
        equal(extract(read(path), kind, name), expected, path + ':' + name)
    for path, start, stop, expected in model['blocks']:
        code = read(path)
        if code.count(start) != 1 or code.count(stop) != 1:
            raise ValueError('missing/ambiguous annex-loop boundary: ' + start)
        equal(code.split(start, 1)[1].split(stop, 1)[0], expected, path + ':' + start)

    prim = 'Haskell/Elements/Simplicity/Elements/Primitive.hs'
    catalog = 'Haskell/Simplicity/Elements/Jets.hs'
    wrapper = 'Haskell/Simplicity/Elements/Programs/SigHash/Lib.hs'
    lib = 'Haskell/Core/Simplicity/Programs/Elements/Lib.hs'
    elements = 'Haskell/Core/Simplicity/Programs/Elements.hs'
    line(catalog, 'specificationSigHash InputAnnexesHash', 'SigHash.inputAnnexesHash')
    line(wrapper, 'inputAnnexesHash', 'SigHash.inputAnnexesHash SigHash.lib')
    require(catalog, 'InputAnnexesHash :: SigHashJet () Word256')
    line(prim, 'interpret InputAnnexHash',
         'return . (atInput $ cast . fmap (encodeHash . bslHash) . sigTxiAnnex)')
    line(prim, 'primName InputAnnexHash', '"inputAnnexHash"')
    require(prim, 'InputAnnexHash :: Prim Word32 (S (S Word256))')
    require('Coq/C/jet_elements_prim.v', '| InputAnnexHash : prim Word32 (S (S Word256))')
    line(lib, 'annexHash', 'Elements.annexHash Elements.libAssert')
    line(elements, 'libAssert', 'mkLibAssert Sha256.lib Sha256.libAssert LibSecp256k1.lib')
    line(elements, 'ctx8Add32', 'ctx8Addn vector32')
    require('Haskell/Simplicity/Elements/Programs/SigHash.hs', 'import Simplicity.Programs.Elements.Lib')
    require(lib, 'import qualified Simplicity.Programs.Elements as Elements')
    found = re.findall(r'\bbool\s+simplicity_input_annexes_hash\s*'
        r'\(frameItem\* dst, frameItem src, const txEnv\* env\)\s*\{([^{}]*)\}',
        read('C/elements/elementsJets.c'), re.S)
    if len(found) != 1:
        raise ValueError('missing/ambiguous original C annexes getter')
    equal(found[0], '(void) src; writeHash(dst, &env->tx->inputAnnexesHash); return true;', 'C getter')
    result['source_sha256'].update({str(path): hashlib.sha256(path.read_bytes()).hexdigest() for path in sorted(paths)})
    result.update(selected_jets=['Elements.InputAnnexesHash'], selected_primitives=['Elements.InputAnnexHash'],
        canonical_annex_loop_source_review_complete=True, original_c_getters=1,
        whole_contracts_reviewed=True, environment_generic_reader_proof=True,
        shared_bitcoin_annex_program_matches_elements=True, absent_and_empty_annex_distinct=True,
        caller_cached_hashes_established=False, formal_host_library_equivalence=False,
        kernel_checked_by_this_tool=False, normal_registration=False, coverage_added=0)
    return result


if __name__ == '__main__':
    print(json.dumps(check(Path(sys.argv[1]).resolve()), indent=2))
