"""Canonical lbtcAsset constant, endian path and whole original-C contract.

This is a selected source correspondence guard, not a formal Haskell compiler
or a proof of the external lens/serialization implementations.
"""
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
CONSTANT = '0x6f0279e9ed041c3d710a9f57d0c02928416460c4b722ae3457a11eec381c526d'


def load(name, path):
    sp = importlib.util.spec_from_file_location(name, path)
    m = importlib.util.module_from_spec(sp)
    sp.loader.exec_module(m)
    return m


def check(repo):
    coq = repo / 'Coq'
    shared = load('lbtc_shared_source', HERE.parent / 'elements-hash-literal/check-source.py')
    r = shared.check(repo, coq, coq / 'C/jet_haskell_hash_word.v', coq / 'C/jet_elements_hash_literal.v')
    p = load('lbtc_source_parser', coq / 'check-secp-predicates-specification.py')
    paths = []

    def read(path):
        paths.append(path)
        return p.read_code(path)

    def equal(a, b, label):
        if p.compact(a) != p.compact(b):
            raise ValueError('lbtc source differs: ' + label)

    def definition(path, name, expected):
        equal(p.definition(read(path), name), expected, name)

    def line(code, start, expected):
        found = re.findall(r'(?m)^\s*' + re.escape(start) + r'\s*=([^\n]*)$', code)
        if len(found) != 1:
            raise ValueError('missing/ambiguous clause: ' + start)
        equal(found[0], expected, start)

    catalog = read(repo / 'Haskell/Simplicity/Elements/Jets.hs')
    p.require(catalog, 'LbtcAsset :: IssuanceJet () Word256', 'canonical jet type')
    line(catalog, 'specificationIssuance LbtcAsset', 'Prog.lbtcAsset')
    p.require(catalog, 'import qualified Simplicity.Programs.Elements.Lib as Prog', 'selected library import')
    library = read(repo / 'Haskell/Core/Simplicity/Programs/Elements/Lib.hs')
    line(library, 'lbtcAsset', 'Elements.lbtcAsset Elements.lib')
    program = read(repo / 'Haskell/Core/Simplicity/Programs/Elements.hs')
    if program.count('mkLib Sha256.Lib{..} = lib') != 1:
        raise ValueError('ambiguous canonical library constructor')
    body = program.split('mkLib Sha256.Lib{..} = lib', 1)[1]
    found = re.findall(r'(?m)^\s*,\s*lbtcAsset\s*=([^\n]*)$', body)
    if len(found) != 1:
        raise ValueError('missing/ambiguous canonical scribe expression')
    equal(found[0], 'scribe (toWord256 (integerHash256 (review (over le256) ' + CONSTANT + ')))', 'canonical scribe')
    digest = read(repo / 'Haskell/Core/Simplicity/Digest.hs')
    line(digest, 'le256', 'adapter rev rev . be256')
    line(digest, 'rev', 'Hash256 . BSS.toShort . BS.reverse . BSS.fromShort . hash256')
    line(digest, 'fro w', 'Hash256 $ BSS.toShort (encode w)')
    numeric = read(repo / 'Haskell/Core/Simplicity/Word.hs')
    line(numeric, 'put (Word256 a3 a2 a1 a0)', 'put a3 >> put a2 >> put a1 >> put a0')
    proof = coq / 'C/jet_elements_lbtc_asset_local.v'
    execution = coq / 'C/jet_elements_lbtc_asset_exec.v'
    definition(proof, 'lbtc_asset_le_integer', CONSTANT)
    definition(proof, 'lbtc_asset_bytes',
               'map (fun i => Byte.repr (lbtc_asset_le_integer / 2 ^ (8 * Z.of_nat i))) (List.seq 0 32)')
    definition(proof, 'haskell_word64_be_bytes',
               'map (fun i => Byte.repr (w / 2 ^ (8 * (7 - Z.of_nat i)))) (List.seq 0 8)')
    definition(proof, 'haskell_word256_be_bytes',
               'concat (map haskell_word64_be_bytes [hw3 w; hw2 w; hw1 w; hw0 w])')
    definition(proof, 'lbtc_asset_literal', 'haskell_to_word 8 (haskell_integer_hash256 lbtc_asset_bytes)')
    definition(proof, 'lbtc_asset_spec', 'Alg.scribe lbtc_asset_literal')
    definition(execution, 'lbtc_asset_words', '''map Int.repr
      [1834097720; -333536937; 883827383; -1000315839;
       673824976; 1470040689; 1025246445; -377945489]''')
    code = read(proof)
    for name, expected in [
        ('lbtc_asset_review_le_bytes', ': lbtc_asset_bytes = rev (haskell_word256_be_bytes (haskell_word256_from_integer lbtc_asset_le_integer)).'),
        ('lbtc_asset_spec_cells', ': hash_cells lbtc_asset_words = encode (@lbtc_asset_spec Alg.CoreFunSem tt).'),
        ('elements_lbtc_asset_local_spec', ''': application_jet_local_spec_sep
          f_simplicity_lbtc_asset elements_ge Elements.env Ty.Unit Word256
          (fun _ _ _ fp => fp = []) (fun a _ => Some (@lbtc_asset_spec Alg.CoreFunSem a)).''')]:
        found = re.findall(r'\b(?:Lemma|Theorem)\s+' + name + r'\s*(.*?)\bProof\.', code, re.S)
        if len(found) != 1:
            raise ValueError('missing/ambiguous whole contract: ' + name)
        equal(found[0], expected, name)
    c = read(repo / 'C/elements/elementsJets.c')
    start = 'bool simplicity_lbtc_asset(frameItem* dst, frameItem src, const txEnv* env)'
    stop = 'bool simplicity_build_tapleaf_simplicity('
    if c.count(start) != 1 or c.count(stop) != 1:
        raise ValueError('missing/ambiguous actual C jet')
    cbody = c.split(start, 1)[1].split(stop, 1)[0]
    cbody = re.sub(r'//[^\n]*|/\*.*?\*/', '', cbody, flags=re.S)
    equal(cbody, '''{
      (void) src; (void) env;
      const sha256_midstate lbtc_assetid = {{
        0x6d521c38u, 0xec1ea157u, 0x34ae22b7u, 0xc4606441u,
        0x2829c0d0u, 0x579f0a71u, 0x3d1c04edu, 0xe979026fu }};
      writeHash(dst, &lbtc_assetid); return true; }''', 'whole C local-constant function')
    r['source_sha256'].update({str(path): hashlib.sha256(path.read_bytes()).hexdigest() for path in set(paths)})
    r.update(selected_jet='Elements.LbtcAsset', canonical_core_scribe=True,
             little_endian_review_checked=True, whole_c_contract_reviewed=True,
             environment_or_global_value_premise=False, formal_host_library_equivalence=False,
             normal_registration=False, kernel_checked_by_this_tool=False)
    return r


if __name__ == '__main__':
    print(json.dumps(check(Path(sys.argv[1]).resolve()), indent=2))
