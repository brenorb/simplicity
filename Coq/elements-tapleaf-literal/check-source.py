"""Selected byte-valued TapleafVersion port and full actual-C contract."""
import argparse
import importlib.util
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def check(repo, coq, literal):
    # The shared converter/transport is imported from this checked dependency.
    inherited = load('tapleaf_shared_sequence_source', HERE.parent / 'elements-sequence-review/check-source.py')
    record = inherited.check(repo, coq, coq / 'C/jet_elements_sequence_literal.v')
    parser = load('tapleaf_selected_source_parser', coq / 'check-secp-predicates-specification.py')
    paths = []
    def read(path):
        paths.append(path)
        return parser.read_code(path)
    def equal(actual, expected, label):
        if parser.compact(actual) != parser.compact(expected):
            raise ValueError('tapleaf source differs: ' + label)
    def line(text, start, expected):
        found = re.findall(r'(?m)^\s*' + re.escape(start) + r'\s*=([^\n]*)$', text)
        if len(found) != 1:
            raise ValueError('missing/ambiguous tapleaf clause: ' + start)
        equal(found[0], expected, start)
    def definition(path, name, expected):
        equal(parser.definition(read(path), name), expected, name)
    catalog = read(repo / 'Haskell/Simplicity/Elements/Jets.hs')
    parser.require(catalog, 'TapleafVersion :: TransactionJet () Word8', 'jet type')
    line(catalog, 'specificationTransaction TapleafVersion', 'primitive Prim.TapleafVersion')
    primitive = read(repo / 'Haskell/Elements/Simplicity/Elements/Primitive.hs')
    parser.require(primitive, 'TapleafVersion :: Prim () Word8', 'primitive type')
    line(primitive, 'primName TapleafVersion', '"tapleafVersion"')
    line(primitive, 'element', 'const')
    line(primitive, 'interpret TapleafVersion',
         'element . return . toWord8 . toInteger . tapleafVersion $ envTap env')
    data = read(repo / 'Haskell/Elements/Simplicity/Elements/DataTypes.hs')
    parser.require(data, 'data TapEnv = TapEnv { tapleafVersion :: Word8', 'unsigned source byte')
    words = read(repo / 'Haskell/Core/Simplicity/Ty/Word.hs')
    for fragment in ['toWord8 = toWord word8', 'word8 = vector8', 'type Word8 = Vector8 Bit',
                     'vector8 = DoubleV vector4', 'vector4 = DoubleV vector2', 'vector2 = DoubleV vector1']:
        parser.require(words, fragment, 'byte shape/conversion')
    port = read(coq / 'C/jet_elements_prim.v')
    for fragment in ['{ tapleafVersion : byte', '| TapleafVersion : prim Unit Word8',
                     '| TapleafVersion => "tapleafVersion"',
                     '| TapleafVersion => fun _ => Some (fromZ (Byte.unsigned (tapleafVersion (envTap e))))']:
        parser.require(port, fragment, 'selected Coq byte primitive')
    definition(coq / 'C/jet_elements_tapleaf_version_local.v', 'elements_tapleaf_version_spec',
               'Primitive.Combinators.prim Elements.TapleafVersion')
    definition(coq / 'C/jet_elements_tapleaf_version_local.v', 'elements_tapleaf_version_env_rep', r'''
      exists be ebase bt tbase,
        env = Vptr be (Ptrofs.repr ebase) /\
        0 <= ebase /\ ebase + 88 <= Ptrofs.max_unsigned /\
        0 <= tbase /\ tbase + 176 <= Ptrofs.max_unsigned /\
        Mem.load Mptr m be (ebase + 8) = Some (Vptr bt (Ptrofs.repr tbase)) /\
        Mem.load Mint8unsigned m bt (tbase + 169) = Some (Vint (Int.repr (Byte.unsigned (tapleafVersion (Elements.envTap e))))) /\
        fp = [(be, ebase + 8, ebase + 16)]''')
    definition(literal, 'elements_tapleaf_version_literal_spec',
               'Some (haskell_to_word 3 (Byte.unsigned (tapleafVersion (Elements.envTap environment))))')
    statements = re.findall(r'Theorem elements_tapleaf_version_literal_local_spec\s*:(.*?)\bProof\.', read(literal), re.S)
    if len(statements) != 1:
        raise ValueError('missing/ambiguous tapleaf C contract')
    equal(statements[0], '''application_jet_local_spec_sep f_simplicity_tapleaf_version elements_ge Elements.env Ty.Unit Word8
      elements_tapleaf_version_env_rep elements_tapleaf_version_literal_spec.''', 'whole actual-C contract')
    import hashlib
    record['source_sha256'].update({str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(set(paths))})
    record.update(selected_primitive='Elements.TapleafVersion', byte_conversion_reviewed=True,
                  shared_sequence_dependency_reviewed=True)
    return record


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    for name in ['repo', 'coq', 'literal']:
        parser.add_argument('--' + name, type=Path, required=True)
    args = parser.parse_args()
    print(json.dumps(check(args.repo, args.coq, args.literal), indent=2))
