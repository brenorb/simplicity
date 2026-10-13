"""Pin the selected Version primitive/program and original C public boundary.

This reviews only Version semantics, not the other thirty Elements clauses.
It supplements compilation, independent kernel checking and AST regeneration.
"""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec); spec.loader.exec_module(module)
    return module


def check(repo, coq):
    parser = load('elements_version_active', coq / 'check-secp-predicates-specification.py')
    compact = parser.compact
    jets = parser.read_code(repo / 'Haskell/Simplicity/Elements/Jets.hs')
    primitive = parser.read_code(repo / 'Haskell/Elements/Simplicity/Elements/Primitive.hs')
    data = parser.read_code(repo / 'Haskell/Elements/Simplicity/Elements/DataTypes.hs')
    for text, wanted, label in [
        (jets, 'Version :: TransactionJet () Word32', 'version jet type'),
        (jets, 'specificationTransaction Version = primitive Prim.Version', 'literal Version dispatch'),
        (primitive, 'Version :: Prim () Word32', 'Version primitive type'),
        (primitive, 'primPrefix = "Elements"', 'primitive namespace'),
        (primitive, 'primName Version = "version"', 'primitive identity'),
        (primitive, 'primSem p a env = interpret p a', 'primitive interpretation application'),
        (primitive, 'tx = envTx env', 'transaction projection'),
        (primitive, 'element = const', 'unit-domain primitive convention'),
        (primitive, 'interpret Version = element . return . toWord32 . toInteger $ sigTxVersion tx',
         'literal unsigned-32 Version semantics'),
        (data, 'sigTxVersion :: Word32', 'transaction version carrier'),
    ]:
        parser.require(text, wanted, label)
    port = parser.read_code(coq / 'C/jet_elements_prim.v')
    # These selected declarations/bindings are exact, not substring matches.
    version_cases = re.findall(r'(?m)^\s*\|\s*Version\s*=>\s*(.*)$', port)
    if version_cases != ['"version"', 'fun _ => Some (fromZ (Int.unsigned (sigTxVersion tx)))']:
        raise ValueError('Version identity/semantics changed or duplicated')
    if (compact(parser.definition(port, 'primName')) != compact('"Elements"')
            or compact(parser.definition(port, 't')) != 'prim'):
        raise ValueError('Elements primitive interface changed')
    parser.require(port, 'Module Elements <: PrimitiveSig.', 'actual primitive module')
    parser.require(port, '| Version : prim Unit Word32', 'Coq primitive type')
    parser.require(port, 'sigTxVersion : int', 'unsigned CompCert word carrier')
    parser.require(port, 'let tx := envTx e in', 'actual primitive transaction projection')
    parser.require(port, 'Module Export PrimitiveElements := PrimitiveModule Elements.',
                   'canonical primitive algebra and semantics')
    canonical = parser.read_code(coq / 'C/jet_elements_version_canonical.v')
    if compact(parser.definition(canonical, 'elements_transaction_version_spec')) != compact(
            'Primitive.Combinators.prim Elements.Version'):
        raise ValueError('public target replaced with nonliteral/numeric program')
    root = parser.read_code(coq / 'C/jet_elements_version_local.v')
    declarations = re.findall(r'\bTheorem\s+elements_version_local_spec\s*:(.*?)\bProof\s*\.', root, re.S)
    wanted = """application_jet_local_spec f_simplicity_version elements_ge Elements.env Ty.Unit Word32
      elements_version_env_rep
      (fun a environment => @elements_transaction_version_spec
        (PrimitivePrimSem option_Monad_Zero) a environment)."""
    if len(declarations) != 1 or compact(declarations[0]) != compact(wanted):
        raise ValueError('original C function/algebra/environment/whole public contract changed')
    representation = """exists be ebase bt txbase version,
      env = Vptr be (Ptrofs.repr ebase) /\\
      0 <= ebase <= Ptrofs.max_unsigned /\\ 0 <= txbase /\\ txbase + 760 <= Ptrofs.max_unsigned /\\
      Mem.load Mptr m be ebase = Some (Vptr bt (Ptrofs.repr txbase)) /\\
      Mem.load Mint64 m bt (txbase + 720) = Some (Vlong version) /\\
      Int64.unsigned version = Int.unsigned (sigTxVersion (Elements.envTx environment))"""
    if compact(parser.definition(root, 'elements_version_env_rep')) != compact(representation):
        raise ValueError('initial physical/logical representation boundary changed')
    unit = (coq / 'C/jet_elements_translation_unit.c').read_text()
    includes = re.findall(r'(?m)^#include\s+"([^"]+)"\s*$', unit)
    if includes != ['../../C/frame.c', '../../C/jets.c', '../../C/sha256.c',
                    '../../C/elements/ops.c', '../../C/elements/elementsJets.c']:
        raise ValueError('derived unit does not include original production C functions')
    paths = [repo / 'Haskell/Simplicity/Elements/Jets.hs',
             repo / 'Haskell/Elements/Simplicity/Elements/Primitive.hs',
             repo / 'Haskell/Elements/Simplicity/Elements/DataTypes.hs',
             coq / 'C/jet_elements_prim.v', coq / 'C/jet_elements_version_canonical.v',
             coq / 'C/jet_elements_version_local.v', coq / 'C/jet_elements_translation_unit.c']
    return {'selected_primitive': 'Elements.Version', 'literal_canonical_dispatch': True,
            'selected_version_semantics_reviewed': True, 'other_semantics_reviewed': False,
            'original_C_public_boundary': True, 'kernel_checked_by_this_tool': False,
            'AST_regeneration_checked_by_this_tool': False, 'normal_registration': False,
            'checkout_coverage_added': 0,
            'sha256': {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}}


if __name__ == '__main__':
    cli = argparse.ArgumentParser(); cli.add_argument('--repo', type=Path, required=True)
    cli.add_argument('--coq', type=Path, required=True)
    args = cli.parse_args(); print(json.dumps(check(args.repo, args.coq), indent=2))

