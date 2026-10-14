"""Selected literal Elements getter semantics and exact public boundaries."""
import argparse
import importlib.util
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True


def check(repo, coq):
    spec = importlib.util.spec_from_file_location('getters_version_guard', coq / 'elements-version-review/check-version-source.py')
    version = importlib.util.module_from_spec(spec); spec.loader.exec_module(version)
    version.check(repo, coq)
    parser = version.load('getters_parser', coq / 'check-secp-predicates-specification.py')
    compact = parser.compact
    port = parser.read_code(coq / 'C/jet_elements_prim.v')
    hs = parser.read_code(repo / 'Haskell/Elements/Simplicity/Elements/Primitive.hs')
    jets = parser.read_code(repo / 'Haskell/Simplicity/Elements/Jets.hs')
    data = parser.read_code(repo / 'Haskell/Elements/Simplicity/Elements/DataTypes.hs')
    parser.require(hs, 'envIx :: Data.Word.Word32', 'index carrier')
    parser.require(hs, 'ix = envIx env', 'index projection')
    parser.require(data, 'sigTxLock :: Lock', 'lock carrier')
    parser.require(data, 'type Lock = Word32', 'unsigned 32-bit lock')
    parser.require(port, 'sigTxLock : int', 'unsigned lock carrier')
    parser.require(port, 'let ix := envIx e in', 'actual index projection')
    parser.require(port, 'envIx : nat', 'natural index carrier')
    parser.require(port, 'envIxWord32 : (Z.of_nat envIx < 4294967296)%Z', 'index range')
    for primitive, label, suffix, function, expr, coq_expr in [
        ('LockTime', 'lockTime', 'locktime', 'lock_time', 'sigTxLock tx', 'Int.unsigned (sigTxLock tx)'),
        ('CurrentIndex', 'currentIndex', 'current_index', 'current_index', 'ix', 'Z.of_nat ix'),
    ]:
        parser.require(jets, primitive + ' :: TransactionJet () Word32', 'jet type')
        parser.require(jets, 'specificationTransaction ' + primitive + ' = primitive Prim.' + primitive, 'literal dispatch')
        parser.require(hs, primitive + ' :: Prim () Word32', 'primitive type')
        parser.require(hs, 'primName ' + primitive + ' = "' + label + '"', 'identity')
        parser.require(hs, 'interpret ' + primitive + ' = element . return . toWord32 . toInteger $ ' + expr, 'literal semantics')
        cases = re.findall(r'(?m)^\s*\|\s*' + primitive + r'\s*=>\s*(.*)$', port)
        if cases != ['"' + label + '"', 'fun _ => Some (fromZ (' + coq_expr + '))']:
            raise ValueError('changed or duplicate selected primitive clause')
        root = parser.read_code(coq / ('C/jet_elements_' + suffix + '_local.v'))
        target = 'elements_transaction_' + suffix + '_spec'
        if compact(parser.definition(root, target)) != compact('Primitive.Combinators.prim Elements.' + primitive):
            raise ValueError('nonliteral target')
        theorem = 'elements_' + suffix + '_local_spec'
        declarations = re.findall(r'\bTheorem\s+' + theorem + r'\s*:(.*?)\bProof\s*\.', root, re.S)
        wanted = ('application_jet_local_spec f_simplicity_' + function + ' elements_ge Elements.env Ty.Unit Word32 '
                  'elements_' + suffix + '_env_rep (fun a environment => @' + target +
                  ' (PrimitivePrimSem option_Monad_Zero) a environment).')
        if len(declarations) != 1 or compact(declarations[0]) != compact(wanted):
            raise ValueError('public function/environment/whole contract changed')
        representation = (r'''exists be ebase bt txbase value,
          env = Vptr be (Ptrofs.repr ebase) /\
          0 <= ebase <= Ptrofs.max_unsigned /\ 0 <= txbase /\ txbase + 760 <= Ptrofs.max_unsigned /\
          Mem.load Mptr m be ebase = Some (Vptr bt (Ptrofs.repr txbase)) /\
          Mem.load Mint64 m bt (txbase + 728) = Some (Vlong value) /\
          Int64.unsigned value = Int.unsigned (sigTxLock (Elements.envTx environment))'''
          if primitive == 'LockTime' else r'''exists be ebase index,
          env = Vptr be (Ptrofs.repr ebase) /\
          0 <= ebase /\ ebase + 88 <= Ptrofs.max_unsigned /\
          Mem.load Mint64 m be (ebase + 80) = Some (Vlong index) /\
          Int64.unsigned index = Z.of_nat (Elements.envIx environment)''')
        if compact(parser.definition(root, 'elements_' + suffix + '_env_rep')) != compact(representation):
            raise ValueError('initial physical/logical boundary changed')
    return 'Selected Version/LockTime/CurrentIndex correspondence checked; other Elements clauses not reviewed.'


if __name__ == '__main__':
    cli = argparse.ArgumentParser(); cli.add_argument('--repo', type=Path, required=True); cli.add_argument('--coq', type=Path, required=True)
    args = cli.parse_args(); print(check(args.repo, args.coq))
