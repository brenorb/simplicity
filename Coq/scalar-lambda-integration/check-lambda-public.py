"""Pin original lambda dispatch, literal term and initialized public boundary."""
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
    parent = load('lambda_parent_public', coq / 'scalar-square-review/check-square-public.py')
    receipt = parent.check(repo, coq)
    parser = load('lambda_active_parser', coq / 'check-secp-predicates-specification.py')
    compact = parser.compact
    catalog = parser.read_code(repo / 'Haskell/Core/Simplicity/CoreJets.hs')
    parser.require(catalog, 'ScalarMultiplyLambda :: Secp256k1Jet Secp256k1.Scalar Secp256k1.Scalar',
                   'lambda catalog type')
    parser.require(catalog, 'specificationSecp256k1 ScalarMultiplyLambda = Secp256k1.scalar_multiply_lambda',
                   'lambda canonical dispatch')
    root = parser.read_code(coq / 'C/jet_secp_scalar_lambda_local.v')
    declarations = re.findall(r'\bTheorem\s+scalar_lambda_initialized_local_spec\s*:(.*?)\bProof\s*\.', root, re.S)
    wanted = ('secp_jet_initialized_local_spec scalar_lambda_initialized '
              'f_simplicity_scalar_multiply_lambda (Word 8) (Word 8) '
              '(@canonical_scalar_multiply_lambda Alg.CoreFunSem).')
    if len(declarations) != 1 or compact(declarations[0]) != compact(wanted):
        raise ValueError('lambda original function/literal public contract changed')
    contract = parser.read_code(coq / 'C/jet_secp_initialized_contract.v')
    legacy = parser.read_code(coq / 'C/jet_secp_normalize_local.v')
    new = compact(parser.definition(contract, 'secp_jet_initialized_local_spec'))
    old = compact(parser.definition(legacy, 'secp_jet_local_spec'))
    header = re.findall(r'\bDefinition\s+secp_jet_initialized_local_spec\b(.*?) :=', contract, re.S)
    signature = '(Ready : Mem.mem -> Prop) (f : function) (A B : Ty) (spec : A -> B) : Prop'
    if len(header) != 1 or compact(header[0]) != compact(signature):
        raise ValueError('initialized contract signature changed')
    if (new.count('Readym->') != 1 or not new.endswith('/\\Readymf')
            or new.replace('Readym->', '', 1).removesuffix('/\\Readymf') != old):
        raise ValueError('initialized contract weakens legacy execution/output/framing')
    definitions = [
        ('jet_secp_canonical_scalar_lambda.v', 'canonical_lambda_word',
         '@fromZ (WordToZ 8) canonical_lambda_value'),
        ('jet_secp_canonical_scalar_lambda.v', 'canonical_scalar_lambda',
         'Alg.scribe canonical_lambda_word'),
        ('jet_secp_canonical_scalar_lambda.v', 'canonical_scalar_multiply_lambda',
         '(unit >>> @canonical_scalar_lambda term) &&& iden >>> @canonical_scalar_multiply term'),
        ('jet_secp_scalar_lambda_initialized.v', 'scalar_lambda_initialized',
         'scalar_lambda_global_rep m /\\ readonly_region_bounds m scalar_lambda_block 0 32'),
        ('jet_secp_scalar_lambda_global.v', 'scalar_lambda_block',
         'secp_symbol_block _secp256k1_const_lambda'),
        ('jet_secp_scalar_lambda_global.v', 'scalar_lambda_words',
         '[Int64.repr (-2377172193522762382); Int64.repr 1310022930574435960; '
         'Int64.repr (-6546514211138018214); Int64.repr 6008836872998760672]'),
        ('jet_secp_scalar_lambda_global.v', 'scalar_lambda_global_rep',
         'Mem.valid_block m scalar_lambda_block /\\ '
         'Mem.range_perm m scalar_lambda_block 0 32 Cur Readable /\\ '
         'forall i w, nth_error scalar_lambda_words i = Some w -> '
         'Mem.load Mint64 m scalar_lambda_block (8 * Z.of_nat i) = Some (Vlong w)'),
        ('jet_clight_readonly_frame.v', 'readonly_region_bounds',
         'forall ofs k p, Mem.perm m b ofs k p <-> lo <= ofs < hi /\\ perm_order Readable p'),
    ]
    for file, name, expected in definitions:
        actual = parser.definition(parser.read_code(coq / 'C' / file), name)
        if compact(actual) != compact(expected):
            raise ValueError('lambda definition changed: ' + name)
    haskell_path = repo / 'Haskell/Core/Simplicity/Programs/LibSecp256k1.hs'
    haskell = parser.read_code(haskell_path)
    parts = haskell.split('mkLib Sha256.Lib{..} = lib')
    if len(parts) != 2:
        raise ValueError('lambda mkLib boundary changed')
    fields = [line.strip() for line in parts[1].splitlines()
              if re.match(r'\s*, scalar_multiply_lambda\s*=', line)]
    if fields != [', scalar_multiply_lambda = (unit >>> scalar_lambda) &&& iden >>> scalar_multiply']:
        raise ValueError('canonical lambda combinator tree changed')
    bindings = re.findall(r'(?m)^\s*scalar_lambda\s*=(.*)$', parts[1])
    if bindings != [' scribe256 LibSecp256k1.lambda']:
        raise ValueError('canonical scalar_lambda literal changed')
    value_path = repo / 'Haskell/Core/Simplicity/LibSecp256k1/Spec.hs'
    constants = re.findall(r'(?m)^lambda\s*=\s*(0x[0-9a-fA-F]+)\s*$', parser.read_code(value_path))
    global_code = parser.read_code(coq / 'C/jet_secp_scalar_lambda_global.v')
    value = compact(parser.definition(global_code, 'canonical_lambda_value'))
    if constants != ['0x5363ad4cc05c30e0a5261c028812645a122e22ea20816678df02967c1b23bd72'] or value != str(int(constants[0], 16)):
        raise ValueError('Haskell/Coq lambda constant changed')
    # Executability from real initialization must remain available, not merely
    # a conditional global-representation assertion.
    fresh = parser.read_code(coq / 'C/jet_secp_scalar_lambda_fresh.v')
    statements = re.findall(r'\bTheorem\s+scalar_lambda_runs_from_actual_init\b(.*?)\bProof\s*\.', fresh, re.S)
    wanted_fresh = r"""(value : Ty.tySem (Word 8)) env :
      exists mi m bd bs bi bw edge mf,
      Genv.init_mem jets_secp.prog = Some mi /\ scalar_lambda_initialized mi /\
      frame_fields_at m bs 0 bi edge 0 /\ frame_input_cells_at m bi edge 0 (encode value) /\
      write_frame_at m bd 0 bw 0 256 256 /\
      Clight2.eval_funcall secp_ge m (Internal f_simplicity_scalar_multiply_lambda)
        [Vptr bd Ptrofs.zero;Vptr bs Ptrofs.zero;env] E0 mf (Vint Int.one) /\
      finv m bd 0 bw 0 256 256 bi mf true (encode (@canonical_scalar_multiply_lambda Alg.CoreFunSem value)) /\
      scalar_lambda_initialized mf /\
      (forall b chunk ofs, Mem.valid_block mi b -> Mem.load chunk mf b ofs = Mem.load chunk mi b ofs)."""
    if len(statements) != 1 or compact(statements[0]) != compact(wanted_fresh):
        raise ValueError('actual init/fresh frames/literal original call witness changed')
    paths = [coq / 'C' / file for file, _, _ in definitions] + [
        coq / 'C/jet_secp_scalar_lambda_local.v', coq / 'C/jet_secp_initialized_contract.v',
        coq / 'C/jet_secp_scalar_lambda_fresh.v', coq / 'C/jet_secp_scalar_lambda_init_exists.v',
        coq / 'C/jet_program_initialization.v', haskell_path, value_path]
    receipt['hashes'].update({str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths})
    receipt.update(lambda_literal_dispatch=True, complete_initialized_public_lambda_C_contract=True,
                   actual_initialization_fresh_frames_witness=True,
                   scope='initialized local-frame / LP64 / RECKLESS; not C evaluator setup, assertion-enabled or every-jet completion',
                   public_coverage_added=0)
    return receipt


if __name__ == '__main__':
    cli = argparse.ArgumentParser()
    cli.add_argument('--repo', type=Path, required=True)
    cli.add_argument('--coq', type=Path, required=True)
    args = cli.parse_args(); print(json.dumps(check(args.repo, args.coq), indent=2))

