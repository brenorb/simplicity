import importlib.util,sys,shutil,tempfile
from pathlib import Path
sys.dont_write_bytecode = True
SOURCE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('predicate_gate',SOURCE/'check-secp-predicates-specification.py')
gate=importlib.util.module_from_spec(spec);spec.loader.exec_module(gate)
project=gate.REPO
mutations=[
 ('repo','Haskell/Core/Simplicity/Programs/Word.hs','rightmost (DoubleV v) = drop (rightmost v)','rightmost (DoubleV v) = take (rightmost v)'),
 ('repo','Haskell/Core/Simplicity/Programs/Word.hs','some (DoubleV w) = or (take rec) (drop rec)','some (DoubleV w) = and (take rec) (drop rec)'),
 ('repo','Haskell/Core/Simplicity/Programs/Generic.hs','go OneR          = true','go OneR          = false'),
 ('repo','Haskell/Core/Simplicity/CoreJets.hs','specificationSecp256k1 FeIsOdd = Secp256k1.fe_is_odd','specificationSecp256k1 FeIsOdd = Secp256k1.fe_is_zero'),
 ('repo','Haskell/Core/Simplicity/CoreJets.hs','FeIsZero :: Secp256k1Jet Secp256k1.FE Bit','FeIsZero :: Secp256k1Jet Secp256k1.FE Secp256k1.FE'),
 ('repo','Haskell/Core/Simplicity/Programs/LibSecp256k1.hs','lsb256 = Arith.lsb word256','lsb256 = Arith.lsb word128'),
 ('repo','Haskell/Core/Simplicity/Programs/Arith.hs','lsb w = rightmost w','lsb w = leftmost w'),
 ('repo','Haskell/Core/Simplicity/Programs/Arith.hs','is_zero w = not (some w)','is_zero w = some w'),
 ('repo','Haskell/Core/Simplicity/Programs/LibSecp256k1.hs','fe_is_odd = fe_normalize >>> lsb256','fe_is_odd = lsb256'),
 ('repo','Haskell/Core/Simplicity/Programs/LibSecp256k1.hs','fe_is_zero = or (Arith.is_zero word256)\n                  ((unit >>> scribeFeOrder) &&& iden >>> eq)','fe_is_zero = Arith.is_zero word256'),
 ('coq','C/jet_secp_canonical_odd.v','@Word.rightmost Bit 8 term','@Word.leftmost Bit 8 term'),
 ('coq','C/jet_secp_canonical_odd.v','@Word.rightmost Bit 8 term','@Word.rightmost Bit 7 term'),
 ('coq','C/jet_secp_canonical_zero.v','Bit.or (@is_zero_word_spec 8 term)','Bit.and (@is_zero_word_spec 8 term)'),
 ('coq','C/jet_secp_canonical_zero.v','@equality_spec (Word 8) term','@equality_spec (Word 7) term'),
 ('coq','C/jet_secp_odd_local.v','Theorem fe_odd_local_spec :','Theorem fe_odd_local_spec : False ->'),
 ('coq','C/jet_secp_zero_local.v','Theorem fe_zero_local_spec :','Theorem fe_zero_local_spec : False ->'),
 ('coq','C/jet_secp_odd_local.v','f_simplicity_fe_is_odd (Word 8) Bit','f_simplicity_fe_is_zero (Word 8) Bit'),
 ('coq','C/jet_secp_zero_local.v','(@canonical_fe_is_zero Alg.CoreFunSem).','(fun _ => Bit.one).'),
 ('coq', 'Simplicity/Bit.v', 's &&& iden >>> cond true t.', 's &&& iden >>> cond t false.'),
 ('coq', 'Simplicity/Bit.v', 't &&& unit >>> cond false true.', 't &&& unit >>> cond true false.'),
 ('coq', 'Simplicity/Bit.v', 'case (drop els) (drop thn).', 'case (drop thn) (drop els).'),
 ('coq', 'Simplicity/Word.v', 'X := drop rec.', 'X := take rec.'),
 ('coq', 'Simplicity/Word.v', '| S n => build_rightmost rightmost', '| S n => build_leftmost leftmost'),
 ('coq', 'C/jet_test_value_spec.v', 'Bit.not (@predicate_spec n Datatypes.false term)', 'Bit.not (@predicate_spec n Datatypes.true term)'),
 ('coq', 'C/jet_predicate_spec.v', 'if all then Bit.and hi lo else Bit.or hi lo', 'if all then Bit.and hi lo else Bit.and hi lo'),
 ('coq', 'C/jet_equality_spec.v', '| Ty.Unit => Bit.true', '| Ty.Unit => Bit.false'),
 ('coq', 'C/jet_equality_spec.v', '>>* Bit.cond (equality_spec R) Bit.false', '>>* Bit.cond (equality_spec R) Bit.true'),
 ('repo', 'Haskell/Core/Simplicity/Programs/Bit.hs', 'or s t = s &&& iden >>> cond true t', 'or s t = s &&& iden >>> cond t false'),
 ('repo', 'Haskell/Core/Simplicity/Programs/Bit.hs', 'not t = t &&& unit >>> cond false true', 'not t = t &&& unit >>> cond true false'),
 ('repo', 'Haskell/Core/Simplicity/Programs/Bit.hs', 'cond thn els = match (drop els) (drop thn)', 'cond thn els = match (drop thn) (drop els)'),
 ('repo', 'Haskell/Core/Simplicity/Programs/Word.hs', 'rightmost (DoubleV v) = drop (rightmost v)', 'rightmost (DoubleV v) = take (rightmost v)\n-- rightmost (DoubleV v) = drop (rightmost v)'),
 ('repo', 'Haskell/Core/Simplicity/Programs/Bit.hs', 'or s t = s &&& iden >>> cond true t', 'or s t = s &&& iden >>> cond t false\n{- or s t = s &&& iden >>> cond true t -}'),
 ('coq', 'C/jet_secp_canonical_odd.v', '@Word.rightmost Bit 8 term', '@Word.leftmost Bit 8 term (* @Word.rightmost Bit 8 term *)'),
 ('coq', 'Simplicity/Word.v', 'X := drop rec.', 'X := take rec.\n(* Definition build_rightmost {V X} {term : Core.Algebra} (rec : term V X) : term (V * V) X := drop rec. *)'),
]
with tempfile.TemporaryDirectory(prefix='secp-predicate-gate.') as tmp:
 coq,repo=Path(tmp)/'Coq',Path(tmp)/'repo'
 for relative in ['check-secp-normalize-specification.py', 'C/jet_secp_canonical_normalize.v', 'C/jet_secp_normalize_local.v', 'C/jet_bitmachine_rep.v', 'Simplicity/Bit.v', 'Simplicity/Word.v', 'C/jet_test_value_spec.v', 'C/jet_equality_spec.v', 'C/jet_predicate_spec.v', 'C/jet_secp_canonical_odd.v', 'C/jet_secp_canonical_zero.v', 'C/jet_secp_odd_local.v', 'C/jet_secp_zero_local.v']:
  dst=coq/relative;dst.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(SOURCE/relative,dst)
 for relative in ['Haskell/Core/Simplicity/CoreJets.hs', 'Haskell/Core/Simplicity/Ty/LibSecp256k1.hs', 'Haskell/Core/Simplicity/Programs/LibSecp256k1.hs', 'Haskell/Core/Simplicity/LibSecp256k1/Spec.hs', 'Haskell/Core/Simplicity/Programs/Arith.hs', 'Haskell/Core/Simplicity/Programs/Word.hs', 'Haskell/Core/Simplicity/Programs/Generic.hs', 'Haskell/Core/Simplicity/Programs/Bit.hs']:
  dst=repo/relative;dst.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(project/relative,dst)
 assert gate.check(coq,repo)==2
 for kind,relative,old,new in mutations:
  path=(coq if kind=='coq' else repo)/relative
  original=path.read_text();assert old in original,(relative,old)
  path.write_text(original.replace(old,new,1))
  try:gate.check(coq,repo)
  except ValueError:pass
  else:raise AssertionError((relative,old))
  finally:path.write_text(original)
 assert gate.check(coq,repo)==2
print(f'predicate source gate passed; rejected {len(mutations)} meaningful mutations')
