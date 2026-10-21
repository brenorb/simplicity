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
 # Curve wiring is checked as a literal tree, not only through its numeric value.
 ('repo','Haskell/Core/Simplicity/Ty/LibSecp256k1.hs','type GE = (FE, FE)','type GE = (FE, GEJ)'),
 ('repo','Haskell/Core/Simplicity/CoreJets.hs','GeIsOnCurve :: Secp256k1Jet Secp256k1.GE Bit','GeIsOnCurve :: Secp256k1Jet Secp256k1.GEJ Bit'),
 ('repo','Haskell/Core/Simplicity/CoreJets.hs','specificationSecp256k1 GeIsOnCurve = Secp256k1.ge_is_on_curve','specificationSecp256k1 GeIsOnCurve = Secp256k1.gej_is_on_curve'),
 ('repo','Haskell/Core/Simplicity/CoreJets.hs','implementationSecp256k1 GeIsOnCurve = FFI.ge_is_on_curve','implementationSecp256k1 GeIsOnCurve = FFI.gej_is_on_curve'),
 ('repo','Haskell/Core/Simplicity/Programs/LibSecp256k1.hs','scribe256 = scribe . toWord256','scribe256 = scribe . toWord128'),
 ('repo','Haskell/Core/Simplicity/Programs/LibSecp256k1.hs','fe_one = one256','fe_one = zero256'),
 ('repo','Haskell/Core/Simplicity/Programs/LibSecp256k1.hs','gej_is_on_curve = ((unit >>> scribe256 7)','gej_is_on_curve = ((unit >>> scribe256 8)'),
 ('repo','Haskell/Core/Simplicity/Programs/LibSecp256k1.hs','(ih >>> fe_cube >>> fe_square)','(oh >>> fe_cube >>> fe_square)'),
 ('repo','Haskell/Core/Simplicity/Programs/LibSecp256k1.hs','take (take fe_cube &&& (drop fe_square >>> fe_negate))','take (drop fe_cube &&& (drop fe_square >>> fe_negate))'),
 ('repo','Haskell/Core/Simplicity/Programs/LibSecp256k1.hs','ge_is_on_curve = iden &&& (unit >>> fe_one) >>> gej_is_on_curve','ge_is_on_curve = iden &&& (unit >>> fe_zero) >>> gej_is_on_curve'),
 ('repo','Haskell/Core/Simplicity/Programs/LibSecp256k1.hs','fe_cube = iden &&& fe_square >>> fe_multiply','fe_cube = fe_square &&& iden >>> fe_multiply'),
 ('coq','C/jet_secp_curve_literal.v','@fromZ (WordToZ 8) 7','@fromZ (WordToZ 8) 8'),
 ('coq','C/jet_secp_curve_literal.v','curve_seven_word : Ty.tySem (Word 8)','curve_seven_word : Ty.tySem (Word 7)'),
 ('coq','C/jet_secp_curve_literal.v','I H >>> @literal_fe_cube term','O H >>> @literal_fe_cube term'),
 ('coq','C/jet_secp_curve_literal.v','@literal_fe_cube term >>> @literal_fe_square term','@literal_fe_square term >>> @literal_fe_square term'),
 ('coq','C/jet_secp_curve_literal.v','O (O (@literal_fe_cube term)','O (I (@literal_fe_cube term)'),
 ('coq','C/jet_secp_curve_literal.v','I (@literal_fe_square term) >>> @literal_fe_negate term','I (@literal_fe_square term) >>> @canonical_fe_normalize term'),
 ('coq','C/jet_secp_curve_literal.v','>>> @canonical_fe_is_zero term.','>>> @canonical_fe_is_odd term.'),
 ('coq','C/jet_secp_curve_literal.v','(unit >>> @literal_fe_one256 term)','(unit >>> @Word.zero 8 term)'),
 ('coq','C/jet_secp_curve_literal.v','iden &&& (unit >>> @literal_fe_one256 term) >>> @literal_gej_is_on_curve term','iden &&& (unit >>> @literal_fe_one256 term) >>> @literal_gej_is_infinity term'),
 ('coq','C/jet_secp_rescale_literal.v','iden &&& @literal_fe_square term >>> @literal_fe_multiply term','@literal_fe_square term &&& iden >>> @literal_fe_multiply term'),
 ('coq','C/jet_secp_literal_add_program.v','Bit.true >>> @left_pad_low_1_n term 8','Bit.false >>> @left_pad_low_1_n term 8'),
 ('coq','C/jet_secp_curve_local.v','Theorem ge_is_on_curve_literal_local_spec :','Theorem ge_is_on_curve_literal_local_spec : False ->'),
 ('coq','C/jet_secp_curve_local.v','f_simplicity_ge_is_on_curve','f_secp256k1_ge_is_valid_var'),
 ('coq','C/jet_secp_curve_local.v','(Ty.Prod (Word 8) (Word 8)) (Ty.Sum Ty.Unit Ty.Unit)','(Ty.Prod (Word 7) (Word 8)) (Ty.Sum Ty.Unit Ty.Unit)'),
 ('coq','C/jet_secp_curve_local.v','(Ty.Sum Ty.Unit Ty.Unit)','(Word 8)'),
 ('coq','C/jet_secp_curve_local.v','(@literal_ge_is_on_curve Alg.CoreFunSem).','(@literal_gej_is_on_curve Alg.CoreFunSem).'),
 ('coq','C/jet_secp_curve_literal.v','I H >>> @literal_fe_cube term','O H >>> @literal_fe_cube term (* I H >>> @literal_fe_cube term *)'),
 # Guarded X-equivalence: preserve the actual program, domain and endpoint.
 ('coq','Simplicity/Bit.v','s &&& iden >>> cond t false.','s &&& iden >>> cond t true.'),
 ('repo','Haskell/Core/Simplicity/Programs/Bit.hs','and s t = s &&& iden >>> cond t false','and s t = s &&& iden >>> cond false t'),
 ('repo','Haskell/Core/Simplicity/CoreJets.hs','GejXEquiv :: Secp256k1Jet (Secp256k1.FE, Secp256k1.GEJ) Bit','GejXEquiv :: Secp256k1Jet (Secp256k1.FE, Secp256k1.GE) Bit'),
 ('repo','Haskell/Core/Simplicity/CoreJets.hs','specificationSecp256k1 GejXEquiv = Secp256k1.gej_x_equiv','specificationSecp256k1 GejXEquiv = Secp256k1.gej_equiv'),
 ('repo','Haskell/Core/Simplicity/CoreJets.hs','implementationSecp256k1 GejXEquiv = FFI.gej_x_equiv','implementationSecp256k1 GejXEquiv = FFI.gej_equiv'),
 ('repo','Haskell/Core/Simplicity/Programs/LibSecp256k1.hs','gej_is_infinity = drop fe_is_zero','gej_is_infinity = take fe_is_zero'),
 ('repo','Haskell/Core/Simplicity/Programs/LibSecp256k1.hs','gej_x_equiv = and (not (drop gej_is_infinity))','gej_x_equiv = and (drop gej_is_infinity)'),
 ('repo','Haskell/Core/Simplicity/Programs/LibSecp256k1.hs','drop (take (take fe_negate)) &&& (drop (drop fe_square) &&& oh >>> fe_multiply)','drop (take (drop fe_negate)) &&& (drop (drop fe_square) &&& oh >>> fe_multiply)'),
 ('repo','Haskell/Core/Simplicity/Programs/LibSecp256k1.hs','drop (drop fe_square) &&& oh >>> fe_multiply','drop (take fe_square) &&& oh >>> fe_multiply'),
 ('repo','Haskell/Core/Simplicity/Programs/LibSecp256k1.hs','drop (drop fe_square) &&& oh >>> fe_multiply','drop (drop fe_square) &&& ih >>> fe_multiply'),
 ('coq','C/jet_secp_literal_gej_predicate.v','Alg.Core.Combinators.drop (@canonical_fe_is_zero term)','Alg.Core.Combinators.take (@canonical_fe_is_zero term)'),
 ('coq','C/jet_secp_x_equiv_literal.v','Bit.and (Bit.not (I (@literal_gej_is_infinity term)))','Bit.or (Bit.not (I (@literal_gej_is_infinity term)))'),
 ('coq','C/jet_secp_x_equiv_literal.v','Bit.and (Bit.not (I (@literal_gej_is_infinity term)))','Bit.and (I (@literal_gej_is_infinity term))'),
 ('coq','C/jet_secp_x_equiv_literal.v','I (O (O (@literal_fe_negate term)))','I (O (I (@literal_fe_negate term)))'),
 ('coq','C/jet_secp_x_equiv_literal.v','I (I (@literal_fe_square term))','I (O (@literal_fe_square term))'),
 ('coq','C/jet_secp_x_equiv_literal.v','&&& O H >>> @literal_fe_multiply term','&&& I H >>> @literal_fe_multiply term'),
 ('coq','C/jet_secp_x_equiv_literal.v','>>> @literal_fe_add term >>> @canonical_fe_is_zero term)','>>> @literal_fe_multiply term >>> @canonical_fe_is_zero term)'),
 ('coq','C/jet_secp_x_equiv_literal.v','>>> @canonical_fe_is_zero term)','>>> @canonical_fe_is_odd term)'),
 ('coq','C/jet_secp_x_equiv_literal.v','term (Ty.Prod (Word 8) (Ty.Prod (Ty.Prod (Word 8) (Word 8)) (Word 8)))','term (Ty.Prod (Word 7) (Ty.Prod (Ty.Prod (Word 8) (Word 8)) (Word 8)))'),
 ('coq','C/jet_secp_x_equiv_literal.v','(Ty.Sum Ty.Unit Ty.Unit) :=','(Word 8) :='),
 ('coq','C/jet_secp_x_equiv_local.v','Theorem gej_x_equiv_literal_local_spec :','Theorem gej_x_equiv_literal_local_spec : False ->'),
 ('coq','C/jet_secp_x_equiv_local.v','secp_jet_local_spec f_simplicity_gej_x_equiv','secp_jet_local_spec f_secp256k1_gej_eq_x_var'),
 ('coq','C/jet_secp_x_equiv_local.v','(Ty.Sum Ty.Unit Ty.Unit)','(Word 8)'),
 ('coq','C/jet_secp_x_equiv_local.v','(@literal_gej_x_equiv Alg.CoreFunSem).','(fun _ => inr tt).'),
 ('coq','C/jet_secp_x_equiv_literal.v','I (I (@literal_fe_square term))','I (O (@literal_fe_square term)) (* I (I (@literal_fe_square term)) *)'),
]
with tempfile.TemporaryDirectory(prefix='secp-predicate-gate.') as tmp:
 coq,repo=Path(tmp)/'Coq',Path(tmp)/'repo'
 for relative in ['check-secp-normalize-specification.py', 'C/jet_secp_canonical_normalize.v', 'C/jet_secp_normalize_local.v', 'C/jet_bitmachine_rep.v', 'Simplicity/Bit.v', 'Simplicity/Word.v', 'C/jet_test_value_spec.v', 'C/jet_equality_spec.v', 'C/jet_predicate_spec.v', 'C/jet_secp_canonical_odd.v', 'C/jet_secp_canonical_zero.v', 'C/jet_secp_odd_local.v', 'C/jet_secp_zero_local.v', 'C/jet_secp_curve_literal.v', 'C/jet_secp_curve_local.v', 'C/jet_secp_rescale_literal.v', 'C/jet_secp_literal_add_program.v', 'C/jet_secp_literal_gej_predicate.v', 'C/jet_secp_x_equiv_literal.v', 'C/jet_secp_x_equiv_local.v']:
  dst=coq/relative;dst.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(SOURCE/relative,dst)
 for relative in ['Haskell/Core/Simplicity/CoreJets.hs', 'Haskell/Core/Simplicity/Ty/LibSecp256k1.hs', 'Haskell/Core/Simplicity/Programs/LibSecp256k1.hs', 'Haskell/Core/Simplicity/LibSecp256k1/Spec.hs', 'Haskell/Core/Simplicity/Programs/Arith.hs', 'Haskell/Core/Simplicity/Programs/Word.hs', 'Haskell/Core/Simplicity/Programs/Generic.hs', 'Haskell/Core/Simplicity/Programs/Bit.hs']:
  dst=repo/relative;dst.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(project/relative,dst)
 assert gate.check(coq,repo)==4
 for kind,relative,old,new in mutations:
  path=(coq if kind=='coq' else repo)/relative
  original=path.read_text();assert old in original,(relative,old)
  path.write_text(original.replace(old,new,1))
  try:gate.check(coq,repo)
  except ValueError:pass
  else:raise AssertionError((relative,old))
  finally:path.write_text(original)
 assert gate.check(coq,repo)==4
print(f'predicate source gate passed; rejected {len(mutations)} meaningful mutations')
