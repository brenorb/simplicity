"""In-memory source-port mutations; no audit inputs are changed."""
from pathlib import Path
import importlib.util,sys
from unittest.mock import patch
sys.dont_write_bytecode=True
archive=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('scalar_literal',archive/'check-scalar-ports.py')
gate=importlib.util.module_from_spec(spec);spec.loader.exec_module(gate)
files,ports=gate.files,gate.ports
mutations=[
 ('repo',files[1],'type Scalar = Word256','type Scalar = Word128'),
 ('repo',files[2],'scalar_normalize = (iden &&& (unit >>> scribeGroupOrder)','scalar_normalize = (iden &&& (unit >>> scribeFeOrder)'),
 ('repo',files[2],'scalar_is_zero = or (Arith.is_zero word256)','scalar_is_zero = and (Arith.is_zero word256)'),
 ('repo',files[3],'groupOrder = 0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141','groupOrder = 0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364142'),
 ('source',ports[0],'>>> cond (I H) (O H)','>>> cond (O H) (I H)'),
 ('source',ports[0],'@subtract_word_spec term 8','@subtract_word_spec term 7'),
 ('source',ports[1],'@equality_spec (Word 8) term','@equality_spec (Word 7) term'),
 ('source',ports[1],'Bit.or (@is_zero_word_spec 8 term)','Bit.and (@is_zero_word_spec 8 term)'),
]

if __name__ == '__main__':
 if len(sys.argv)!=4: raise SystemExit('usage: test-literal.py REPO SCRATCH COQ')
 repo,source,coq=map(Path,sys.argv[1:])
 if gate.check(repo,source,coq)!=2: raise AssertionError('scope')
 mutations += [
  ('repo','Haskell/Core/Simplicity/Programs/Bit.hs','or s t = s &&& iden >>> cond true t','or s t = s &&& iden >>> cond false t'),
  ('coq','C/jet_test_value_spec.v','Bit.not (@predicate_spec n Datatypes.false term)','Bit.not (@predicate_spec n Datatypes.true term)'),
  ('coq','C/jet_equality_spec.v','Ty.Unit => Bit.true','Ty.Unit => Bit.false'),
 ]
 original=Path.read_text
 for kind,relative,old,new in mutations:
  target={'repo':repo,'source':source,'coq':coq}[kind]/relative
  baseline=original(target)
  if old not in baseline: raise AssertionError('missing fixture '+relative)
  changed=baseline.replace(old,new,1)
  def read(p,*args,**kwargs):
   return changed if p==target else original(p,*args,**kwargs)
  with patch.object(Path,'read_text',read):
   try: gate.check(repo,source,coq)
   except (ValueError,AssertionError): pass
   else: raise AssertionError('mutation accepted: '+relative)
 if gate.check(repo,source,coq)!=2: raise AssertionError('post-fixture scope')
 print('two literal scalar ports match; eleven in-memory canonical/recursive mutations rejected')
