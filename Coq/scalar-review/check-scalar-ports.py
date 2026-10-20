"""Review isolated literal scalar programs; this does not establish C execution."""
from pathlib import Path
import argparse,importlib.util,re,sys,json,hashlib
sys.dont_write_bytecode=True
files=['Haskell/Core/Simplicity/CoreJets.hs','Haskell/Core/Simplicity/Ty/LibSecp256k1.hs','Haskell/Core/Simplicity/Programs/LibSecp256k1.hs','Haskell/Core/Simplicity/LibSecp256k1/Spec.hs']
ports=['jet_secp_canonical_scalar.v','jet_secp_canonical_scalar_zero.v']
def check(repo,source,coq):
 spec=importlib.util.spec_from_file_location('literal_gate',coq/'check-secp-predicates-specification.py')
 gate=importlib.util.module_from_spec(spec);spec.loader.exec_module(gate)
 gate.check(coq,repo)  # Recheck recursive equality/is_zero/subtraction ports and canonical dependencies.

 catalog=gate.read_code(repo/files[0]);types=gate.read_code(repo/files[1]);program=gate.read_code(repo/files[2]);field=gate.read_code(repo/files[3])
 gate.require(types,'type Scalar = Word256','scalar domain')
 for constructor,name,out in [('ScalarNormalize','scalar_normalize','Secp256k1.Scalar'),('ScalarIsZero','scalar_is_zero','Bit')]:
  gate.require(catalog,f'{constructor} :: Secp256k1Jet Secp256k1.Scalar {out}',name+' jet type')
  gate.require(catalog,f'specificationSecp256k1 {constructor} = Secp256k1.{name}',name+' dispatch')
 gate.require(program,'scribeGroupOrder = scribe256 LibSecp256k1.groupOrder','group constant')
 impl=program.split('lib@Lib{..} = Lib {',1)[1]
 gate.exact_program(impl,'scalar_normalize','scalar_is_zero','(iden &&& (unit >>> scribeGroupOrder) >>> sub256) &&& iden >>> ooh &&& (oih &&& ih) >>> cond ih oh')
 gate.exact_program(impl,'scalar_is_zero','scalar_add','or (Arith.is_zero word256) ((unit >>> scribeGroupOrder) &&& iden >>> eq)')
 port=gate.read_code(source/ports[0]);zero=gate.read_code(source/ports[1])
 group=re.search(r'(?m)^groupOrder\s*=\s*(0x[0-9a-fA-F]+)\s*$',field)
 assert group and int(group[1],16)==int(gate.definition(port,'canonical_group_order').strip())
 assert gate.compact(gate.definition(port,'canonical_group_word'))==gate.compact('@fromZ (WordToZ 8) canonical_group_order')
 expected='((iden &&& (unit >>> Alg.scribe canonical_group_word) >>> @subtract_word_spec term 8) &&& iden) >>> (O O H &&& (O I H &&& I H)) >>> cond (I H) (O H)'
 assert gate.compact(gate.definition(port,'canonical_scalar_normalize'))==gate.compact(expected)
 expected='Bit.or (@is_zero_word_spec 8 term) (((unit >>> Alg.scribe canonical_group_word) &&& iden) >>> @equality_spec (Word 8) term)'
 assert gate.compact(gate.definition(zero,'canonical_scalar_is_zero'))==gate.compact(expected)
 return 2

if __name__ == '__main__':
 p=argparse.ArgumentParser()
 p.add_argument('--repo',type=Path,required=True)
 p.add_argument('--source',type=Path,required=True)
 p.add_argument('--coq',type=Path,required=True)
 a=p.parse_args()
 if check(a.repo,a.source,a.coq)!=2: raise ValueError('unexpected scope')
 hashes={str(path):hashlib.sha256(path.read_bytes()).hexdigest() for path in
   [a.repo/f for f in files]+[a.source/f for f in ports]}
 print(json.dumps({'literal_scalar_ports':2,'literal_scalar_programs':True,
   'formal_parametricity':'OriginalC.jet_secp_scalar_canonical_parametric',
   'public_coverage_added':0,'hashes':hashes},indent=2))
