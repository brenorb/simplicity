"""In-memory parser fixtures; never edits proof or audit inputs."""
import importlib.util
from pathlib import Path
import sys
sys.dont_write_bytecode=True
here=Path(__file__).resolve().parent
def load(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod);return mod
review=load('review',here/'review-preliminary.py')
parser=load('assumptions',here.parent/'gej-predicate/review-preliminary.py')
class Text:
    def __init__(self,s):self.s=s
    def read_text(self):return self.s
def rejected(fn):
    try:fn()
    except ValueError:return
    raise AssertionError('bad fixture accepted')
rs=[['C.example','pair']]
assert 'pair' in review.types('@pair ?A ?B\n     : forall a, a = a\nwhere\n?A : [ |- Type]\n',rs)
assert len(review.definitions('Variant field : Set :=\n ctor : field.\nArguments ctor\nlimbs =\n fun f => f\n',[['C.example','field'],['C.example','limbs']]))==2
assert review.retained('ab...cd','abXYZcd')
assert not review.retained('ab...cd','abXYZce')
assert not review.retained('cd...ab','abXYZcd')
rejected(lambda:review.types('unrelated\n : True\n',rs))
rejected(lambda:review.types('pair\n : True\npair\n : True\n',rs))
rejected(lambda:review.definitions('field =\n 0\n',[['C.example','field'],['C.example','limbs']]))
rejected(lambda:review.definitions('field =\n 0\nfield =\n 0\n',[['C.example','field']]))
closed='JET_ASSUMPTIONS C.example.pair\nClosed under the global context\n'
axioms='JET_ASSUMPTIONS C.example.pair\nAxioms:\nClassical_Prop.classic : forall P : Prop, or P (not P)\n'
wanted={'C.example.pair'}
assert parser.assumptions(Text(closed),wanted)=={'C.example.pair':set()}
assert parser.assumptions(Text(axioms),wanted)=={'C.example.pair':{'Classical_Prop.classic'}}
for bad in [closed+closed,'','JET_ASSUMPTIONS C.example.pair\n',
            'JET_ASSUMPTIONS C.example.pair\nAxioms:\n',
            axioms.replace('Classical_Prop.classic','New.assumption'),
            closed.replace('C.example.pair','C.example.wrong'),
            'Axioms:\n'+closed]:
    rejected(lambda bad=bad:parser.assumptions(Text(bad),wanted))
print('Preliminary review fixtures passed: implicit headers, records, ellipsis diagnostics; 11 malformed reports rejected')
