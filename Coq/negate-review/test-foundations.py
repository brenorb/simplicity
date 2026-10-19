"""In-memory conversion/type/notation and inactive-source mutation fixtures."""
import argparse
import importlib.machinery
import importlib.util
from pathlib import Path
from types import SimpleNamespace

p = argparse.ArgumentParser()
p.add_argument('--repo', required=True)
p.add_argument('--candidates', required=True)
args = p.parse_args()
path = Path(__file__).with_name('check-foundations.py.source')
if not path.exists(): path = path.with_suffix('')
loader = importlib.machinery.SourceFileLoader('foundations', str(path))
spec = importlib.util.spec_from_loader(loader.name, loader)
gate = importlib.util.module_from_spec(spec)
loader.exec_module(gate)
parser, sources = gate.load(args.repo, args.candidates, path.parent)
assert gate.check(parser, sources)
mutations = [
    ('hs_word', 'type Vector2 x = (x,x)', 'type Vector2 x = Either x x'),
    ('hs_word', 'type Word256 = Vector256 Bit', 'type Word256 = Vector128 Bit'),
    ('hs_word', 'type Word512 = Vector512 Bit', 'type Word512 = Vector256 Bit'),
    ('hs_word', 'word256 = vector256', 'word256 = vector128'),
    ('hs_word', 'toWord256 = toWord word256', 'toWord256 = toWord word128'),
    ('hs_word', 'put (i `div` 2)', 'put (i `div` 4)'),
    ('hs_word', 'toBit (odd i)', 'toBit (even i)'),
    ('hs_word', 'return (a, b)', 'return (b, a)'),
    ('hs_word', 'vectorComp v SingleV = v', 'vectorComp v SingleV = DoubleV v'),
    ('hs_bit', 'toBit False = Left ()', 'toBit False = Right ()'),
    ('hs_bit', 'type Bit = Either () ()', 'type Bit = Bool'),
    ('conversion', 'z / 2', 'z / 4'),
    ('conversion', 'haskell_word_state n rest', 'haskell_word_state n z'),
    ('conversion', '((hi, lo), final)', '((lo, hi), final)'),
    ('coq_word', 'Prod rec rec', 'Sum rec rec'),
    ('coq_word', 'if Z.odd z then Bit.one else Bit.zero', 'if Z.odd z then Bit.zero else Bit.one'),
    ('coq_word', 'z / two_power_nat (bitSize b)', 'z / two_power_nat (bitSize a)'),
    ('hs_generic', 'injl (go l v)', 'injr (go l v)'),
    ('coq_alg', 'pair (scribe (fst b)) (scribe (snd b))', 'pair (scribe (snd b)) (scribe (fst b))'),
    ('hs_core', 'oh = take iden', 'oh = drop iden'),
    ('coq_alg', 'Notation "\'O\' x" := (take x)', 'Notation "\'O\' x" := (drop x)'),
    ('hs_word', 'toWord256 = toWord word256', '{- toWord256 = toWord word256 -}'),
    ('coq_word', 'Definition Word := Vector Bit.', '(* (* nested *) Definition Word := Vector Bit. *)'),
]
for bits in (2, 4, 8, 16, 32, 64, 128, 256, 512):
    mutations.append(('hs_word', 'vector'+str(bits)+' = DoubleV vector'+str(bits//2),
                      'vector'+str(bits)+' = DoubleV vector'+str(bits)))
for key, old, new in mutations:
    assert old in sources[key], (key, old)
    changed = dict(sources)
    changed[key] = changed[key].replace(old, new)
    # Same active-source parser as the ordinary file-loading path.
    text = changed[key]
    changed[key] = parser.read_code(SimpleNamespace(
        suffix='.hs' if key.startswith('hs_') else '.v', read_text=lambda: text))
    try:
        gate.check(parser, changed)
    except ValueError:
        pass
    else:
        raise AssertionError('accepted foundation mutation '+key+' '+old)
print(str(len(mutations))+' conversion/type/scribe/notation mutations rejected')
