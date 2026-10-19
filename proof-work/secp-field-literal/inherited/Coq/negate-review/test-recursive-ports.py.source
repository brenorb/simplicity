"""In-memory typed-port, implementation and nested-comment negative fixtures."""
import argparse
import importlib.machinery
import importlib.util
from pathlib import Path

p = argparse.ArgumentParser()
p.add_argument('--repo', required=True)
p.add_argument('--candidates', required=True)
args = p.parse_args()
path = Path(__file__).with_name('check-recursive-ports.py.source')
if not path.exists(): path = path.with_suffix('')
loader = importlib.machinery.SourceFileLoader('recursive_gate', str(path))
spec = importlib.util.spec_from_loader(loader.name, loader)
gate = importlib.util.module_from_spec(spec)
loader.exec_module(gate)
module = gate.parser(args.repo)
reference, sources = gate.load(args.repo, args.candidates)
assert gate.check(module, reference, sources) == (48, 16)
mutations = []
for r in reference['coq']:
    key = 'Coq/'+r['path']
    code = gate.active(module, key, sources[key])
    decl = gate.declaration(code, r['name']).rstrip()
    # Removing each active port must fail even if a nested comment retains it.
    assert decl in sources[key], r['name']
    mutations.append((key, decl, '(* (* retained text is not code *) '+decl+' *)'))
for r in reference['haskell']:
    text = sources[r['path']]
    begin, end = text.index(r['start']), (len(text) if r['end'] is None else text.index(r['end']))
    region = text[begin:end]
    mutations.append((r['path'], region, '\n{- '+region+' -}\n'))
targeted = [
    ('Coq/Simplicity/Bit.v', 'case (drop els) (drop thn)', 'case (drop thn) (drop els)'),
    ('Coq/Simplicity/Bit.v', 'cond false true', 'cond true false'),
    ('Coq/Simplicity/Bit.v', 'cond (cond true iden) (cond iden false)', 'cond (cond false iden) (cond iden true)'),
    ('Coq/Simplicity/Word.v', 'maj &&& xor3', 'xor3 &&& maj'),
    ('Coq/C/jet_subtract_spec.v', '(Bit.not (AC.take AC.iden))', '(AC.take AC.iden)'),
    ('Coq/C/jet_order_spec.v', '(AC.take AC.iden)', '(AC.drop AC.iden)'),
    ('Coq/C/jet_predicate_spec.v', 'if all then Bit.and hi lo else Bit.or hi lo', 'if all then Bit.or hi lo else Bit.and hi lo'),
    ('Coq/C/jet_test_value_spec.v', '@predicate_spec n Datatypes.false term', '@predicate_spec n Datatypes.true term'),
    ('Haskell/Core/Simplicity/Programs/Bit.hs', 'not t = t &&& unit >>> cond false true', 'not t = t &&& unit >>> cond true false'),
    ('Haskell/Core/Simplicity/Programs/Arith.hs', 'lt w = subtract w >>> oh', 'lt w = subtract w >>> ih'),
    ('Coq/Simplicity/Word.v', '| 0 => fullMultiplierBit', '| 0 => iden'),
    ('Coq/Simplicity/Word.v', 'buildFullMultiplier fullMultiplier', 'buildFullMultiplier iden'),
    ('Coq/C/jet_division_core_spec.v', 'Bit.cond (I H &&& O H)', 'Bit.cond (O H &&& I H)'),
    ('Coq/C/jet_division_core_spec.v', '@division_pre_shift_spec n 0 term', '@division_pre_shift_spec n 1 term'),
    ('Coq/C/jet_division_normalize_spec.v', '(eq_sym (Nat.add_succ_r m n))', '(eq_sym (Nat.add_succ_r n m))'),
    ('Coq/C/jet_division_shift_step.v', '@full_left_word_spec n (S m) term', '@full_left_word_spec n m term'),
    ('Coq/C/jet_division_shift_step.v', '@full_right_word_spec n m term', '@full_left_word_spec n m term'),
    ('Coq/C/jet_full_shift_spec.v', '@Word.full_left_shift1 (Word n) m term', '@Word.full_right_shift1 (Word n) m term'),
    ('Haskell/Core/Simplicity/Programs/Arith.hs', 'zero_case = ih &&& oh', 'zero_case = oh &&& ih'),
    ('Haskell/Core/Simplicity/Programs/Arith.hs', 'rec = div3n2n w', 'rec = div3n2n (DoubleV w)'),
    ('Haskell/Core/Simplicity/Programs/Arith.hs', '>>> divPreShift w v\'', '>>> divPreShift w v'),
    ('Haskell/Core/Simplicity/Programs/Arith.hs', 'full_shift w (vectorComp w v\') >>> oh', 'full_shift w (vectorComp w v\') >>> ih'),
]
mutations.extend(targeted)
for key, old, new in mutations:
    assert old in sources[key], (key, old)
    changed = dict(sources)
    changed[key] = changed[key].replace(old, new, 1)
    try:
        gate.check(module, reference, changed)
    except ValueError:
        pass
    else:
        raise AssertionError('accepted recursive mutation '+key+' '+old)
print(str(len(mutations))+' recursive port/implementation mutations rejected')
