"""Reviewed word conversion, type, scribe and basic combinator correspondence.

This is a source gate, not a formal translation of Haskell. The state algorithm
has a separate closed Coq equivalence proof. No update mode is provided.
"""
import argparse
import importlib.machinery
import importlib.util
import re
from pathlib import Path


def helpers(directory):
    path = Path(directory).parent/'source-review.py'
    loader = importlib.machinery.SourceFileLoader('foundation_parser', str(path))
    spec = importlib.util.spec_from_loader(loader.name, loader)
    module = importlib.util.module_from_spec(spec)
    loader.exec_module(module)
    return module


def load(repo, candidates, gates):
    h = helpers(gates)
    p = h.parser(repo)
    paths = {
        'hs_word': Path(repo)/'Haskell/Core/Simplicity/Ty/Word.hs',
        'hs_bit': Path(repo)/'Haskell/Core/Simplicity/Ty/Bit.hs',
        'hs_generic': Path(repo)/'Haskell/Core/Simplicity/Programs/Generic.hs',
        'hs_core': Path(repo)/'Haskell/Core/Simplicity/Term/Core.hs',
        'coq_word': Path(repo)/'Coq/Simplicity/Word.v',
        'coq_alg': Path(repo)/'Coq/Simplicity/Alg.v',
        'conversion': Path(candidates)/'jet_haskell_word_conversion.v',
    }
    return p, {k: h.active(p, path, path.read_text()) for k, path in paths.items()}


def check(p, sources):
    def need(key, text):
        if p.compact(text) not in p.compact(sources[key]):
            raise ValueError('foundation correspondence differs '+key+' '+text)
    need('hs_word', 'type Vector1 x = x')
    need('hs_word', 'type Vector2 x = (x,x)')
    need('hs_word', 'type Vector4 x = Vector2 (Vector2 x)')
    for bits in (8, 16, 32, 64, 128, 256, 512):
        need('hs_word', 'type Vector'+str(bits)+' x = Vector2 (Vector'+str(bits//2)+' x)')
    for bits in (256, 512):
        need('hs_word', 'type Word'+str(bits)+' = Vector'+str(bits)+' Bit')
        need('hs_word', 'word'+str(bits)+' = vector'+str(bits))
    need('hs_word', 'toWord256 = toWord word256')
    need('hs_word', 'vector1 = SingleV')
    for bits in (2, 4, 8, 16, 32, 64, 128, 256, 512):
        need('hs_word', 'vector'+str(bits)+' = DoubleV vector'+str(bits//2))
    need('hs_word', 'vectorComp v SingleV = v')
    need('hs_word', 'vectorComp v (DoubleV w) = DoubleV (vectorComp v w)')
    need('hs_bit', 'type Bit = Either () ()')
    need('hs_bit', 'toBit False = Left ()')
    need('hs_bit', 'toBit True = Right ()')
    match = re.search(r'\ntoWord w i =(.*?)\nfromWord1 ::', sources['hs_word'], re.S)
    expected = '''evalState (go w) i
      where
        go :: Word a -> State Integer a
        go SingleV = do
          i <- get
          put (i `div` 2)
          return $ toBit (odd i)
        go (DoubleV w) = do
          b <- go w
          a <- go w
          return (a, b)'''
    if not match or p.compact(match[1]) != p.compact(expected):
        raise ValueError('Haskell low-first conversion differs')
    expected = '''match n as n return Ty.tySem (Word n) * Z with
      | O => ((if Z.odd z then Bit.one else Bit.zero), z / 2)
      | S n => let '(lo, rest) := haskell_word_state n z in
               let '(hi, final) := haskell_word_state n rest in
               ((hi, lo), final)
      end'''
    if p.compact(p.definition(sources['conversion'].replace('Fixpoint haskell_word_state',
            'Definition haskell_word_state'), 'haskell_word_state')) != p.compact(expected):
        raise ValueError('Coq low-first state port differs')
    need('coq_word', 'Fixpoint Vector X (n : nat) := match n with | 0 => X | S n => let rec := Vector X n in Prod rec rec end.')
    need('coq_word', 'Definition Word := Vector Bit.')
    need('coq_word', 'Let BitFromZ (z : Z) : Bit := if Z.odd z then Bit.one else Bit.zero.')
    need('coq_word', 'Let PairFromZ (z : Z) : a * b := (fromZ (z / two_power_nat (bitSize b)), fromZ z).')
    need('hs_generic', '''scribe = go reify
      where
        go :: (Core term, TyC a, TyC b) => TyReflect b -> b -> term a b
        go OneR () = unit
        go (SumR l _) (Left v) = injl (go l v)
        go (SumR _ r) (Right v) = injr (go r v)
        go (ProdR b1 b2) (v1, v2) = pair (go b1 v1) (go b2 v2)''')
    if p.compact(p.definition(sources['coq_alg'], 'scribe').replace(' ', '')) != p.compact('''match B with
      | Unit => fun _ _ => unit
      | Sum BL BR => fun b => match b with
        | inl l => fun _ => injl (scribe l)
        | inr r => fun _ => injr (scribe r) end
      | Prod B1 B2 => fun b _ => pair (scribe (fst b)) (scribe (snd b)) end'''):
        raise ValueError('Coq structural scribe differs')
    for text in ['(>>>) = comp', '(&&&) = pair', 'oh = take iden', 'ih = drop iden']:
        need('hs_core', text)
    for text in ['Notation "s &&& t" := (pair s t)', 'Notation "s >>> t" := (comp s t)',
                 'Notation "\'H\'" := iden', 'Notation "\'O\' x" := (take x)',
                 'Notation "\'I\' x" := (drop x)']:
        need('coq_alg', text)
    return True


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--repo', required=True)
    p.add_argument('--candidates', required=True)
    p.add_argument('--gates', default=str(Path(__file__).parent))
    args = p.parse_args()
    parser, sources = load(args.repo, args.candidates, args.gates)
    check(parser, sources)
    print('Reviewed conversion/types/scribe/basic combinator mappings match')
