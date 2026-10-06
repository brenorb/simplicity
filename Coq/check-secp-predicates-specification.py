"""Check literal canonical field predicate programs and complete jet contracts.

This supplements kernel and execution checks; it does not establish C execution.
"""
import importlib.util
import re
import os
import sys
from pathlib import Path

sys.dont_write_bytecode = True
COQ = Path(__file__).resolve().parent
REPO = Path(os.environ.get("JET_C_REPO", COQ.parent))


def read_code(path):
    """Discard nested comments before checking active source fragments."""
    source = path.read_text()
    opening, closing = ('(*', '*)') if path.suffix == '.v' else ('{-', '-}')
    result, depth, i, quoted = [], 0, 0, False
    while i < len(source):
        if depth:
            if source.startswith(opening, i):
                depth += 1; i += 2
            elif source.startswith(closing, i):
                depth -= 1; i += 2
            else:
                if source[i] == '\n': result.append('\n')
                i += 1
        elif quoted:
            result.append(source[i])
            if source[i] == '\\' and i + 1 < len(source):
                result.append(source[i+1]); i += 2; continue
            if source[i] == '"': quoted = False
            i += 1
        elif source.startswith(opening, i):
            depth = 1; result.append(' '); i += 2
        elif path.suffix == '.hs' and source.startswith('--', i):
            end = source.find('\n', i)
            i = len(source) if end < 0 else end
        else:
            quoted = source[i] == '"'
            result.append(source[i]); i += 1
    if depth: raise ValueError('unterminated comment: '+str(path))
    return ''.join(result)

def compact(text):
    return re.sub(r"\s+", "", text)


def definition(source, name):
    m = re.search(rf"\b(?:Definition|Fixpoint)\s+{name}\b.*?:=(.*?)\.\s*(?:\n|$)", source, re.S)
    if not m:
        raise ValueError(f"missing definition: {name}")
    return m[1]


def require(text, fragment, label):
    if compact(fragment) not in compact(text):
        raise ValueError(f"predicate correspondence differs: {label}")


def exact_program(implementation, name, next_name, expected):
    m = re.search(rf"\b{name}\s*=(.*?)\n\s*,\s*{next_name}\b", implementation, re.S)
    if not m or compact(m[1]) != compact(expected):
        raise ValueError(f"canonical {name} program differs")


def check(coq=COQ, repo=REPO):
    coq, repo = Path(coq), Path(repo)
    spec = importlib.util.spec_from_file_location('normalize_gate', coq/'check-secp-normalize-specification.py')
    normalize = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(normalize)
    normalize.check(coq, repo)
    # Freeze the actual recursive ports used by these canonical programs.
    ports = [
        ('Simplicity/Bit.v', 'false', 'injl unit'),
        ('Simplicity/Bit.v', 'true', 'injr unit'),
        ('Simplicity/Bit.v', 'cond', 'case (drop els) (drop thn)'),
        ('Simplicity/Bit.v', 'not', 't &&& unit >>> cond false true'),
        ('Simplicity/Bit.v', 'or', 's &&& iden >>> cond true t'),
        ('Simplicity/Word.v', 'build_rightmost', 'drop rec'),
        ('Simplicity/Word.v', 'rightmost', 'match n with | 0 => iden | S n => build_rightmost rightmost end'),
        ('C/jet_test_value_spec.v', 'is_zero_word_spec', 'Bit.not (@predicate_spec n Datatypes.false term)'),
        ('C/jet_predicate_spec.v', 'predicate_spec',
         """match n with
         | O => @Alg.Core.Combinators.iden Bit term
         | S n =>
             let hi := @Alg.Core.Combinators.take (Word n) (Word n) Bit term (predicate_spec n all) in
             let lo := @Alg.Core.Combinators.drop (Word n) (Word n) Bit term (predicate_spec n all) in
             if all then Bit.and hi lo else Bit.or hi lo
         end"""),
        ('C/jet_equality_spec.v', 'equality_spec',
         """match A with
         | Ty.Unit => Bit.true
         | Ty.Sum L R => Alg.Core.Combinators.case
             (Alg.Core.Combinators.swapP >>* Alg.Core.Combinators.case (equality_spec L) Bit.false)
             (Alg.Core.Combinators.swapP >>* Alg.Core.Combinators.case Bit.false (equality_spec R))
         | Ty.Prod L R =>
             ((O O H &&* I O H >>* equality_spec L) &&* (O I H &&* I I H))
               >>* Bit.cond (equality_spec R) Bit.false
         end"""),
    ]
    for path, name, expected in ports:
        if compact(definition(read_code(coq/path), name)) != compact(expected):
            raise ValueError('canonical predicate dependency differs: '+name)
    hs_bit = read_code(repo/'Haskell/Core/Simplicity/Programs/Bit.hs')
    for fragment in ['false = injl unit', 'true = injr unit',
                     'cond thn els = match (drop els) (drop thn)',
                     'not t = t &&& unit >>> cond false true',
                     'or s t = s &&& iden >>> cond true t']:
        require(hs_bit, fragment, 'Bit combinator '+fragment.split('=')[0].strip())
    catalog = read_code(repo/'Haskell/Core/Simplicity/CoreJets.hs')
    program = read_code(repo/'Haskell/Core/Simplicity/Programs/LibSecp256k1.hs')
    arith = read_code(repo/'Haskell/Core/Simplicity/Programs/Arith.hs')
    word = read_code(repo/'Haskell/Core/Simplicity/Programs/Word.hs')
    generic = read_code(repo/'Haskell/Core/Simplicity/Programs/Generic.hs')
    require(word,'rightmost SingleV = iden','rightmost base')
    require(word,'rightmost (DoubleV v) = drop (rightmost v)','rightmost recursion')
    require(word,'some SingleV = iden','some base')
    require(word,'some (DoubleV w) = or (take rec) (drop rec)\n where\n  rec = some w','some recursion')
    require(generic,'eq = go reify','generic equality dispatch')
    require(generic,'go OneR = true','generic equality unit')
    require(generic,'go (SumR l r) = match (swapP >>> match (go l) false) (swapP >>> match false (go r))','generic equality sum')
    require(generic,'go (ProdR a1 a2) = pair (pair (take (take iden)) (drop (take iden)) >>> (go a1)) (pair (take (drop iden)) (drop (drop iden))) >>> cond (go a2) false','generic equality product')
    impl = program.split('lib@Lib{..} = Lib {',1)[1]
    require(program,'lsb256 = Arith.lsb word256','lsb specialization')
    require(arith,'lsb w = rightmost w','lsb recursion')
    require(arith,'is_zero w = not (some w)','is_zero composition')
    for constructor, name in [('FeIsOdd','fe_is_odd'),('FeIsZero','fe_is_zero')]:
        require(catalog,f'{constructor} :: Secp256k1Jet Secp256k1.FE Bit',name+' jet type')
        require(catalog,f'specificationSecp256k1 {constructor} = Secp256k1.{name}',name+' dispatch')
    exact_program(impl,'fe_is_odd','fe_add','fe_normalize >>> lsb256')
    exact_program(impl,'fe_is_zero','fe_is_odd','or (Arith.is_zero word256) ((unit >>> scribeFeOrder) &&& iden >>> eq)')
    expected = {
        'odd': '@canonical_fe_normalize term >>> @Word.rightmost Bit 8 term',
        'zero': 'Bit.or (@is_zero_word_spec 8 term) (((unit >>> Alg.scribe canonical_field_word) &&& iden) >>> @equality_spec (Word 8) term)',
    }
    for suffix in ['odd','zero']:
        port = read_code(coq/f'C/jet_secp_canonical_{suffix}.v')
        name = f'canonical_fe_is_{suffix}'
        require(port,f'{name} {{term : Alg.Core.Algebra}} : term (Word 8) Bit',name+' domain')
        if compact(definition(port,name)) != compact(expected[suffix]):
            raise ValueError(name+' literal port differs')
        local = read_code(coq/f'C/jet_secp_{suffix}_local.v')
        statement = re.search(rf'Theorem fe_{suffix}_local_spec\s*:(.*?)\bProof\.',local,re.S)
        want = f'secp_jet_local_spec f_simplicity_fe_is_{suffix} (Word 8) Bit (@{name} Alg.CoreFunSem).'
        if not statement or compact(statement[1]) != compact(want):
            raise ValueError(name+' full public contract differs')
    return 2


if __name__ == "__main__":
    try:
        check()
    except (ValueError, OSError, IndexError) as error:
        raise SystemExit(str(error))
    print("canonical field predicate programs, recursive ports and full frame contracts match")
