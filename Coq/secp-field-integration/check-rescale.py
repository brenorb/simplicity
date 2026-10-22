"""Point and field square-root literal ports/public contracts; not C execution.

Reuse the existing source parser.  Field multiply/square dependencies retain
their own gates; this checks the new projections, cube and zinv composition.
"""
import importlib.util
import os
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
COQ = Path(__file__).resolve().parents[1]
REPO = Path(os.environ.get("JET_C_REPO", COQ.parent))
sp = importlib.util.spec_from_file_location("rescale_source_parser", COQ / "check-secp-predicates-specification.py")
p = importlib.util.module_from_spec(sp)
sp.loader.exec_module(p)


def check(s):
    p.require(s["catalog"], "GejRescale :: Secp256k1Jet (Secp256k1.GEJ,Secp256k1.FE) Secp256k1.GEJ", "GejRescale type")
    p.require(s["catalog"], "specificationSecp256k1 GejRescale = Secp256k1.gej_rescale", "GejRescale dispatch")
    for declaration in ["type FE = Word256", "type GE = (FE, FE)", "type GEJ = (GE, FE)"]:
        p.require(s["types"], declaration, "point/field representation")
    impl = s["program"].split("lib@Lib{..} = Lib {", 1)[1]
    p.exact_program(impl, "gej_rescale", "gej_normalize",
                    "(ooh &&& ih >>> zinv) &&& (oih &&& ih >>> fe_multiply)")
    for name, expected in [
        ("fe_cube", "iden &&& fe_square >>> fe_multiply"),
        ("zinv", "(ooh &&& drop fe_square >>> fe_multiply) &&& (oih &&& drop fe_cube >>> fe_multiply)"),
    ]:
        definitions = re.findall(r"^\s*" + name + r"\s*=([^\n]*)$", impl, re.M)
        if len(definitions) != 1 or p.compact(definitions[0]) != p.compact(expected):
            raise ValueError("canonical rescale dependency differs: " + name)
    for name, expected in [
        ("literal_fe_cube", "iden &&& @literal_fe_square term >>> @literal_fe_multiply term"),
        ("literal_gej_zinv", "(O (O H) &&& I (@literal_fe_square term) >>> @literal_fe_multiply term) &&& "
                             "(O (I H) &&& I (@literal_fe_cube term) >>> @literal_fe_multiply term)"),
        ("literal_gej_rescale", "(O (O H) &&& I H >>> @literal_gej_zinv term) &&& "
                                "(O (I H) &&& I H >>> @literal_fe_multiply term)"),
    ]:
        if p.compact(p.definition(s["port"], name)) != p.compact(expected):
            raise ValueError("literal rescale tree differs: " + name)
    statement = re.search(r"Theorem gej_rescale_literal_local_spec\s*:(.*?)\bProof\.", s["jet"], re.S)
    expected = "secp_jet_local_spec f_simplicity_gej_rescale " \
        "(Ty.Prod (Ty.Prod (Ty.Prod (Word 8) (Word 8)) (Word 8)) (Word 8)) " \
        "(Ty.Prod (Ty.Prod (Word 8) (Word 8)) (Word 8)) (@literal_gej_rescale Alg.CoreFunSem)."
    if not statement or p.compact(statement[1]) != p.compact(expected):
        raise ValueError("GejRescale full public contract differs")


def check_double(s):
    for fragment in [
        "GejDouble :: Secp256k1Jet Secp256k1.GEJ Secp256k1.GEJ",
        "specificationSecp256k1 GejDouble = Secp256k1.gej_double",
        "implementationSecp256k1 GejDouble = FFI.gej_double",
    ]:
        p.require(s["catalog"], fragment, "GejDouble catalog")
    for declaration in ["type FE = Word256", "type GE = (FE, FE)", "type GEJ = (GE, FE)"]:
        p.require(s["types"], declaration, "doubling representation")
    impl = s["program"].split("lib@Lib{..} = Lib {", 1)[1]
    p.exact_program(impl, "fe_halve", "fe_invert",
                    "(false &&& iden) >>> full_shift word1 word256 >>> ih &&& oh "
                    ">>> cond ((unit >>> scribeFeHalf) &&& iden >>> fe_add) iden")
    p.require(s["program"], "scribeFeHalf = scribe256 ((LibSecp256k1.fieldOrder + 1) `div` 2)", "field half constant")
    p.require(s["program"], "fe_multiplyInt i = scribe256 (i `mod` LibSecp256k1.fieldOrder) &&& iden >>> fe_multiply", "field integer multiplier")
    p.exact_program(impl, "gej_double", "gej_add_ex", """
      let
        body = (take (oh &&& (take fe_square >>> fe_multiplyInt 3 >>> fe_halve) &&& drop fe_square)
          >>> ((iih &&& oh >>> fe_multiply >>> fe_negate) &&& ih)
          >>> (((take (fe_multiplyInt 2) &&& drop (take fe_square) >>> fe_add) &&& oh) &&& ih)
          >>> (ooh &&& ((ioh &&& (take fe_add) >>> fe_multiply) &&& drop (drop fe_square) >>> fe_add >>> fe_negate)))
          &&& (oih &&& ih >>> fe_multiply)
      in gej_is_infinity &&& iden >>> cond (unit >>> gej_infinity) body
    """)
    expected_ports = {
        "double_half_word": "@fromZ (WordToZ 8) ((feP+1)/2)",
        "double_multiplier_word": "@fromZ (WordToZ 8) (i mod feP)",
        "literal_fe_multiply_int": "Alg.scribe (double_multiplier_word i) &&& iden >>> @literal_fe_multiply term",
        "literal_fe_halve": "(Bit.false &&& iden) >>> @Word.full_right_shift1 Bit 8 term >>> I H &&& O H >>> "
                            "Bit.cond ((unit >>> Alg.scribe double_half_word) &&& iden >>> @literal_fe_add term) iden",
        "literal_gej_double_body": """
          (O (O H &&& ((O (@literal_fe_square term) >>> @literal_fe_multiply_int 3 term >>> @literal_fe_halve term)
              &&& I (@literal_fe_square term)))
            >>> ((I (I H) &&& O H >>> @literal_fe_multiply term >>> @literal_fe_negate term) &&& I H)
            >>> (((O (@literal_fe_multiply_int 2 term) &&& I (O (@literal_fe_square term))
              >>> @literal_fe_add term) &&& O H) &&& I H)
            >>> (O (O H) &&& ((I (O H) &&& O (@literal_fe_add term) >>> @literal_fe_multiply term)
              &&& I (I (@literal_fe_square term)) >>> @literal_fe_add term >>> @literal_fe_negate term)))
            &&& (O (I H) &&& I H >>> @literal_fe_multiply term)
        """,
        "literal_gej_double": "@literal_gej_is_infinity term &&& iden >>> "
                              "Bit.cond (unit >>> @literal_gej_infinity term) (@literal_gej_double_body term)",
    }
    for name, expected in expected_ports.items():
        if p.compact(p.definition(s["double_port"], name)) != p.compact(expected):
            raise ValueError("literal doubling tree differs: " + name)
    statement = re.search(r"Theorem gej_double_literal_local_spec\s*:(.*?)\bProof\.", s["double_jet"], re.S)
    expected = "secp_jet_local_spec f_simplicity_gej_double " \
        "(Ty.Prod (Ty.Prod (Word 8) (Word 8)) (Word 8)) " \
        "(Ty.Prod (Ty.Prod (Word 8) (Word 8)) (Word 8)) (@literal_gej_double Alg.CoreFunSem)."
    if not statement or p.compact(statement[1]) != p.compact(expected):
        raise ValueError("GejDouble full public contract differs")


def check_addition_ports(s):
    """Freeze addition routing used by the C mixed-addition proof.

    No public addition contract or coverage is asserted by this helper check.
    The existing field/doubling checks retain responsibility for callees.
    """
    impl = s["program"].split("lib@Lib{..} = Lib {", 1)[1]
    p.exact_program(impl, "gej_add_ex", "gej_add", """
      let
      body = ((oooh &&& (iih >>> fe_square) >>> fe_multiply) &&& (drop (take (take fe_negate)) &&& (oih >>> fe_square) >>> fe_multiply) >>> fe_add &&& oh)
      &&& ((ooih  &&& (iih >>> fe_cube) >>> fe_multiply)   &&& (drop (take (drop fe_negate)) &&& (oih >>> fe_cube) >>> fe_multiply) >>> fe_add &&& oh) &&&
      (oh &&& drop (drop fe_negate))
      >>> take (take fe_is_zero) &&& iden >>> cond (drop zeroH) nonZeroH
      zeroH = take (take fe_is_zero) &&& ioh >>> cond (oih &&& gej_double) (unit >>> fe_zero &&& gej_infinity)
      nonZeroH = (ooh &&& ((ooh &&& drop ioih >>> fe_multiply) &&& iiih)) &&& ((take (take fe_square) &&& oih >>> fe_multiply) &&& ioh)
      >>> ((ooh &&& oiih >>> fe_multiply) &&& take (drop fe_multiply)) &&& (((ooh >>> fe_cube) &&& ioh) &&& iih)
      >>> ooh &&& drop ((((take (oh &&& drop (fe_multiplyInt (-2)) >>> fe_add) &&& drop (take fe_square) >>> fe_add) &&& oih) &&& (ioh &&& (ooh &&& iih >>> fe_multiply)))
      >>> ooh &&& (iih &&& (ioh &&& take (oh &&& drop fe_negate >>> fe_add) >>> fe_multiply) >>> fe_add))
      &&& oih
      in
      take gej_is_infinity &&& iden
      >>> cond ((unit >>> fe_zero) &&& (drop (take (take fe_normalize &&& drop fe_normalize) &&& (drop fe_normalize))))
      (drop gej_is_infinity &&& iden
      >>> cond ((unit >>> fe_one) &&& (take (take (take fe_normalize &&& drop fe_normalize) &&& (drop fe_normalize)))) body)
    """)
    for name, next_name, expected in [
        ("gej_add", "gej_ge_add_ex", "gej_add_ex >>> ih"),
        ("gej_ge_add_ex", "gej_ge_add", "oh &&& (ih &&& (unit >>> fe_one)) >>> gej_add_ex"),
        ("gej_ge_add", "gej_scale_lambda", "gej_ge_add_ex >>> ih"),
    ]:
        p.exact_program(impl, name, next_name, expected)
    expected_ports = {
        "literal_gej_add_ex": """
          let zeroH := O (O (@canonical_fe_is_zero term)) &&& I O H >>> Bit.cond (O I H &&& (@literal_gej_double term)) (unit >>> (@literal_fe_zero256 term) &&& (@literal_gej_infinity term)) in
          let nonZeroH := (O O H &&& ((O O H &&& I I O I H >>> (@literal_fe_multiply term)) &&& I I I H)) &&& ((O (O (@literal_fe_square term)) &&& O I H >>> (@literal_fe_multiply term)) &&& I O H)
          >>> ((O O H &&& O I I H >>> (@literal_fe_multiply term)) &&& O (I (@literal_fe_multiply term))) &&& (((O O H >>> (@literal_fe_cube term)) &&& I O H) &&& I I H)
          >>> O O H &&& I ((((O (O H &&& I ((@literal_fe_multiply_int (-2) term)) >>> (@literal_fe_add term)) &&& I (O (@literal_fe_square term)) >>> (@literal_fe_add term)) &&& O I H) &&& (I O H &&& (O O H &&& I I H >>> (@literal_fe_multiply term))))
          >>> O O H &&& (I I H &&& (I O H &&& O (O H &&& I (@literal_fe_negate term) >>> (@literal_fe_add term)) >>> (@literal_fe_multiply term)) >>> (@literal_fe_add term)))
          &&& O I H in
          let body := ((O O O H &&& (I I H >>> (@literal_fe_square term)) >>> (@literal_fe_multiply term)) &&& (I (O (O (@literal_fe_negate term))) &&& (O I H >>> (@literal_fe_square term)) >>> (@literal_fe_multiply term)) >>> (@literal_fe_add term) &&& O H)
          &&& ((O O I H  &&& (I I H >>> (@literal_fe_cube term)) >>> (@literal_fe_multiply term))   &&& (I (O (I (@literal_fe_negate term))) &&& (O I H >>> (@literal_fe_cube term)) >>> (@literal_fe_multiply term)) >>> (@literal_fe_add term) &&& O H) &&&
          (O H &&& I (I (@literal_fe_negate term)))
          >>> O (O (@canonical_fe_is_zero term)) &&& iden >>> Bit.cond (I zeroH) nonZeroH in
          O (@literal_gej_is_infinity term) &&& iden
          >>> Bit.cond ((unit >>> (@literal_fe_zero256 term)) &&& (I (O (O (@canonical_fe_normalize term) &&& I (@canonical_fe_normalize term)) &&& (I (@canonical_fe_normalize term)))))
          (I (@literal_gej_is_infinity term) &&& iden
          >>> Bit.cond ((unit >>> (@literal_fe_one256 term)) &&& (O (O (O (@canonical_fe_normalize term) &&& I (@canonical_fe_normalize term)) &&& (I (@canonical_fe_normalize term))))) body)
        """,
        "literal_gej_add": """
          @literal_gej_add_ex term >>> I H
        """,
        "literal_gej_ge_add_ex": """
          O H &&& (I H &&& (unit >>> @literal_fe_one256 term)) >>> @literal_gej_add_ex term
        """,
        "literal_gej_ge_add": """
          @literal_gej_ge_add_ex term >>> I H
        """,
    }
    for name, expected in expected_ports.items():
        if p.compact(p.definition(s["add_port"], name)) != p.compact(expected):
            raise ValueError("literal addition tree differs: " + name)


def check_mixed(s):
    check_addition_ports(s)
    for fragment in [
        "GejGeAdd :: Secp256k1Jet (Secp256k1.GEJ,Secp256k1.GE) Secp256k1.GEJ",
        "specificationSecp256k1 GejGeAdd = Secp256k1.gej_ge_add",
        "implementationSecp256k1 GejGeAdd = FFI.gej_ge_add",
    ]:
        p.require(s["catalog"], fragment, "GejGeAdd catalog")
    for declaration in ["type FE = Word256", "type GE = (FE, FE)", "type GEJ = (GE, FE)"]:
        p.require(s["types"], declaration, "mixed-addition representation")
    statement = re.search(r"Theorem gej_ge_add_literal_local_spec\s*:(.*?)\bProof\.", s["mixed_jet"], re.S)
    expected = "secp_jet_local_spec f_simplicity_gej_ge_add " \
        "(Ty.Prod (Ty.Prod (Ty.Prod (Word 8) (Word 8)) (Word 8)) (Ty.Prod (Word 8) (Word 8))) " \
        "(Ty.Prod (Ty.Prod (Word 8) (Word 8)) (Word 8)) (@literal_gej_ge_add Alg.CoreFunSem)."
    if not statement or p.compact(statement[1]) != p.compact(expected):
        raise ValueError("GejGeAdd full public contract differs")


def check_root_ports(s):
    """Check routing/counts of the fixed square-root program and its port."""
    for fragment in [
        "FeSquareRoot :: Secp256k1Jet Secp256k1.FE (Either () Secp256k1.FE)",
        "specificationSecp256k1 FeSquareRoot = Secp256k1.fe_square_root",
        "implementationSecp256k1 FeSquareRoot = FFI.fe_square_root",
    ]:
        p.require(s["catalog"], fragment, "FeSquareRoot catalog")
    p.require(s["types"], "type FE = Word256", "root field representation")
    impl = s["program"].split("lib@Lib{..} = Lib {", 1)[1]
    p.exact_program(impl, "fe_square_root", "fe_is_quad", """
      iden &&& tower
      >>> oh &&& drop ((oh &&& drop fe_square >>> fe_multiply) >>> fe_square >>> fe_square)
      >>> (take fe_negate &&& drop fe_square >>> fe_add >>> fe_is_zero) &&& ih
      >>> cond (injr iden) (injl unit)
    """)
    tower = re.search(r"\btower\s*=(.*?)\n\s*zinv\s*=", impl, re.S)
    expected_tower = """
iden &&& fe_cube
        >>> ih &&& (oh &&& drop fe_square >>> fe_multiply)
        >>> oh &&& ((ih &&& (oh &&& (drop (iden &&& (iden &&& (fe_square >>> fe_square >>> fe_square) >>> fe_multiply >>> fe_square >>> fe_square >>> fe_square) >>> fe_multiply) >>> fe_square >>> fe_square) >>> fe_multiply
                          >>> iden &&& foldr1 (>>>) (replicate 11 fe_square) >>> fe_multiply))
                 >>> ih &&& (oh &&& drop (iden &&& foldr1 (>>>) (replicate 22 fe_square) >>> fe_multiply
                                     >>> (iden &&& (iden &&& foldr1 (>>>) (replicate 44 fe_square) >>> fe_multiply
                                                 >>> iden &&& foldr1 (>>>) (replicate 88 fe_square) >>> fe_multiply
                                           >>> foldr1 (>>>) (replicate 44 fe_square)) >>> fe_multiply)
                                    >>> fe_square >>> fe_square >>> fe_square) >>> fe_multiply
                           >>> foldr1 (>>>) (replicate 23 fe_square)) >>> fe_multiply
                 >>> foldr1 (>>>) (replicate 5 fe_square))
    """
    if not tower or p.compact(tower[1]) != p.compact(expected_tower):
        raise ValueError("canonical square-root tower differs")
    expected_ports = {
        "literal_fe_squares": """
match n with
 | Datatypes.O => iden
 | S k => match k with
   | Datatypes.O => @literal_fe_square term
   | S _ => @literal_fe_square term >>> @literal_fe_squares k term
   end
 end
        """,
        "literal_fe_tower": """
iden &&& (@literal_fe_cube term)
        >>> I H &&& (O H &&& I (@literal_fe_square term) >>> (@literal_fe_multiply term))
        >>> O H &&& ((I H &&& (O H &&& (I (iden &&& (iden &&& ((@literal_fe_square term) >>> (@literal_fe_square term) >>> (@literal_fe_square term)) >>> (@literal_fe_multiply term) >>> (@literal_fe_square term) >>> (@literal_fe_square term) >>> (@literal_fe_square term)) >>> (@literal_fe_multiply term)) >>> (@literal_fe_square term) >>> (@literal_fe_square term)) >>> (@literal_fe_multiply term)
                          >>> iden &&& (@literal_fe_squares 11 term) >>> (@literal_fe_multiply term)))
                 >>> I H &&& (O H &&& I (iden &&& (@literal_fe_squares 22 term) >>> (@literal_fe_multiply term)
                                     >>> (iden &&& (iden &&& (@literal_fe_squares 44 term) >>> (@literal_fe_multiply term)
                                                 >>> iden &&& (@literal_fe_squares 88 term) >>> (@literal_fe_multiply term)
                                           >>> (@literal_fe_squares 44 term)) >>> (@literal_fe_multiply term))
                                    >>> (@literal_fe_square term) >>> (@literal_fe_square term) >>> (@literal_fe_square term)) >>> (@literal_fe_multiply term)
                           >>> (@literal_fe_squares 23 term)) >>> (@literal_fe_multiply term)
                 >>> (@literal_fe_squares 5 term))
        """,
        "literal_fe_square_root": """
iden &&& @literal_fe_tower term
 >>> O H &&& I ((O H &&& I (@literal_fe_square term) >>> @literal_fe_multiply term)
               >>> @literal_fe_square term >>> @literal_fe_square term)
 >>> (O (@literal_fe_negate term) &&& I (@literal_fe_square term) >>> @literal_fe_add term
      >>> @canonical_fe_is_zero term) &&& I H
 >>> Bit.cond (injr iden) (injl unit)
        """,
    }
    for name, expected in expected_ports.items():
        if p.compact(p.definition(s["root_port"], name)) != p.compact(expected):
            raise ValueError("literal square-root tree differs: " + name)


def check_root(s):
    check_root_ports(s)
    statement = re.search(r"Theorem fe_square_root_literal_local_spec\s*:(.*?)\bProof\.", s["root_jet"], re.S)
    expected = "secp_jet_local_spec f_simplicity_fe_square_root (Word 8) (Ty.Sum Ty.Unit (Word 8)) " \
        "(@literal_fe_square_root Simplicity.Alg.CoreFunSem)."
    if not statement or p.compact(statement[1]) != p.compact(expected):
        raise ValueError("FeSquareRoot full public contract differs")


def test():
    s = {key: p.read_code(path) for key, path in {
        "catalog": REPO / "Haskell/Core/Simplicity/CoreJets.hs",
        "types": REPO / "Haskell/Core/Simplicity/Ty/LibSecp256k1.hs",
        "program": REPO / "Haskell/Core/Simplicity/Programs/LibSecp256k1.hs",
        "port": COQ / "C/jet_secp_rescale_literal.v",
        "jet": COQ / "C/jet_secp_rescale_local.v",
        "double_port": COQ / "C/jet_secp_double_literal.v",
        "double_jet": COQ / "C/jet_secp_double_local.v",
        "add_port": COQ / "C/jet_secp_add_literal.v",
        "mixed_jet": COQ / "C/jet_secp_mixed_local.v",
        "root_port": COQ / "C/jet_secp_root_literal.v",
        "root_jet": COQ / "C/jet_secp_root_local.v",
    }.items()}
    check(s)
    mutations = [
        ("catalog", "specificationSecp256k1 GejRescale = Secp256k1.gej_rescale", "specificationSecp256k1 GejRescale = Secp256k1.gej_negate"),
        ("types", "type GEJ = (GE, FE)", "type GEJ = (FE, GE)"),
        ("program", "gej_rescale = (ooh", "gej_rescale = (oih"),
        ("program", "fe_cube = iden &&& fe_square", "fe_cube = fe_square &&& iden"),
        ("program", "zinv = (ooh", "zinv = (oih"),
        ("port", "iden &&& @literal_fe_square term", "iden &&& iden"),
        ("port", "I (@literal_fe_cube term)", "I (@literal_fe_square term)"),
        ("port", "I H >>> @literal_gej_zinv term", "O H >>> @literal_gej_zinv term"),
        ("jet", "secp_jet_local_spec f_simplicity_gej_rescale", "False -> secp_jet_local_spec f_simplicity_gej_rescale"),
        ("jet", "f_simplicity_gej_rescale", "f_simplicity_gej_negate"),
        ("jet", "(Word 8)", "(Word 7)"),
        ("jet", "@literal_gej_rescale Alg.CoreFunSem", "@literal_gej_negate Alg.CoreFunSem"),
    ]
    for key, old, new in mutations:
        if old not in s[key]:
            raise ValueError("inactive rescale mutation fixture: " + old)
        changed = dict(s)
        changed[key] = s[key].replace(old, new, 1)
        try:
            check(changed)
        except ValueError:
            continue
        raise ValueError("accepted rescale source mutation: " + old)
    print("GejRescale catalog/literal/full contract match; 12 targeted mutations rejected")
    check_double(s)
    mutations = [
        ("catalog", "GejDouble :: Secp256k1Jet Secp256k1.GEJ Secp256k1.GEJ", "GejDouble :: Secp256k1Jet Secp256k1.GE Secp256k1.GE"),
        ("catalog", "specificationSecp256k1 GejDouble = Secp256k1.gej_double", "specificationSecp256k1 GejDouble = Secp256k1.gej_negate"),
        ("catalog", "implementationSecp256k1 GejDouble = FFI.gej_double", "implementationSecp256k1 GejDouble = FFI.gej_negate"),
        ("types", "type GEJ = (GE, FE)", "type GEJ = (FE, GE)"),
        ("program", "full_shift word1 word256", "full_shift word2 word256"),
        ("program", "fe_multiplyInt 3 >>> fe_halve", "fe_multiplyInt 2 >>> fe_halve"),
        ("program", "take (fe_multiplyInt 2)", "drop (fe_multiplyInt 2)"),
        ("program", "((iih &&& oh >>> fe_multiply >>> fe_negate)", "((ioh &&& oh >>> fe_multiply >>> fe_negate)"),
        ("program", "(oih &&& ih >>> fe_multiply)", "(ooh &&& ih >>> fe_multiply)"),
        ("program", "cond (unit >>> gej_infinity) body", "cond body (unit >>> gej_infinity)"),
        ("program", "fieldOrder + 1) `div` 2", "fieldOrder - 1) `div` 2"),
        ("program", "i `mod` LibSecp256k1.fieldOrder", "i `mod` LibSecp256k1.groupOrder"),
        ("double_port", "((feP+1)/2)", "((feP-1)/2)"),
        ("double_port", "(i mod feP)", "i"),
        ("double_port", "@Word.full_right_shift1 Bit 8 term", "@Word.full_left_shift1 Bit 8 term"),
        ("double_port", "@Word.full_right_shift1 Bit 8 term", "@Word.full_right_shift1 Bit 7 term"),
        ("double_port", "I H &&& O H", "O H &&& I H"),
        ("double_port", "@literal_fe_multiply_int 3 term", "@literal_fe_multiply_int 2 term"),
        ("double_port", "I (I H) &&& O H", "I (O H) &&& O H"),
        ("double_port", "@literal_fe_multiply_int 2 term", "@literal_fe_multiply_int 3 term"),
        ("double_port", "I (I (@literal_fe_square term))", "I (O (@literal_fe_square term))"),
        ("double_port", "O (I H) &&& I H >>> @literal_fe_multiply term", "O (O H) &&& I H >>> @literal_fe_multiply term"),
        ("double_port", "Bit.cond (unit >>> @literal_gej_infinity term) (@literal_gej_double_body term)",
                        "Bit.cond (@literal_gej_double_body term) (unit >>> @literal_gej_infinity term)"),
        ("double_jet", "secp_jet_local_spec f_simplicity_gej_double", "False -> secp_jet_local_spec f_simplicity_gej_double"),
        ("double_jet", "f_simplicity_gej_double", "f_secp256k1_gej_double_var"),
        ("double_jet", "(Word 8)", "(Word 7)"),
        ("double_jet", "@literal_gej_double Alg.CoreFunSem", "@literal_gej_double_body Alg.CoreFunSem"),
    ]
    for key, old, new in mutations:
        if old not in s[key]:
            raise ValueError("inactive doubling mutation fixture: " + old)
        changed = dict(s)
        changed[key] = s[key].replace(old, new, 1)
        try:
            check_double(changed)
        except ValueError:
            continue
        raise ValueError("accepted doubling source mutation: " + old)
    print(f"GejDouble catalog/literal/full contract match; {len(mutations)} targeted mutations rejected")
    check_addition_ports(s)
    mutations = [
        ("program", "zeroH = take (take fe_is_zero)", "zeroH = take (drop fe_is_zero)"),
        ("program", "cond (oih &&& gej_double)", "cond (ooh &&& gej_double)"),
        ("program", "fe_multiplyInt (-2)", "fe_multiplyInt 2"),
        ("program", "gej_add = gej_add_ex >>> ih", "gej_add = gej_add_ex >>> oh"),
        ("program", "gej_ge_add_ex = oh &&&", "gej_ge_add_ex = ih &&&"),
        ("program", "gej_ge_add = gej_ge_add_ex >>> ih", "gej_ge_add = gej_ge_add_ex >>> oh"),
        ("add_port", "Bit.cond (O I H &&&", "Bit.cond (O O H &&&"),
        ("add_port", "I zeroH", "O zeroH"),
        ("add_port", "@literal_fe_multiply_int (-2) term", "@literal_fe_multiply_int 2 term"),
        ("add_port", "O O O H &&&", "O O I H &&&"),
        ("add_port", "@literal_gej_add_ex term >>> I H", "@literal_gej_add_ex term >>> O H"),
        ("add_port", "O H &&& (I H &&& (unit >>> @literal_fe_one256 term))", "I H &&& (O H &&& (unit >>> @literal_fe_one256 term))"),
        ("add_port", "@literal_gej_ge_add_ex term >>> I H", "@literal_gej_ge_add_ex term >>> O H"),
    ]
    for key, old, new in mutations:
        if old not in s[key]:
            raise ValueError("inactive addition mutation fixture: " + old)
        changed = dict(s)
        changed[key] = s[key].replace(old, new, 1)
        try:
            check_addition_ports(changed)
        except ValueError:
            continue
        raise ValueError("accepted addition source mutation: " + old)
    print(f"Addition literal ports match; {len(mutations)} targeted mutations rejected")
    check_mixed(s)
    mutations = [
        ("catalog", "GejGeAdd :: Secp256k1Jet (Secp256k1.GEJ,Secp256k1.GE) Secp256k1.GEJ",
                    "GejGeAdd :: Secp256k1Jet (Secp256k1.GE,Secp256k1.GEJ) Secp256k1.GEJ"),
        ("catalog", "specificationSecp256k1 GejGeAdd = Secp256k1.gej_ge_add",
                    "specificationSecp256k1 GejGeAdd = Secp256k1.gej_add"),
        ("catalog", "implementationSecp256k1 GejGeAdd = FFI.gej_ge_add",
                    "implementationSecp256k1 GejGeAdd = FFI.gej_add"),
        ("types", "type GEJ = (GE, FE)", "type GEJ = (FE, GE)"),
        ("mixed_jet", "secp_jet_local_spec f_simplicity_gej_ge_add", "False -> secp_jet_local_spec f_simplicity_gej_ge_add"),
        ("mixed_jet", "f_simplicity_gej_ge_add", "f_secp256k1_gej_add_ge_var"),
        ("mixed_jet", "(Word 8)", "(Word 7)"),
        ("mixed_jet", "@literal_gej_ge_add Alg.CoreFunSem", "@literal_gej_ge_add_ex Alg.CoreFunSem"),
    ]
    for key, old, new in mutations:
        if old not in s[key]:
            raise ValueError("inactive mixed-addition mutation fixture: " + old)
        changed = dict(s)
        changed[key] = s[key].replace(old, new, 1)
        try:
            check_mixed(changed)
        except ValueError:
            continue
        raise ValueError("accepted mixed-addition source mutation: " + old)
    print(f"GejGeAdd catalog/literal/full contract match; {len(mutations)} targeted mutations rejected")
    check_root(s)
    mutations = [
        ("catalog", "specificationSecp256k1 FeSquareRoot = Secp256k1.fe_square_root",
                    "specificationSecp256k1 FeSquareRoot = Secp256k1.fe_square"),
        ("catalog", "implementationSecp256k1 FeSquareRoot = FFI.fe_square_root",
                    "implementationSecp256k1 FeSquareRoot = FFI.fe_square"),
        ("catalog", "FeSquareRoot :: Secp256k1Jet Secp256k1.FE (Either () Secp256k1.FE)",
                    "FeSquareRoot :: Secp256k1Jet Secp256k1.FE Secp256k1.FE"),
        ("program", "replicate 88 fe_square", "replicate 87 fe_square"),
        ("program", "tower = iden &&& fe_cube", "tower = fe_cube &&& iden"),
        ("program", ">>> oh &&& drop ((oh &&& drop fe_square", ">>> ih &&& drop ((oh &&& drop fe_square"),
        ("program", ">>> cond (injr iden) (injl unit)", ">>> cond (injl unit) (injr iden)"),
        ("root_port", "| Datatypes.O => iden", "| Datatypes.O => @literal_fe_square term"),
        ("root_port", "| Datatypes.O => @literal_fe_square term", "| Datatypes.O => iden"),
        ("root_port", "@literal_fe_squares 88 term", "@literal_fe_squares 87 term"),
        ("root_port", "iden &&& (@literal_fe_cube term)", "(@literal_fe_cube term) &&& iden"),
        ("root_port", ">>> O H &&& I ((O H", ">>> I H &&& I ((O H"),
        ("root_port", "Bit.cond (injr iden) (injl unit)", "Bit.cond (injl unit) (injr iden)"),
        ("root_jet", "secp_jet_local_spec f_simplicity_fe_square_root",
                     "secp_jet_local_spec f_simplicity_fe_normalize"),
        ("root_jet", "(Word 8) (Ty.Sum Ty.Unit (Word 8))", "(Word 7) (Ty.Sum Ty.Unit (Word 8))"),
        ("root_jet", "(Ty.Sum Ty.Unit (Word 8))", "(Word 8)"),
        ("root_jet", "(@literal_fe_square_root Simplicity.Alg.CoreFunSem)",
                     "(@literal_fe_square Simplicity.Alg.CoreFunSem)"),
        ("root_jet", "secp_jet_local_spec f_simplicity_fe_square_root",
                     "False -> secp_jet_local_spec f_simplicity_fe_square_root"),
    ]
    for key, old, new in mutations:
        if old not in s[key]:
            raise ValueError("inactive root mutation fixture: " + old)
        changed = dict(s)
        changed[key] = s[key].replace(old, new, 1)
        try:
            check_root(changed)
        except ValueError:
            continue
        raise ValueError("accepted root source mutation: " + old)
    print(f"FeSquareRoot catalog/literal/full contract match; {len(mutations)} targeted mutations rejected")


if __name__ == "__main__":
    test()
