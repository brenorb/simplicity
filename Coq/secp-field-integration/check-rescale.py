"""Point, field square-root and off-curve-scale literal ports/public contracts.

Reuse the existing source parser.  Field multiply/square dependencies retain
their own gates. This source correspondence check does not prove C execution.
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


def check_projective(s):
    """Canonical two-projective-point dispatch and the unrestricted public type."""
    check_addition_ports(s)
    for fragment in [
        "GejAdd :: Secp256k1Jet (Secp256k1.GEJ,Secp256k1.GEJ) Secp256k1.GEJ",
        "specificationSecp256k1 GejAdd = Secp256k1.gej_add",
        "implementationSecp256k1 GejAdd = FFI.gej_add",
    ]:
        p.require(s["catalog"], fragment, "GejAdd catalog")
    for declaration in ["type FE = Word256", "type GE = (FE, FE)", "type GEJ = (GE, FE)"]:
        p.require(s["types"], declaration, "projective-addition representation")
    statement = re.search(r"Theorem gej_add_literal_local_spec\s*:(.*?)\bProof\.", s["projective_jet"], re.S)
    expected = "secp_jet_local_spec f_simplicity_gej_add " \
        "(Ty.Prod (Ty.Prod (Ty.Prod (Word 8) (Word 8)) (Word 8)) " \
        "(Ty.Prod (Ty.Prod (Word 8) (Word 8)) (Word 8))) " \
        "(Ty.Prod (Ty.Prod (Word 8) (Word 8)) (Word 8)) (@literal_gej_add Alg.CoreFunSem)."
    if not statement or p.compact(statement[1]) != p.compact(expected):
        raise ValueError("GejAdd full public contract differs")


def check_gej_equiv(s):
    """Exact two-projective-point predicate and unrestricted public contract."""
    check_projective(s)
    for fragment in [
        "GejEquiv :: Secp256k1Jet (Secp256k1.GEJ, Secp256k1.GEJ) Bit",
        "specificationSecp256k1 GejEquiv = Secp256k1.gej_equiv",
        "implementationSecp256k1 GejEquiv = \\(a,b) -> return . toBit $ LibSecp256k1.gej_equiv (fromGEJ a) (fromGEJ b)",
    ]:
        p.require(s["catalog"], fragment, "GejEquiv catalog")
    impl = s["program"].split("lib@Lib{..} = Lib {", 1)[1]
    p.exact_program(impl, "gej_equiv", "gej_ge_equiv",
                    "take (gej_negate) &&& ih >>> gej_add >>> gej_is_infinity")
    expected = "O (@literal_gej_negate term) &&& I H >>> @literal_gej_add term >>> @literal_gej_is_infinity term"
    if p.compact(p.definition(s["projective_equiv_port"], "literal_gej_equiv")) != p.compact(expected):
        raise ValueError("literal projective-equivalence tree differs")
    statement = re.search(r"Theorem gej_equiv_literal_local_spec\s*:(.*?)\bProof\.", s["projective_equiv_jet"], re.S)
    expected = "secp_jet_local_spec f_simplicity_gej_equiv " \
        "(Ty.Prod (Ty.Prod (Ty.Prod (Word 8) (Word 8)) (Word 8)) " \
        "(Ty.Prod (Ty.Prod (Word 8) (Word 8)) (Word 8))) " \
        "(Ty.Sum Ty.Unit Ty.Unit) (@literal_gej_equiv Alg.CoreFunSem)."
    if not statement or p.compact(statement[1]) != p.compact(expected):
        raise ValueError("GejEquiv full public contract differs")


def check_gej_ge_equiv_ports(s):
    """Exact canonical mixed-equivalence composition and representation."""
    for fragment in [
        "GejGeEquiv :: Secp256k1Jet (Secp256k1.GEJ, Secp256k1.GE) Bit",
        "specificationSecp256k1 GejGeEquiv = Secp256k1.gej_ge_equiv",
        "implementationSecp256k1 GejGeEquiv = \\(a,b) -> return . toBit $ LibSecp256k1.gej_ge_equiv (fromGEJ a) (fromGE b)",
    ]:
        p.require(s["catalog"], fragment, "GejGeEquiv catalog")
    for declaration in ["type FE = Word256", "type GE = (FE, FE)", "type GEJ = (GE, FE)"]:
        p.require(s["types"], declaration, "mixed-equivalence representation")
    impl = s["program"].split("lib@Lib{..} = Lib {", 1)[1]
    p.exact_program(impl, "gej_ge_equiv", "gej_x_equiv",
                    "take (gej_negate) &&& ih >>> gej_ge_add >>> gej_is_infinity")
    expected = "O (@literal_gej_negate term) &&& I H >>> @literal_gej_ge_add term >>> @literal_gej_is_infinity term"
    if p.compact(p.definition(s["equiv_port"], "literal_gej_ge_equiv")) != p.compact(expected):
        raise ValueError("literal mixed-equivalence tree differs")


def check_gej_ge_equiv(s):
    check_gej_ge_equiv_ports(s)
    statement = re.search(r"Theorem gej_ge_equiv_literal_local_spec\s*:(.*?)\bProof\.", s["equiv_jet"], re.S)
    expected = "secp_jet_local_spec f_simplicity_gej_ge_equiv " \
        "(Ty.Prod (Ty.Prod (Ty.Prod (Word 8) (Word 8)) (Word 8)) (Ty.Prod (Word 8) (Word 8))) " \
        "(Ty.Sum Ty.Unit Ty.Unit) (@literal_gej_ge_equiv Alg.CoreFunSem)."
    if not statement or p.compact(statement[1]) != p.compact(expected):
        raise ValueError("GejGeEquiv full public contract differs")


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


def check_decompress(s):
    """Freeze parity routing, optional payload and the entire public contract."""
    for fragment in [
        "Decompress :: Secp256k1Jet Secp256k1.Point (Either () Secp256k1.GE)",
        "specificationSecp256k1 Decompress = Secp256k1.decompress",
        "implementationSecp256k1 Decompress = FFI.decompress",
    ]:
        p.require(s["catalog"], fragment, "Decompress catalog")
    for declaration in ["type FE = Word256", "type Point = (Bit, FE)", "type GE = (FE, FE)"]:
        p.require(s["types"], declaration, "decompression representation")
    impl = s["program"].split("lib@Lib{..} = Lib {", 1)[1]
    p.exact_program(impl, "decompress", "point_check_1", """
      let
        k = drop (drop fe_normalize) &&& (xor (take fe_is_odd) ioh &&& oh >>> cond fe_negate iden)
      in
        drop y_from_x &&& iden >>> match (injl unit) (injr k)
    """)
    root_input = re.search(r"\by_from_x\s*=(.*?)\n\s*fe_cube\s*=", impl, re.S)
    if not root_input or p.compact(root_input[1]) != p.compact(
            "(unit >>> scribe256 7) &&& fe_cube >>> fe_add >>> fe_square_root"):
        raise ValueError("canonical decompression root input differs")
    p.require(s["bit_program"], "xor s t = s &&& iden >>> cond (not t) t", "decompression parity xor")
    expected_ports = {
        "literal_y_from_x": "((unit >>> Alg.scribe curve_seven_word) &&& @literal_fe_cube term) "
                             ">>> @literal_fe_add term >>> @literal_fe_square_root term",
        "literal_decompress_flip": "(O (@canonical_fe_is_odd term) &&& iden) "
                                   ">>> Bit.cond (Bit.not (I (O H))) (I (O H))",
        "literal_decompress_point": "I (I (@canonical_fe_normalize term)) &&& "
                                    "((@literal_decompress_flip term &&& O H) >>> Bit.cond (@literal_fe_negate term) iden)",
        "literal_decompress": "I (@literal_y_from_x term) &&& iden >>> "
                              "case (injl unit) (injr (@literal_decompress_point term))",
    }
    for name, expected in expected_ports.items():
        if p.compact(p.definition(s["decompress_port"], name)) != p.compact(expected):
            raise ValueError("literal decompression tree differs: " + name)
    statement = re.search(r"Theorem decompress_literal_local_spec\s*:(.*?)\bProof\.", s["decompress_jet"], re.S)
    expected = "secp_jet_local_spec f_simplicity_decompress " \
        "(Ty.Prod (Ty.Sum Ty.Unit Ty.Unit) (Word 8)) (Ty.Sum Ty.Unit (Ty.Prod (Word 8) (Word 8))) " \
        "(@literal_decompress Simplicity.Alg.CoreFunSem)."
    if not statement or p.compact(statement[1]) != p.compact(expected):
        raise ValueError("Decompress full public contract differs")


# OffCurveScale is an exported helper, not a CoreJets constructor. Bind its
# named library term through the existing FFI comparison, without inventing
# a commitment identity. These are source-correspondence checks, not proofs
# of C execution. The registered kernel theorem supplies that evidence.
SCALE_PORT_FILES = {
    'scale_complete': 'jet_secp_strauss_complete_program.v',
    'scale_steps': 'jet_secp_strauss_program.v',
    'scale_table': 'jet_secp_scalar_table_literal.v',
    'scale_split': 'jet_secp_split_literal.v',
    'scale_round': 'jet_secp_split_round_literal.v',
    'scale_multipliers': 'jet_secp_split_multipliers.v',
    'scale_basis': 'jet_secp_split_constants.v',
    'scale_lattice': 'jet_secp_split_signed_bounds.v',
    'scale_wnaf': 'jet_secp_wnaf_literal.v',
    'scale_wnaf5': 'jet_secp_wnaf5_literal.v',
    'scale_split128': 'jet_secp_scalar_split128_literal.v',
    'scale_lookup': 'jet_secp_lookup5_literal.v',
    'scale_ge_lambda': 'jet_secp_table_get_lambda_literal.v',
    'scale_generate': 'jet_secp_generate_program.v',
    'scale_generator_loop': 'jet_secp_generator_program.v',
    'scale_startup': 'jet_secp_scale_startup.v',
    'scale_increment': 'jet_increment_spec.v',
    'scale_jet': 'jet_secp_scale_local.v',
}


def check_off_curve_scale(s):
    """Literal off_curve_scale only: its generator scalar is identically zero.

    The checked zero-digit lemmas make generator table/inversion leaves
    unreachable. This does not certify nonzero-generator combinations or
    the separate on-curve assertion in Scale. Existing field/scalar/word
    dependency gates retain responsibility for their primitive ports.
    """
    for declaration in ["type FE = Word256", "type GE = (FE, FE)",
                        "type GEJ = (GE, FE)", "type Scalar = Word256"]:
        p.require(s["types"], declaration, "off-curve scale representation")
    p.require(s["program"], "off_curve_scale :: term (Scalar, GEJ) GEJ", "scale library type")
    p.require(s["scale_ffi"], "off_curve_scale :: (Scalar, GEJ) -> Maybe GEJ", "scale FFI type")
    p.require(s["scale_ffi"], "off_curve_scale = unsafeLocalCoreJet c_off_curve_scale", "scale FFI binding")
    p.require(s["scale_ffi"], 'foreign import ccall unsafe "" c_off_curve_scale :: Ptr FrameItem -> Ptr FrameItem -> IO CBool', "scale foreign declaration")
    p.require(s["scale_ffi_test"], "fast_off_curve_scale = testCoreEval Prog.off_curve_scale", "scale comparison term")
    p.require(s["scale_ffi_test"], "fast_off_curve_scale (scalarAsTy na, gejAsTy a) == C.off_curve_scale (scalarAsTy na, gejAsTy a)", "scale comparison binding")
    impl = s["program"].split("lib@Lib{..} = Lib {", 1)[1]
    p.exact_program(impl, 'scalar_split_lambda', 'scalar_split_128', r"""
let
        g1 = scribe256 0x3086d221a7d46bcde86c90e49284eb153daa8a1471e8ca7fe893209a45dbb031
        g2 = scribe256 0xe4437ed6010e88286f547fa90abfe4c4221208ac9df506c61571b4ae8ac47f71
        negB1 = scribe128 0xe4437ed6010e88286f547fa90abfe4c3
        b2 = scribe128 0x3086d221a7d46bcde86c90e49284eb15
        roundDivTwo384 = take (drop (Arith.msb word128) &&& oh >>> Arith.full_increment word128) >>> ih
        c1 = ((iden &&& (unit >>> g1) >>> mul256) >>> roundDivTwo384) &&& (unit >>> negB1) >>> mul128
        c2 = ((iden &&& (unit >>> g2) >>> mul256) >>> roundDivTwo384) &&& (unit >>> b2) >>> mul128
        k1 = oh &&& drop (cond (((unit >>> high word128) &&& iden) &&& (unit >>> scribeGroupOrder) >>> add256 >>> ih)
                               ((unit >>> zero128) &&& iden)
                          &&& (unit >>> scalar_lambda) >>> scalar_multiply >>> scalar_negate) >>> scalar_add
         >>> msb256 &&& iden >>> cond (iden &&& (unit >>> scribeGroupOrder) >>> sub256 >>> injr unit &&& iih) (injl unit &&& ih)
      in
        scalar_normalize >>> iden &&& (c1 &&& c2 >>> sub256 >>> oh &&& iih) >>> k1 &&& ih
    """)
    p.exact_program(impl, 'scalar_split_128', 'wnaf5', r"""
scalar_normalize >>> (false &&& ih) &&& (false &&& oh)
    """)
    p.exact_program(impl, 'wnaf5', 'wnaf15', r"""
wnaf5step128 >>> (take wnaf5step1 >>> ih) &&& ih
    """)
    p.exact_program(impl, 'wnaf15', 'generate', r"""
wnaf15step128 >>> (take wnaf15step1 >>> ih) &&& ih
    """)
    p.exact_program(impl, 'generate', 'off_curve_linear_combination_1', r"""
let
      step = iih &&& (ioh &&& take gej_double >>> match ih (ih &&& take generateSmall >>> gej_ge_add))
         >>> match ih (ih &&& take generate128Small >>> gej_ge_add)
      step2 = (oh &&& (iooh &&& iioh) >>> step) &&& (ioih &&& iiih) >>> step
      step4 = (oh &&& (iooh &&& iioh) >>> step2) &&& (ioih &&& iiih) >>> step2
      step8 = (oh &&& (iooh &&& iioh) >>> step4) &&& (ioih &&& iiih) >>> step4
      step16 = (oh &&& (iooh &&& iioh) >>> step8) &&& (ioih &&& iiih) >>> step8
      step32 = (oh &&& (iooh &&& iioh) >>> step16) &&& (ioih &&& iiih) >>> step16
      step64 = (oh &&& (iooh &&& iioh) >>> step32) &&& (ioih &&& iiih) >>> step32
      step128 = (oh &&& (iooh &&& iioh) >>> step64) &&& (ioih &&& iiih) >>> step64
      step129 = (oh &&& (iooh &&& iioh) >>> step) &&& (ioih &&& iiih) >>> step128
     in
      (unit >>> gej_infinity) &&& split128 >>> step129
    """)
    p.exact_program(impl, 'off_curve_linear_combination_1', 'linear_check_1', r"""
let
      splitLambda = scalar_split_lambda >>> take wnaf5 &&& drop wnaf5
      body = (unit >>> gej_infinity) &&& (oih >>> scalarTable5) &&& (ooh >>> splitLambda) &&& (ih >>> split128)
         >>> iooh &&& step129
         >>> ioh &&& (oh &&& iih >>> fe_multiply)
      step = drop iiih
        &&& (drop iioh
         &&& (drop ioih
          &&& (drop iooh &&& take gej_double &&& ioih
                     >>> match ioh (ioh &&& (oh &&& iih >>> lookupTable5) >>> gej_ge_add))
          &&& ioih
          >>> match ioh (ioh &&& (oh &&& iih >>> lookupTable5 >>> ge_scale_lambda) >>> gej_ge_add))
         &&& iooh
         >>> match ioh (ioh &&& (take generateSmall &&& iih >>> zinv) >>> gej_ge_add))
        &&& iooh
        >>> match ioh (ioh &&& (take generate128Small &&& iih >>> zinv) >>> gej_ge_add)
      step2 = (oh &&& drop (oh &&& drop ((oooh &&& oioh) &&& (iooh &&& iioh))) >>> step)
                  &&& drop (oh &&& drop ((ooih &&& oiih) &&& (ioih &&& iiih))) >>> step
      step4 = (oh &&& drop (oh &&& drop ((oooh &&& oioh) &&& (iooh &&& iioh))) >>> step2)
                  &&& drop (oh &&& drop ((ooih &&& oiih) &&& (ioih &&& iiih))) >>> step2
      step8 = (oh &&& drop (oh &&& drop ((oooh &&& oioh) &&& (iooh &&& iioh))) >>> step4)
                  &&& drop (oh &&& drop ((ooih &&& oiih) &&& (ioih &&& iiih))) >>> step4
      step16 = (oh &&& drop (oh &&& drop ((oooh &&& oioh) &&& (iooh &&& iioh))) >>> step8)
                   &&& drop (oh &&& drop ((ooih &&& oiih) &&& (ioih &&& iiih))) >>> step8
      step32 = (oh &&& drop (oh &&& drop ((oooh &&& oioh) &&& (iooh &&& iioh))) >>> step16)
                   &&& drop (oh &&& drop ((ooih &&& oiih) &&& (ioih &&& iiih))) >>> step16
      step64 = (oh &&& drop (oh &&& drop ((oooh &&& oioh) &&& (iooh &&& iioh))) >>> step32)
                   &&& drop (oh &&& drop ((ooih &&& oiih) &&& (ioih &&& iiih))) >>> step32
      step128 = (oh &&& drop (oh &&& drop ((oooh &&& oioh) &&& (iooh &&& iioh))) >>> step64)
                    &&& drop (oh &&& drop ((ooih &&& oiih) &&& (ioih &&& iiih))) >>> step64
      step129 = (oh &&& drop (oh &&& drop ((oooh &&& oioh) &&& (iooh &&& iioh))) >>> step)
                    &&& drop (oh &&& drop ((ooih &&& oiih) &&& (ioih &&& iiih))) >>> step128
     in


      or (take (drop gej_is_infinity)) (take (take scalar_is_zero)) &&& iden
  >>> cond (drop generate) body
    """)
    p.exact_program(impl, 'off_curve_scale', 'decompress', r"""
iden &&& (unit >>> zero256) >>> off_curve_linear_combination_1
    """)
    p.exact_program(impl, 'ge_scale_lambda', 'gej_rescale', r"""
take fe_multiply_beta &&& drop fe_normalize
    """)
    helpers = [
        ('signResize4', '\\bsignResize4\\s*=(.*?)\\n\\s*wnafpre\\s*::', r"""
left_extend word4 (DoubleV . DoubleV . DoubleV . DoubleV . DoubleV $ SingleV)
  signResize16 = left_extend word16 (DoubleV . DoubleV . DoubleV $ SingleV)
  fullShift128 = full_shift word1 word128 >>> oh
  wnafsub128 :: term ((Bit, Word128), Word128) (Bit, Word128)
  wnafsub128 = xor ooh (drop msb128) &&& (oih &&& ih >>> sub128) >>> xor oh ioh &&& iih

  wnaf5step1 :: term (Bit, Word128) ((Bit, Word128), (Either () Word4))
  wnaf5step1 = drop lsb128 &&& (oh &&& fullShift128)
           >>> cond body (iden &&& injl unit)
   where
    body = iden &&& (drop . drop . drop $ iiih) >>> (oh &&& drop signResize4 >>> wnafsub128) &&& injr ih

  wnaf15step1 :: term (Bit,Word128) ((Bit,Word128), (Either () Word16))
  wnaf15step1 = drop lsb128 &&& iden
            >>> cond body ((oh &&& fullShift128) &&& injl unit)
   where
    mask = take (take (take (ih &&& ih) &&& ih) &&& ih) &&& ih
    body = iden &&& (drop iiih >>> mask)
       >>> ((ooh &&& take fullShift128) &&& drop (signResize16 >>> msb128 &&& iden >>> fullShift128) >>> wnafsub128)
       &&& injr ih

  wnafstepD :: (TyC s, TyC v) => term s (s, v) -> term s (s, (v, v))
  wnafstepD rec = rec >>> take rec &&& ih >>> ooh &&& (oih &&& ih)

  wnaf5step16 = wnafstepD . wnafstepD . wnafstepD . wnafstepD $ wnaf5step1
  wnaf5step128 = wnafstepD . wnafstepD . wnafstepD $ wnaf5step16
  wnaf15step16 = wnafstepD . wnafstepD . wnafstepD . wnafstepD $ wnaf15step1
  wnaf15step128 = wnafstepD . wnafstepD . wnafstepD $ wnaf15step16
        """),
        ('scalarTable5', '\\bscalarTable5\\s*=(.*?)\\n\\s*lookupTable5\\s*::', r"""
iden &&& gej_double
               >>> iih &&& (((ooh &&& iih >>> zinv) &&& oih) &&& ioh
                        >>> pass1_8)
               >>> (oh &&& iih >>> fe_multiply) &&& drop (take pass2_8)
     where
      pass1_2 = iden &&& gej_ge_add_ex >>> (ioh &&& (oooh &&& iioh)) &&& (iih &&& oih)
      pass1_4 = pass1_2 >>> oh &&& drop (gej_ge_add_ex &&& ih >>> ooh &&& (oih &&& ih >>> pass1_2)) >>> (ioh &&& (oh &&& iioh)) &&& iiih
      pass1_8 = pass1_4 >>> oh &&& drop (gej_ge_add_ex &&& ih >>> ooh &&& (oih &&& ih >>> pass1_4)) >>> (ioh &&& (oh &&& iioh)) &&& drop (drop ioih)
      pass2_1 = oh &&& ih >>> zinv
      pass2_2 = (oioh &&& (ooh &&& ih >>> fe_multiply)) &&& (oiih &&& ih >>> pass2_1) >>> (take pass2_1 &&& ih) &&& oih
      pass2_4 = (ooh &&& oioh) &&& (oiih &&& ih >>> pass2_2) >>> (oih &&& (ooh &&& iih >>> fe_multiply) >>> pass2_2) &&& ioh >>> (ooh &&& ih) &&& oih
      pass2_8 = ( oh &&&  ioh) &&& ( iih &&& (unit >>> fe_one) >>> pass2_4) >>> (oih &&& (ooh &&& iih >>> fe_multiply) >>> pass2_4) &&& ioh >>> ooh &&& ih
        """),
        ('lookupTable5', '\\blookupTable5\\s*=(.*?)\\n\\s*split128\\s*=', r"""
oooh &&& ooih &&& oih &&& ih
               >>> cond neg pos
     where
      pos = ioih &&& (iooh &&& (oh &&& iih >>> cond ih oh) >>> cond ih oh) >>> cond ih oh
      neg = ioih &&& (iooh &&& (oh &&& iih >>> cond oh ih) >>> cond oh ih) >>> cond (take ge_negate) (drop ge_negate)
        """),
    ]
    for name, pattern, expected in helpers:
        bodies = re.findall(pattern, s["program"], re.S)
        if len(bodies) != 1 or p.compact(bodies[0]) != p.compact(expected):
            raise ValueError("canonical scale helper differs: " + name)
    p.require(s["program"], "split128 = scalar_split_128 >>> take wnaf15 &&& drop wnaf15", "generator split")
    p.require(s["scale_arith"], "full_increment w = oh &&& (ih &&& (unit >>> zero w)) >>> full_add w", "rounding carry")
    ports = [
        ('scale_complete', 'literal_strauss_args', r"""
Ty.Prod (Ty.Prod (Word 8) literal_table_gej) (Word 8)
        """),
        ('scale_complete', 'strauss_split_windows', r"""
split >>> (O wnaf &&& I wnaf)
        """),
        ('scale_complete', 'literal_strauss_split_lambda', r"""
@strauss_split_windows term literal_wnaf5_digit (@literal_scalar_split_lambda term) (@literal_wnaf5 term)
        """),
        ('scale_complete', 'literal_strauss_split128', r"""
@strauss_split_windows term literal_wnaf_digit (@literal_scalar_split128 term) (@literal_wnaf15 term)
        """),
        ('scale_complete', 'strauss_body_routing', r"""
((unit >>> infinity) &&& (O I H >>> table)
  &&& (O O H >>> splitlam) &&& (I H >>> splitgen))
 >>> (I O O H &&& digits) >>> (I O H &&& ((O H &&& I I H) >>> multiply))
        """),
        ('scale_complete', 'literal_strauss_body', r"""
@strauss_body_routing term (@literal_gej_infinity term) (@literal_scalar_table5 term)
  (@literal_strauss_split_lambda term) (@literal_strauss_split128 term)
  (@literal_strauss_digits129 term) (@literal_fe_multiply term)
        """),
        ('scale_complete', 'literal_strauss_guard', r"""
Bit.or (O (I (@literal_gej_is_infinity term))) (O (O (@canonical_scalar_is_zero term)))
        """),
        ('scale_complete', 'literal_off_curve_linear_combination_1', r"""
(@literal_strauss_guard term &&& iden) >>>
 Bit.cond (I (@literal_generate term)) (@literal_strauss_body term)
        """),
        ('scale_complete', 'literal_off_curve_scale', r"""
(iden &&& (unit >>> @Word.zero 8 term)) >>> @literal_off_curve_linear_combination_1 term
        """),
        ('scale_steps', 'literal_strauss_context', r"""
Ty.Prod (Word 8) (literal_table_vector 3)
        """),
        ('scale_steps', 'literal_strauss_windows', r"""
Ty.Prod (Ty.Prod a a) (Ty.Prod b b)
        """),
        ('scale_steps', 'literal_strauss_input', r"""
Ty.Prod literal_generator_jacobian
 (Ty.Prod literal_strauss_context (literal_strauss_windows a b))
        """),
        ('scale_steps', 'literal_strauss_step', r"""
I (I I I H)
 &&& (I (I I O H)
  &&& (I (I O I H)
   &&& (I (I O O H) &&& O (@literal_gej_double term) &&& I O I H
      >>> Alg.Core.Combinators.case (I O H)
       ((I O H &&& (O H &&& I I H >>> @literal_lookup5 term)) >>> @literal_gej_ge_add term))
   &&& I O I H
   >>> Alg.Core.Combinators.case (I O H)
    ((I O H &&& (O H &&& I I H >>> @literal_lookup5 term >>> @literal_ge_scale_lambda term))
     >>> @literal_gej_ge_add term))
  &&& I O O H
  >>> Alg.Core.Combinators.case (I O H)
   ((I O H &&& (O (@literal_generate_small false term) &&& I I H >>> @literal_gej_zinv term))
    >>> @literal_gej_ge_add term))
 &&& I O O H
 >>> Alg.Core.Combinators.case (I O H)
  ((I O H &&& (O (@literal_generate_small true term) &&& I I H >>> @literal_gej_zinv term))
   >>> @literal_gej_ge_add term)
        """),
        ('scale_steps', 'literal_strauss_block', r"""
match depth as d return
  term (literal_strauss_input (Vector literal_wnaf5_digit d) (Vector literal_wnaf_digit d))
   literal_generator_jacobian with
 | Datatypes.O=>@literal_strauss_step term
 | Datatypes.S d=>
   let rec:=@literal_strauss_block d term in
   ((O H &&& I (O H &&& I ((O O O H &&& O I O H) &&& (I O O H &&& I I O H)))) >>> rec)
   &&& I (O H &&& I ((O O I H &&& O I I H) &&& (I O I H &&& I I I H))) >>> rec
 end
        """),
        ('scale_steps', 'literal_strauss_digits129', r"""
((O H &&& I (O H &&& I ((O O O H &&& O I O H) &&& (I O O H &&& I I O H))))
  >>> @literal_strauss_step term)
 &&& I (O H &&& I ((O O I H &&& O I I H) &&& (I O I H &&& I I I H)))
 >>> @literal_strauss_block 7 term
        """),
        ('scale_table', 'literal_table_ge', r"""
Ty.Prod (Word 8) (Word 8)
        """),
        ('scale_table', 'literal_table_gej', r"""
Ty.Prod literal_table_ge (Word 8)
        """),
        ('scale_table', 'literal_table_tree', r"""
match n with
 | Datatypes.O=>literal_table_ge
 | Datatypes.S k=>Ty.Prod (Word 8) (Ty.Prod (literal_table_tree k) (literal_table_tree k)) end
        """),
        ('scale_table', 'literal_table_vector', r"""
match n with
 | Datatypes.O=>literal_table_ge
 | Datatypes.S k=>Ty.Prod (literal_table_vector k) (literal_table_vector k) end
        """),
        ('scale_table', 'literal_pass1_2', r"""
iden &&& @literal_gej_ge_add_ex term >>>
 (I O H &&& (O O O H &&& I I O H)) &&& (I I H &&& O I H)
        """),
        ('scale_table', 'literal_pass1_4', r"""
@literal_pass1_2 term >>> O H &&& I
 (@literal_gej_ge_add_ex term &&& I H >>> O O H &&& (O I H &&& I H >>> @literal_pass1_2 term)) >>>
 (I O H &&& (O H &&& I I O H)) &&& I I I H
        """),
        ('scale_table', 'literal_pass1_8', r"""
@literal_pass1_4 term >>> O H &&& I
 (@literal_gej_ge_add_ex term &&& I H >>> O O H &&& (O I H &&& I H >>> @literal_pass1_4 term)) >>>
 (I O H &&& (O H &&& I I O H)) &&& I (I (I O I H))
        """),
        ('scale_table', 'literal_pass2_1', r"""
O H &&& I H >>> @literal_gej_zinv term
        """),
        ('scale_table', 'literal_pass2_2', r"""
(O I O H &&& (O O H &&& I H >>> @literal_fe_multiply term)) &&&
 (O I I H &&& I H >>> @literal_pass2_1 term) >>> (O (@literal_pass2_1 term) &&& I H) &&& O I H
        """),
        ('scale_table', 'literal_pass2_4', r"""
(O O H &&& O I O H) &&& (O I I H &&& I H >>> @literal_pass2_2 term) >>>
 (O I H &&& (O O H &&& I I H >>> @literal_fe_multiply term) >>> @literal_pass2_2 term) &&& I O H >>>
 (O O H &&& I H) &&& O I H
        """),
        ('scale_table', 'literal_pass2_8', r"""
(O H &&& I O H) &&& (I I H &&& (unit >>> @literal_fe_one256 term) >>> @literal_pass2_4 term) >>>
 (O I H &&& (O O H &&& I I H >>> @literal_fe_multiply term) >>> @literal_pass2_4 term) &&& I O H >>>
 O O H &&& I H
        """),
        ('scale_table', 'literal_scalar_table5', r"""
iden &&& @literal_gej_double term >>>
 I I H &&& (((O O H &&& I I H >>> @literal_gej_zinv term) &&& O I H) &&& I O H >>> @literal_pass1_8 term) >>>
 (O H &&& I I H >>> @literal_fe_multiply term) &&& I (O (@literal_pass2_8 term))
        """),
        ('scale_split', 'literal_split_half', r"""
Ty.Prod Bit (Word 7)
        """),
        ('scale_split', 'literal_split_basis_value', r"""
if first then split_basis_value Datatypes.true else split_lattice_b2
        """),
        ('scale_split', 'literal_split_basis_word', r"""
@fromZ (WordToZ 7) (literal_split_basis_value first)
        """),
        ('scale_split', 'literal_split_high', r"""
@Word.fill Ty.Unit Bit 7 term (@Bit.true Ty.Unit term)
        """),
        ('scale_split', 'literal_split_product', r"""
(@literal_split_coefficient first term &&& (unit >>> Alg.scribe (literal_split_basis_word first))) >>>
 @multiply_word_spec 7 term
        """),
        ('scale_split', 'literal_split_second', r"""
(@literal_split_product Datatypes.true term &&& @literal_split_product Datatypes.false term) >>>
 @subtract_word_spec term 8 >>> O H &&& I I H
        """),
        ('scale_split', 'literal_split_signed_scalar', r"""
Bit.cond
  ((((unit >>> @literal_split_high term) &&& iden) &&& (unit >>> Alg.scribe canonical_group_word)) >>>
   @canonical_add_word 8 term >>> I H)
  ((unit >>> @Word.zero 7 term) &&& iden)
        """),
        ('scale_split', 'literal_split_pack_half', r"""
(@Word.leftmost Bit 8 term &&& iden) >>> Bit.cond
  ((iden &&& (unit >>> Alg.scribe canonical_group_word)) >>> @subtract_word_spec term 8 >>> injr unit &&& I I H)
  (injl unit &&& I H)
        """),
        ('scale_split', 'literal_split_first', r"""
(O H &&& I (((@literal_split_signed_scalar term &&& (unit >>> @canonical_scalar_lambda term)) >>>
  @canonical_scalar_multiply term) >>> @canonical_scalar_negate term)) >>>
 @canonical_scalar_add term >>> @literal_split_pack_half term
        """),
        ('scale_split', 'literal_scalar_split_lambda', r"""
@canonical_scalar_normalize term >>> (iden &&& @literal_split_second term) >>>
 @literal_split_first term &&& I H
        """),
        ('scale_round', 'literal_round384', r"""
O ((I (@Word.leftmost Bit 7 term) &&& O H) >>> @full_increment_word_spec term 7) >>> I H
        """),
        ('scale_round', 'literal_split_coefficient', r"""
(iden &&& (unit >>> Alg.scribe (@fromZ (WordToZ 8) (split_multiplier_value first)))) >>>
 @multiply_word_spec 8 term >>> @literal_round384 term
        """),
        ('scale_multipliers', 'split_multiplier_value', r"""
if first then
 0x3086d221a7d46bcde86c90e49284eb153daa8a1471e8ca7fe893209a45dbb031 else
 0xe4437ed6010e88286f547fa90abfe4c4221208ac9df506c61571b4ae8ac47f71
        """),
        ('scale_basis', 'split_basis_value', r"""
if first then 0xe4437ed6010e88286f547fa90abfe4c3 else
 canonical_group_order-0x3086d221a7d46bcde86c90e49284eb15
        """),
        ('scale_lattice', 'split_lattice_b2', r"""
0x3086d221a7d46bcde86c90e49284eb15
        """),
        ('scale_wnaf', 'literal_wnaf_state', r"""
Ty.Prod Bit (Word 7)
        """),
        ('scale_wnaf', 'literal_wnaf_digit', r"""
Ty.Sum Ty.Unit (Word 4)
        """),
        ('scale_wnaf', 'literal_wnaf_shift128', r"""
@Word.full_right_shift1 Bit 7 term >>> O H
        """),
        ('scale_wnaf', 'literal_wnaf_extend16', r"""
@left_extend_word_spec 4 3 term
        """),
        ('scale_wnaf', 'literal_wnaf_sub128', r"""
(((O O H &&& I (@Word.leftmost Bit 7 term)) >>> @binary_bit_spec BXor term) &&&
    ((O I H &&& I H) >>> @subtract_word_spec term 7)) >>>
  ((O H &&& I O H) >>> @binary_bit_spec BXor term) &&& I I H
        """),
        ('scale_wnaf', 'literal_wnaf_mask15', r"""
O (O (O (I H &&& I H) &&& I H) &&& I H) &&& I H
        """),
        ('scale_wnaf', 'literal_wnaf15_body', r"""
(iden &&& (I (I I I H) >>> @literal_wnaf_mask15 term)) >>>
  (((O O H &&& O (@literal_wnaf_shift128 term)) &&&
    I (@literal_wnaf_extend16 term >>> (@Word.leftmost Bit 7 term &&& iden)
      >>> @literal_wnaf_shift128 term) >>> @literal_wnaf_sub128 term) &&& injr (I H))
        """),
        ('scale_wnaf', 'literal_wnaf15_step', r"""
(I (@Word.rightmost Bit 7 term) &&& iden) >>>
    Bit.cond (@literal_wnaf15_body term)
      ((O H &&& @literal_wnaf_shift128 term) &&& injl unit)
        """),
        ('scale_wnaf', 'literal_wnaf_double', r"""
rec >>> (O rec &&& I H) >>> O O H &&& (O I H &&& I H)
        """),
        ('scale_wnaf', 'literal_wnaf_block', r"""
match depth as d return term literal_wnaf_state
    (Ty.Prod literal_wnaf_state (Vector literal_wnaf_digit d)) with
  | Datatypes.O => @literal_wnaf15_step term
  | Datatypes.S d => literal_wnaf_double (literal_wnaf_block d)
  end
        """),
        ('scale_wnaf', 'literal_wnaf15_step16', r"""
@literal_wnaf_block 4 term
        """),
        ('scale_wnaf', 'literal_wnaf15_step128', r"""
literal_wnaf_double (literal_wnaf_double (literal_wnaf_double (@literal_wnaf15_step16 term)))
        """),
        ('scale_wnaf', 'literal_wnaf15', r"""
@literal_wnaf15_step128 term >>> (O (@literal_wnaf15_step term) >>> I H) &&& I H
        """),
        ('scale_wnaf5', 'literal_wnaf5_digit', r"""
Ty.Sum Ty.Unit (Word 2)
        """),
        ('scale_wnaf5', 'literal_wnaf_extend4', r"""
@left_extend_word_spec 2 5 term
        """),
        ('scale_wnaf5', 'literal_wnaf5_body', r"""
(iden &&& (I (I (I (I I I H))))) >>>
  (((O H &&& I (@literal_wnaf_extend4 term)) >>> @literal_wnaf_sub128 term) &&& injr (I H))
        """),
        ('scale_wnaf5', 'literal_wnaf5_step', r"""
(I (@Word.rightmost Bit 7 term) &&& (O H &&& @literal_wnaf_shift128 term)) >>>
    Bit.cond (@literal_wnaf5_body term) (iden &&& injl unit)
        """),
        ('scale_wnaf5', 'literal_wnaf5_block', r"""
match depth as d return term literal_wnaf_state
    (Ty.Prod literal_wnaf_state (Vector literal_wnaf5_digit d)) with
  | Datatypes.O => @literal_wnaf5_step term
  | Datatypes.S d => literal_wnaf_double (literal_wnaf5_block d)
  end
        """),
        ('scale_wnaf5', 'literal_wnaf5_step16', r"""
literal_wnaf_double (literal_wnaf_double
    (literal_wnaf_double (literal_wnaf_double (@literal_wnaf5_step term))))
        """),
        ('scale_wnaf5', 'literal_wnaf5_step128', r"""
literal_wnaf_double (literal_wnaf_double (literal_wnaf_double (@literal_wnaf5_step16 term)))
        """),
        ('scale_wnaf5', 'literal_wnaf5', r"""
@literal_wnaf5_step128 term >>> (O (@literal_wnaf5_step term) >>> I H) &&& I H
        """),
        ('scale_split128', 'literal_scalar_split128', r"""
@canonical_scalar_normalize term >>>
  ((@Bit.false (Word 8) term &&& I H) &&& (@Bit.false (Word 8) term &&& O H))
        """),
        ('scale_lookup', 'literal_lookup5_branch_type', r"""
Ty.Prod Bit (Ty.Prod (Word 1) (literal_table_vector 3))
        """),
        ('scale_lookup', 'literal_lookup5_pos', r"""
(I O I H &&& (I O O H &&& ((O H &&& I I H) >>> Bit.cond (I H) (O H))
  >>> Bit.cond (I H) (O H))) >>> Bit.cond (I H) (O H)
        """),
        ('scale_lookup', 'literal_lookup5_neg', r"""
(I O I H &&& (I O O H &&& ((O H &&& I I H) >>> Bit.cond (O H) (I H))
  >>> Bit.cond (O H) (I H))) >>> Bit.cond (O (@literal_ge_negate term)) (I (@literal_ge_negate term))
        """),
        ('scale_lookup', 'literal_lookup5', r"""
(O O O H &&& O O I H &&& O I H &&& I H) >>>
 Bit.cond (@literal_lookup5_neg term) (@literal_lookup5_pos term)
        """),
        ('scale_ge_lambda', 'literal_ge_scale_lambda', r"""
O (@literal_fe_multiply_beta term) &&& I (@canonical_fe_normalize term)
        """),
        ('scale_generate', 'literal_generate', r"""
((unit >>> @literal_gej_infinity term) &&&
   (@literal_scalar_split128 term >>> (O (@literal_wnaf15 term) &&& I (@literal_wnaf15 term)))) >>>
  @literal_generator_digits129 term
        """),
        ('scale_generator_loop', 'literal_generator_step', r"""
(I I H &&& ((I O H &&& O (@literal_gej_double term)) >>>
   Alg.Core.Combinators.case (I H)
     ((I H &&& O (@literal_generate_small false term)) >>> @literal_gej_ge_add term))) >>>
   Alg.Core.Combinators.case (I H)
     ((I H &&& O (@literal_generate_small true term)) >>> @literal_gej_ge_add term)
        """),
        ('scale_generator_loop', 'literal_generator_block', r"""
match depth as d return term (Ty.Prod literal_generator_jacobian
   (Ty.Prod (Vector literal_wnaf_digit d) (Vector literal_wnaf_digit d))) literal_generator_jacobian with
 | Datatypes.O=>@literal_generator_step term
 | Datatypes.S d=>
   let rec:=@literal_generator_block d term in
   ((O H &&& (I O O H &&& I I O H)) >>> rec) &&& (I O I H &&& I I I H) >>> rec
 end
        """),
        ('scale_generator_loop', 'literal_generator_digits129', r"""
((O H &&& (I O O H &&& I I O H)) >>> @literal_generator_step term) &&&
   (I O I H &&& I I I H) >>> @literal_generator_block 7 term
        """),
        ('scale_startup', 'scale_startup', r"""
strauss_zero_global_state m /\ split_constants_ready m /\ beta_initialized m
        """),
        ('scale_increment', 'full_increment_word_spec', r"""
@Alg.Core.Combinators.comp (Ty.Prod Bit (Word n))
    (Ty.Prod Bit (Ty.Prod (Word n) (Word n))) (Ty.Prod Bit (Word n)) term
    (@Alg.Core.Combinators.pair (Ty.Prod Bit (Word n)) Bit
      (Ty.Prod (Word n) (Word n)) term
      (@Alg.Core.Combinators.take Bit (Word n) Bit term
        (@Alg.Core.Combinators.iden Bit term))
      (@Alg.Core.Combinators.pair (Ty.Prod Bit (Word n)) (Word n) (Word n) term
        (@Alg.Core.Combinators.drop Bit (Word n) (Word n) term
          (@Alg.Core.Combinators.iden (Word n) term))
        (@Alg.Core.Combinators.comp (Ty.Prod Bit (Word n)) Ty.Unit (Word n) term
          (@Alg.Core.Combinators.unit (Ty.Prod Bit (Word n)) term)
          (@Word.zero n term))))
    (@Word.fullAdder n term)
        """),
    ]
    for key, name, expected in ports:
        if p.compact(p.definition(s[key], name)) != p.compact(expected):
            raise ValueError("literal off-curve scale tree differs: " + name)
    statements = re.findall(r"Theorem off_curve_scale_initialized_local_spec\s*:(.*?)\bProof\.", s["scale_jet"], re.S)
    expected = ("memset_model -> secp_jet_initialized_local_spec scale_startup "
                "f_simplicity_off_curve_scale (Ty.Prod (Word 8) literal_table_gej) "
                "literal_table_gej (@literal_off_curve_scale Alg.CoreFunSem).")
    if len(statements) != 1 or p.compact(statements[0]) != p.compact(expected):
        raise ValueError("off_curve_scale full public contract differs")
    return 75


CHECKED_SCALE_PORT_FILES = {
    'checked_literal': 'jet_secp_checked_scale_literal.v',
    'checked_contract': 'jet_secp_initialized_partial_contract.v',
    'checked_startup': 'jet_secp_checked_scale_startup.v',
    'checked_ready': 'jet_secp_scale_startup.v',
    'checked_zero': 'jet_secp_strauss_zero_generator.v',
    'checked_jet': 'jet_secp_checked_scale_local.v',
}

LINEAR_PORT_FILES = {
    'linear_jet': 'jet_secp_linear_local.v',
    'linear_startup': 'jet_secp_linear_startup.v',
    'linear_generator': 'jet_secp_generate_literal.v',
    'linear_norm': 'jet_secp_gej_norm_literal.v',
}


def check_off_curve_linear(s):
    """Bind the whole arbitrary-generator caller to the exported library term.

    Reuse all 75 Strauss ports, then check the generator leaves that were
    unreachable for off_curve_scale. There is no CoreJets identity for this
    exported helper; the library type and FFI comparison identify the target.
    """
    check_off_curve_scale(s)
    name = 'off_curve_linear_combination_1'
    for key, fragment in [
        ('program', f'{name} :: term ((Scalar, GEJ), Scalar) GEJ'),
        ('scale_ffi', f'{name} :: ((Scalar, GEJ), Scalar) -> Maybe GEJ'),
        ('scale_ffi', f'{name} = unsafeLocalCoreJet c_{name}'),
        ('scale_ffi', f'foreign import ccall unsafe "" c_{name} :: Ptr FrameItem -> Ptr FrameItem -> IO CBool'),
        ('scale_ffi_test', f'fast_{name} = testCoreEval Prog.{name}'),
        ('scale_ffi_test', f'fast_{name} ((scalarAsTy na, gejAsTy a), scalarAsTy ng) == C.{name} ((scalarAsTy na, gejAsTy a), scalarAsTy ng)'),
        ('program', 'generateSmall = generateSigned word16 >>> gej_norm'),
        ('program', 'generate128Small = generate128Signed word16 >>> gej_norm'),
        ('program', 'gej_norm = oh &&& drop fe_invert >>> zinv'),
    ]:
        p.require(s[key], fragment, 'linear-combination binding')
    for name, pattern, expected in [
        ('scaleConstant', r'\bscaleConstant base\s*=(.*?)\n\s*lib@Lib', '''
go
 where
  go :: Word a -> term (a, GEJ) GEJ
  go SingleV = cond (gej_double &&& (unit >>> base) >>> gej_ge_add) gej_double
  go (DoubleV w) = oih &&& (ooh &&& ih >>> rec) >>> rec
   where
    rec = go w
        '''),
        ('generateSigned', r'\bgenerateSigned SingleV\s*=(.*?)\n\s*generateSmall\s*::', '''
copair gej_infinity ((generate0 >>> ge_negate) &&& fe_one)
 generateSigned (DoubleV w) = ih &&& take rec >>> scaleConstant generate0 w
  where
   rec = generateSigned w
        '''),
        ('generate128Signed', r'\bgenerate128Signed SingleV\s*=(.*?)\n\s*generate128Small\s*::', '''
copair gej_infinity ((generate128 >>> ge_negate) &&& fe_one)
 generate128Signed (DoubleV w) = ih &&& take rec >>> scaleConstant generate128 w
  where
   rec = generate128Signed w
        '''),
    ]:
        bodies = re.findall(pattern, s['program'], re.S)
        if len(bodies) != 1 or p.compact(bodies[0]) != p.compact(expected):
            raise ValueError('canonical generator leaf differs: ' + name)
    for name, point, end in [
        ('generate0', '(toWord256 0x79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798, toWord256 0x483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8)', 'generate128'),
        ('generate128', '(toWord256 0x8f68b9d2f63b5f339239c1ad981f162ee88c5678723ea3351b7b444c9ec4c0da, toWord256 0x662a9f2dba063986de1d90c2b6be215dbbea2cfe95510bfdf23cbf79501fff82)', 'scaleConstant'),
    ]:
        local = 'g' if name == 'generate0' else 'g128'
        body = re.findall(r'\b' + name + r'\s*=(.*?)\n\s*' + end + r'\s*::', s['program'], re.S)
        if len(body) != 1 or p.compact(body[0]) != p.compact(f'scribe {local} where {local} = {point}'):
            raise ValueError('canonical generator constant differs: ' + name)
    for key, name, expected in [
        ('linear_startup', 'linear_startup', 'split_constants_ready m /\\ beta_initialized m /\\ (forall h,generator_table_state h m)'),
        ('linear_norm', 'literal_gej_norm', '(O H &&& I (@literal_fe_invert term)) >>> @literal_gej_zinv term'),
        ('linear_generator', 'literal_generator_point', 'Ty.Prod (Word 8) (Word 8)'),
        ('linear_generator', 'literal_generator_jacobian', 'Ty.Prod literal_generator_point (Word 8)'),
        ('linear_generator', 'literal_generator_base_word', '''
if second then
 (@fromZ (WordToZ 8) 0x8f68b9d2f63b5f339239c1ad981f162ee88c5678723ea3351b7b444c9ec4c0da,
  @fromZ (WordToZ 8) 0x662a9f2dba063986de1d90c2b6be215dbbea2cfe95510bfdf23cbf79501fff82)
else
 (@fromZ (WordToZ 8) 0x79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798,
  @fromZ (WordToZ 8) 0x483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8)
        '''),
        ('linear_generator', 'literal_generator_base', 'Alg.scribe (literal_generator_base_word second)'),
        ('linear_generator', 'literal_scale_constant', '''
match n as k return term (Ty.Prod (Word k) literal_generator_jacobian) literal_generator_jacobian with
 | Datatypes.O => Bit.cond
     ((@literal_gej_double term &&& (unit >>> base)) >>> @literal_gej_ge_add term)
     (@literal_gej_double term)
 | Datatypes.S k =>
     let rec := @literal_scale_constant k term base in
     (O (I H) &&& ((O (O H) &&& I H) >>> rec)) >>> rec
end
        '''),
        ('linear_generator', 'literal_generate_signed', '''
match n as k return term (Word k) literal_generator_jacobian with
 | Datatypes.O => Alg.Core.Combinators.copair (@literal_gej_infinity term)
     ((base >>> @literal_ge_negate term) &&& @literal_fe_one256 term)
 | Datatypes.S k =>
     (I H &&& O (@literal_generate_signed k term base)) >>> @literal_scale_constant k term base
end
        '''),
        ('linear_generator', 'literal_generate_small', '@literal_generate_signed 4 term (@literal_generator_base second term) >>> @literal_gej_norm term'),
    ]:
        if p.compact(p.definition(s[key], name)) != p.compact(expected):
            raise ValueError('linear-combination literal boundary differs: ' + name)
    statements = re.findall(r'Theorem off_curve_linear_initialized_local_spec\s*:(.*?)\bProof\.', s['linear_jet'], re.S)
    expected = ('memset_model -> secp_jet_initialized_local_spec linear_startup '
                'f_simplicity_off_curve_linear_combination_1 literal_strauss_args '
                'literal_table_gej (@literal_off_curve_linear_combination_1 Alg.CoreFunSem).')
    if len(statements) != 1 or p.compact(statements[0]) != p.compact(expected):
        raise ValueError('off_curve_linear_combination_1 full public contract differs')


def check_checked_scale(s):
    """Reuse the off-curve ports and the shared assertion-root gate.

    This checks the added on-curve assertion and all-input partial contract;
    it does not turn a successful-only theorem into complete coverage.
    """
    for fragment in [
        "Scale :: Secp256k1Jet (Secp256k1.Scalar,Secp256k1.GEJ) Secp256k1.GEJ",
        "specificationSecp256k1 Scale = Secp256k1.scale",
        "implementationSecp256k1 Scale = FFI.scale",
    ]:
        p.require(s["catalog"], fragment, "Scale catalog")
    p.require(s["program"], "scale :: Assert term => Lib term -> term (Scalar, GEJ) GEJ", "Scale assertion type")
    p.require(s["program"], "scale m = drop (gej_is_on_curve m) &&& (off_curve_scale m) >>> assertr cmrFail0 ih", "Scale assertion tree")
    p.require(s["scale_ffi"], "scale :: (Scalar, GEJ) -> Maybe GEJ", "Scale FFI type")
    p.require(s["scale_ffi"], "scale = unsafeLocalCoreJet c_scale", "Scale FFI binding")
    ports = [
        ('checked_literal', 'literal_checked_scale_core', r"""
SC.pair (SC.drop (@literal_gej_is_on_curve term)) (@literal_off_curve_scale term)
        """),
        ('checked_literal', 'literal_checked_scale', r"""
SC.comp (@literal_checked_scale_core (Alg.Assertion.toCore term))
  (Alg.Assertion.Combinators.assertr assertion_cmr_fail0 (SC.drop SC.iden))
        """),
        ('checked_contract', 'secp_jet_initialized_partial_local_spec', r"""
forall env m bd base bs sbase bi bw edge outedge cursor rc (a:Ty.tySem A),
 Ready m -> frame_base_valid sbase -> (8|sbase) ->
 frame_fields_at m bs sbase bi edge rc ->
 0<=rc -> rc+Z.of_nat (bitSize A)<=Int64.max_unsigned ->
 frame_input_cells_at m bi edge rc (encode a) ->
 write_frame_at m bd base bw outedge cursor (Z.of_nat (bitSize B)) ->
 exists mf,
 Clight2.eval_funcall secp_ge m (Internal f)
  [Vptr bd (Ptrofs.repr base);Vptr bs (Ptrofs.repr sbase);env] E0 mf (jet_partial_return (spec a)) /\
 (match spec a with
  | Some value=>frame_output_cells_at mf bw outedge cursor (encode value) /\
    write_prefix_at m mf bw outedge cursor /\
    frame_fields_at mf bd base bw outedge (cursor-Z.of_nat (bitSize B))
  | None=>True end) /\
 (forall chunk b ofs,Mem.valid_block m b ->
  (b<>bd \/ ofs+size_chunk chunk<=base+8 \/ base+16<=ofs) ->
  (b<>bw \/ ofs+size_chunk chunk<=outedge+8*((cursor-Z.of_nat (bitSize B))/64) \/
   write_word_address outedge cursor+8<=ofs) ->
  Mem.load chunk mf b ofs=Mem.load chunk m b ofs) /\ Ready mf
        """),
        ('checked_startup', 'checked_zero_block', r"""
secp_symbol_block _ng__1
        """),
        ('checked_startup', 'checked_scale_startup', r"""
scale_startup_at checked_zero_block m
        """),
        ('checked_ready', 'scale_startup_at', r"""
zero_scalar_state bng m /\ split_constants_ready m /\ beta_initialized m
        """),
        ('checked_zero', 'zero_scalar_state', r"""
scalar_at m bng 0 [Int64.zero;Int64.zero;Int64.zero;Int64.zero] /\
 readonly_region_bounds m bng 0 32
        """),
    ]
    for key, name, expected in ports:
        if p.compact(p.definition(s[key], name)) != p.compact(expected):
            raise ValueError("checked Scale boundary differs: " + name)
    statements = re.findall(r"Theorem checked_scale_initialized_local_spec\s*:(.*?)\bProof\.", s["checked_jet"], re.S)
    expected = ("memset_model -> secp_jet_initialized_partial_local_spec checked_scale_startup "
                "f_simplicity_scale (Ty.Prod (Word 8) literal_table_gej) literal_table_gej "
                "(@literal_checked_scale (Alg.AssertionSem option_Monad_Zero)).")
    if len(statements) != 1 or p.compact(statements[0]) != p.compact(expected):
        raise ValueError("Scale complete success/failure contract differs")

def check_checked_linear(s):
    """Bind the assertion caller while reusing the accepted shared boundaries."""
    check_off_curve_linear(s)
    check_checked_scale(s)  # Includes the complete shared partial contract.
    for key, fragment in [
        ('catalog', 'LinearCombination1 :: Secp256k1Jet ((Secp256k1.Scalar,Secp256k1.GEJ),Secp256k1.Scalar) Secp256k1.GEJ'),
        ('catalog', 'specificationSecp256k1 LinearCombination1 = Secp256k1.linear_combination_1'),
        ('catalog', 'implementationSecp256k1 LinearCombination1 = FFI.linear_combination_1'),
        ('program', 'linear_combination_1 :: Assert term => Lib term -> term ((Scalar, GEJ), Scalar) GEJ'),
        ('program', 'linear_combination_1 m = take (drop (gej_is_on_curve m)) &&& (off_curve_linear_combination_1 m) >>> assertr cmrFail0 ih'),
        ('scale_ffi', 'linear_combination_1 :: ((Scalar, GEJ), Scalar) -> Maybe GEJ'),
        ('scale_ffi', 'linear_combination_1 = unsafeLocalCoreJet c_linear_combination_1'),
        ('scale_ffi', 'foreign import ccall unsafe "" c_linear_combination_1 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool'),
    ]:
        p.require(s[key], fragment, 'LinearCombination1 binding')
    for name, expected in [
        ('literal_checked_linear_core', 'SC.pair (SC.take (SC.drop (@literal_gej_is_on_curve term))) (@literal_off_curve_linear_combination_1 term)'),
        ('literal_checked_linear', '''
SC.comp (@literal_checked_linear_core (Alg.Assertion.toCore term))
 (Alg.Assertion.Combinators.assertr assertion_cmr_fail0 (SC.drop SC.iden))
        '''),
    ]:
        if p.compact(p.definition(s['checked_linear_literal'], name)) != p.compact(expected):
            raise ValueError('checked linear assertion tree differs: ' + name)
    statements = re.findall(r'Theorem checked_linear_initialized_local_spec\s*:(.*?)\bProof\.', s['checked_linear_jet'], re.S)
    expected = ('memset_model -> secp_jet_initialized_partial_local_spec linear_startup '
                'f_simplicity_linear_combination_1 literal_strauss_args literal_table_gej '
                '(@literal_checked_linear (Alg.AssertionSem option_Monad_Zero)).')
    if len(statements) != 1 or p.compact(statements[0]) != p.compact(expected):
        raise ValueError('LinearCombination1 complete success/failure contract differs')



def check_linear_verify(s):
    """Bind the affine verifier and its complete success/failure contract."""
    check_checked_linear(s)
    for key, fragment in [
        ('catalog', 'LinearVerify1 :: Secp256k1Jet (((Secp256k1.Scalar,Secp256k1.GE),Secp256k1.Scalar),Secp256k1.GE) ()'),
        ('catalog', 'specificationSecp256k1 LinearVerify1 = Secp256k1.linear_verify_1'),
        ('catalog', 'implementationSecp256k1 LinearVerify1 = FFI.linear_verify_1'),
        ('program', 'linear_verify_1 :: Assert term => Lib term -> term (((Scalar, GE), Scalar), GE) ()'),
        ('program', 'linear_verify_1 m = assert (linear_check_1 m)'),
        ('bit_program', 'assert t = t &&& unit >>> assertr cmrFail0 oh'),
        ('scale_ffi', 'linear_verify_1 :: (((Scalar, GE), Scalar), GE) -> Maybe ()'),
        ('scale_ffi', 'linear_verify_1 = unsafeLocalCoreJet c_linear_verify_1'),
        ('scale_ffi', 'foreign import ccall unsafe "" c_linear_verify_1 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool'),
    ]:
        p.require(s[key], fragment, 'LinearVerify1 binding')
    impl = s['program'].split('lib@Lib{..} = Lib {', 1)[1]
    p.exact_program(impl, 'linear_check_1', 'off_curve_scale', r"""
and (drop ge_is_on_curve)
 (and (take (take (drop ge_is_on_curve)))
  ((take (take (oh &&& (ih &&& (unit >>> fe_one))) &&& ih >>> off_curve_linear_combination_1))
    &&& drop ge_negate >>> gej_ge_add >>> gej_is_infinity))
    """)
    for name, expected in [
        ('literal_linear_verify_args', 'Ty.Prod (Ty.Prod (Ty.Prod (Word 8) literal_table_ge) (Word 8)) literal_table_ge'),
        ('literal_affine_linear_routing', 'O (O H &&& (I H &&& (unit >>> @literal_fe_one256 term))) &&& I H'),
        ('literal_linear_check_body', r"""
((O (@literal_affine_linear_routing term >>> @literal_off_curve_linear_combination_1 term))
 &&& I (@literal_ge_negate term)) >>> @literal_gej_ge_add term >>> @literal_gej_is_infinity term
        """),
        ('literal_linear_check', r"""
Bit.and (I (@literal_ge_is_on_curve term))
 (Bit.and (O (O (I (@literal_ge_is_on_curve term)))) (@literal_linear_check_body term))
        """),
        ('literal_linear_verify', r"""
SC.comp (SC.pair (@literal_linear_check (Alg.Assertion.toCore term)) SC.unit)
 (Alg.Assertion.Combinators.assertr assertion_cmr_fail0 (SC.take SC.iden))
        """),
    ]:
        if p.compact(p.definition(s['linear_verify_literal'], name)) != p.compact(expected):
            raise ValueError('affine verifier literal tree differs: ' + name)
    statements = re.findall(r'Theorem linear_verify_initialized_local_spec\s*:(.*?)\bProof\.', s['linear_verify_jet'], re.S)
    expected = ('memset_model -> secp_jet_initialized_partial_local_spec linear_startup '
                'f_simplicity_linear_verify_1 literal_linear_verify_args Ty.Unit '
                '(@literal_linear_verify (Alg.AssertionSem option_Monad_Zero)).')
    if len(statements) != 1 or p.compact(statements[0]) != p.compact(expected):
        raise ValueError('LinearVerify1 complete success/failure contract differs')


def check_point_verify(s):
    """Bind compressed-point decoding and the full C assertion contract."""
    check_linear_verify(s)
    check_decompress(s)
    for key, fragment in [
        ('catalog', 'PointVerify1 :: Secp256k1Jet (((Secp256k1.Scalar,Secp256k1.Point),Secp256k1.Scalar),Secp256k1.Point) ()'),
        ('catalog', 'specificationSecp256k1 PointVerify1 = Secp256k1.point_verify_1'),
        ('catalog', 'implementationSecp256k1 PointVerify1 = FFI.point_verify_1'),
        ('types', 'type Point = (Bit, FE)'),
        ('program', 'point_verify_1 :: Assert term => Lib term -> term (((Scalar, Point), Scalar), Point) ()'),
        ('program', 'point_verify_1 m = assert (point_check_1 m)'),
        ('scale_ffi', 'point_verify_1 :: (((Scalar, Point), Scalar), Point) -> Maybe ()'),
        ('scale_ffi', 'point_verify_1 = unsafeLocalCoreJet c_point_verify_1'),
        ('scale_ffi', 'foreign import ccall unsafe "" c_point_verify_1 :: Ptr FrameItem -> Ptr FrameItem -> IO CBool'),
    ]:
        p.require(s[key], fragment, 'PointVerify1 binding')
    impl = s['program'].split('lib@Lib{..} = Lib {', 1)[1]
    p.exact_program(impl, 'point_check_1', 'pubkey_unpack', r"""
let
  k1 = drop (take (drop decompress)) &&& (drop (ooh &&& ih) &&& oh)
   >>> match false k2
  k2 = ((iooh &&& oh) &&& ioih) &&& iih >>> linear_check_1
in
  drop decompress &&& oh >>> match false k1
    """)
    for name, expected in [
        ('literal_compressed_point', 'Ty.Prod Bit (Word 8)'),
        ('literal_point_verify_args', 'Ty.Prod (Ty.Prod (Ty.Prod (Word 8) literal_compressed_point) (Word 8)) literal_compressed_point'),
        ('literal_point_check_k2', '((I (O (O H)) &&& O H) &&& I (O (I H))) &&& I (I H) >>> @literal_linear_check term'),
        ('literal_point_check_k1', r"""
(I (O (I (@literal_decompress term))) &&& (I (O (O H) &&& I H) &&& O H))
 >>> case Bit.false (@literal_point_check_k2 term)
        """),
        ('literal_point_check', 'I (@literal_decompress term) &&& O H >>> case Bit.false (@literal_point_check_k1 term)'),
        ('literal_point_verify', r"""
SC.comp (SC.pair (@literal_point_check (Alg.Assertion.toCore term)) SC.unit)
 (Alg.Assertion.Combinators.assertr assertion_cmr_fail0 (SC.take SC.iden))
        """),
    ]:
        if p.compact(p.definition(s['point_verify_literal'], name)) != p.compact(expected):
            raise ValueError('compressed verifier literal tree differs: ' + name)
    statements = re.findall(r'Theorem point_verify_initialized_local_spec\s*:(.*?)\bProof\.', s['point_verify_jet'], re.S)
    expected = ('memset_model -> secp_jet_initialized_partial_local_spec linear_startup '
                'f_simplicity_point_verify_1 literal_point_verify_args Ty.Unit '
                '(@literal_point_verify (Alg.AssertionSem option_Monad_Zero)).')
    if len(statements) != 1 or p.compact(statements[0]) != p.compact(expected):
        raise ValueError('PointVerify1 complete success/failure contract differs')


def check_bip0340(s):
    """Bind BIP340 to the frozen signature jet and its all-input C theorem."""
    check_point_verify(s)
    for key, fragment in [
        ('catalog', 'Bip0340Verify :: SignatureJet ((Secp256k1.PubKey, Word256),Secp256k1.Sig) ()'),
        ('catalog', 'specificationSignature Bip0340Verify = Secp256k1.bip_0340_verify'),
        ('catalog', 'implementationSignature Bip0340Verify a = FFI.bip_0340_verify a'),
        ('types', 'type PubKey = Word256'),
        ('types', 'type Sig = (Word256, Word256)'),
        ('program', 'bip_0340_verify :: Assert term => Lib term -> term ((PubKey, Word256), Sig) ()'),
        ('program', 'bip_0340_verify m = assert (bip_0340_check m)'),
        ('program', 'pubkey_check = (iden &&& scribe (toWord256 LibSecp256k1.fieldOrder) >>> lt256) &&& iden'),
        ('program', 'lt256 = Arith.lt word256'),
        ('scale_ffi', 'bip_0340_verify :: ((PubKey, Word256), Sig) -> Maybe ()'),
        ('scale_ffi', 'bip_0340_verify = unsafeLocalCoreJet c_bip_0340_verify'),
        ('scale_ffi', 'foreign import ccall unsafe "" c_bip_0340_verify :: Ptr FrameItem -> Ptr FrameItem -> IO CBool'),
        ('schnorr_digest', 'tagIv tag = compress noTagIv (tagDigest, tagDigest)'),
        ('schnorr_digest', 'tagDigest = bsHash . BSC.pack $ tag'),
        ('schnorr_digest', 'noTagIv = IV sha256Incremental'),
        ('schnorr_digest', 'compress (IV state) (h1, h2) = IV $ state `pushChunk` BSS.fromShort (hash256 h1) `pushChunk` BSS.fromShort (hash256 h2)'),
    ]:
        p.require(s[key], fragment, 'BIP340 binding')
    impl = s['program'].split('lib@Lib{..} = Lib {', 1)[1]
    p.exact_program(impl, 'pubkey_unpack_neg', 'signature_unpack',
                    'pubkey_check >>> cond (injr ((unit >>> true) &&& iden)) (injl unit)')
    p.exact_program(impl, 'signature_unpack', 'bip_0340_check', '''
and (oh &&& scribe (toWord256 LibSecp256k1.fieldOrder) >>> lt256)
    (ih &&& scribe (toWord256 LibSecp256k1.groupOrder) >>> lt256)
 &&& iden >>> cond (injr iden) (injl unit)
    ''')
    p.exact_program(impl, 'bip_0340_check', 'swu', '''
let
 k1 = iih &&& (ioh &&& oh) >>> match false k2
 k2 = (ih &&& oih) &&& ((unit >>> false) &&& ooh) >>> point_check_1
 e = m >>> (iv &&& oh >>> hashBlock) &&& ih >>> hashBlock >>> scalar_normalize
 iv = scribe $ toWord256 . integerHash256 . ivHash . tagIv $ "BIP0340/challenge"
 m = (ioh &&& ooh) &&& (oih &&& (scribe (toWord256 0x8000000000000000000000000000000000000000000000000000000000000500)))
in take (take pubkey_unpack_neg) &&& (e &&& drop signature_unpack) >>> match false k1
    ''')
    ports = [
        ('schnorr_literal', 'literal_schnorr_signature', 'Ty.Prod (Word 8) (Word 8)'),
        ('schnorr_literal', 'literal_schnorr_pubkey_check',
         '((iden &&& Alg.scribe canonical_field_word) >>> @lt_word_spec term 8) &&& iden'),
        ('schnorr_literal', 'literal_schnorr_pubkey_unpack_neg', '''
@literal_schnorr_pubkey_check term >>> Bit.cond
 (injr ((unit >>> Bit.true) &&& iden)) (injl unit)
        '''),
        ('schnorr_literal', 'literal_schnorr_signature_unpack', '''
(Bit.and ((O H &&& Alg.scribe canonical_field_word) >>> @lt_word_spec term 8)
         ((I H &&& Alg.scribe canonical_group_word) >>> @lt_word_spec term 8) &&& iden)
 >>> Bit.cond (injr iden) (injl unit)
        '''),
        ('schnorr_literal', 'literal_bip0340_k2',
         '((I H &&& O (I H)) &&& ((unit >>> Bit.false) &&& O (O H))) >>> @literal_point_check term'),
        ('schnorr_literal', 'literal_bip0340_k1',
         '(I (I H) &&& (I (O H) &&& O H)) >>> case Bit.false (@literal_bip0340_k2 term)'),
        ('schnorr_literal', 'literal_bip0340_check', '''
(O (O (@literal_schnorr_pubkey_unpack_neg term)) &&&
 (@literal_bip0340_challenge term &&& I (@literal_schnorr_signature_unpack term)))
 >>> case Bit.false (@literal_bip0340_k1 term)
        '''),
        ('schnorr_literal', 'literal_bip0340_verify', '''
SC.comp (SC.pair (@literal_bip0340_check (Alg.Assertion.toCore term)) SC.unit)
 (Alg.Assertion.Combinators.assertr assertion_cmr_fail0 (SC.take SC.iden))
        '''),
        ('schnorr_challenge', 'literal_bip0340_args',
         'Ty.Prod (Ty.Prod (Word 8) (Word 8)) (Ty.Prod (Word 8) (Word 8))'),
        ('schnorr_challenge', 'literal_bip0340_challenge_message',
         '(I (O H) &&& O (O H)) &&& (O (I H) &&& Alg.scribe schnorr_challenge_pad_word)'),
        ('schnorr_challenge', 'literal_bip0340_challenge', '''
@literal_bip0340_challenge_message term >>>
 (((Alg.scribe schnorr_challenge_iv_word &&& O H) >>> @Simplicity.SHA256.hashBlock term) &&& I H)
 >>> @Simplicity.SHA256.hashBlock term >>> @canonical_scalar_normalize term
        '''),
        ('schnorr_tag', 'schnorr_challenge_tag_digest', 'Digest.stringHash "BIP0340/challenge"'),
        ('schnorr_tag', 'schnorr_challenge_tag_iv',
         'Digest.compress Digest.sha256_iv schnorr_challenge_tag_digest schnorr_challenge_tag_digest'),
        ('schnorr_tag', 'schnorr_challenge_iv_word', 'Word.from_hash256 schnorr_challenge_tag_iv'),
        ('schnorr_hash', 'schnorr_challenge_pad_word',
         '@fromZ (WordToZ 8) 0x8000000000000000000000000000000000000000000000000000000000000500'),
        ('schnorr_startup', 'schnorr_startup', r'linear_startup m /\modinfo_fe_state m /\secp_sha_startup m'),
    ]
    for key, name, expected in ports:
        if p.compact(p.definition(s[key], name)) != p.compact(expected):
            raise ValueError('BIP340 literal dependency differs: ' + name)
    statements = re.findall(r'Theorem bip0340_initialized_local_spec\s*:(.*?)\bProof\.', s['schnorr_jet'], re.S)
    expected = ('memcpy_model ->memset_model ->ctz_model -> '
                'secp_jet_initialized_partial_local_spec schnorr_startup f_simplicity_bip_0340_verify '
                'literal_bip0340_args Ty.Unit '
                '(@literal_bip0340_verify (Alg.AssertionSem option_Monad_Zero)).')
    if len(statements) != 1 or p.compact(statements[0]) != p.compact(expected):
        raise ValueError('BIP340 complete success/failure contract differs')


def check_checksig(s):
    """Bind the new Signature hash/composition port; public C proof is pending."""
    for key, fragment in [
        ('catalog', 'CheckSigVerify :: SignatureJet ((Secp256k1.PubKey, Word512),Secp256k1.Sig) ()'),
        ('catalog', 'specificationSignature CheckSigVerify = CheckSig.checkSigVerify'),
        ('scale_ffi', 'check_sig_verify :: ((PubKey, Word512), Sig) -> Maybe ()'),
        ('scale_ffi', 'check_sig_verify = unsafeLocalCoreJet c_check_sig_verify'),
        ('scale_ffi', 'foreign import ccall unsafe "" c_check_sig_verify :: Ptr FrameItem -> Ptr FrameItem -> IO CBool'),
        ('checksig_tags', r'tag = tagIv . intercalate "\US"'),
        ('checksig_tags', 'prefix = ["Simplicity"]'),
        ('checksig_tags', 'signatureTag = tag $ prefix ++ ["Signature"]'),
    ]:
        p.require(s[key], fragment, 'CheckSig binding')
    pad = '0x8' + '0'*124 + '400'
    expected = f"""(scribe iv &&& iden >>> hb)
 &&& scribe (toWord512 {pad}) >>> hb
 where
  iv = toWord256 . integerHash256 . ivHash $ signatureTag
  hb = hashBlock"""
    body = re.search(r"\bsigHash\s+Sha256\.Lib\{\.\.\}\s*=(.*?)\nsigHash'\s*::", s['checksig_program'], re.S)
    if not body or p.compact(body[1]) != p.compact(expected):
        raise ValueError('canonical Signature hash differs')
    body = re.search(r"\bcheckSigVerify\s+sha256\s+libsecp256k1\s*=(.*?)\ncheckSigVerify'\s*::", s['checksig_program'], re.S)
    expected = 'take (oh &&& drop (sigHash sha256)) &&& ih >>> bip_0340_verify libsecp256k1'
    if not body or p.compact(body[1]) != p.compact(expected):
        raise ValueError('canonical CheckSig composition differs')
    ports = [
        ('checksig_literal', 'literal_checksig_args', 'Ty.Prod (Ty.Prod (Word 8) (Word 9)) (Word 9)'),
        ('checksig_literal', 'literal_checksig_hash',
         '(((Alg.scribe checksig_iv_word &&& iden) >>> @Simplicity.SHA256.hashBlock term) &&& Alg.scribe checksig_pad_word) >>> @Simplicity.SHA256.hashBlock term'),
        ('checksig_literal', 'literal_checksig_verify',
         'CS.comp (CS.pair (CS.take (CS.pair (CS.take CS.iden) (CS.drop (@literal_checksig_hash (Alg.Assertion.toCore term))))) (CS.drop CS.iden)) (@literal_bip0340_verify term)'),
        ('checksig_hash', 'checksig_pad_word', '@fromZ (WordToZ 9) ' + pad),
        ('checksig_hash', 'checksig_hash_word',
         '@Simplicity.SHA256.hashBlock Alg.CoreFunSem (@Simplicity.SHA256.hashBlock Alg.CoreFunSem (checksig_iv_word,(ir,h)),checksig_pad_word)'),
        ('checksig_tag', 'checksig_tag_hash', 'MerkleRoot.tag (MerkleRoot.prefix++["Signature"])'),
        ('checksig_tag', 'checksig_iv_word', 'Word.from_hash256 checksig_tag_hash'),
    ]
    for key, name, expected in ports:
        if p.compact(p.definition(s[key], name)) != p.compact(expected):
            raise ValueError('CheckSig literal dependency differs: ' + name)


def test():
    s = {key: p.read_code(path) for key, path in {
        "catalog": REPO / "Haskell/Core/Simplicity/CoreJets.hs",
        "types": REPO / "Haskell/Core/Simplicity/Ty/LibSecp256k1.hs",
        "program": REPO / "Haskell/Core/Simplicity/Programs/LibSecp256k1.hs",
        **{key: COQ / "C" / file for key, file in SCALE_PORT_FILES.items()},
        **{key: COQ / "C" / file for key, file in CHECKED_SCALE_PORT_FILES.items()},
        **{key: COQ / "C" / file for key, file in LINEAR_PORT_FILES.items()},
        "checked_linear_literal": COQ / "C/jet_secp_checked_linear_literal.v",
        "checked_linear_jet": COQ / "C/jet_secp_checked_linear_local.v",
        "linear_verify_literal": COQ / "C/jet_secp_linear_verify_literal.v",
        "linear_verify_jet": COQ / "C/jet_secp_linear_verify_local.v",
        "point_verify_literal": COQ / "C/jet_secp_point_verify_literal.v",
        "point_verify_jet": COQ / "C/jet_secp_point_verify_local.v",
        "schnorr_literal": COQ / "C/jet_secp_schnorr_verify_literal.v",
        "schnorr_challenge": COQ / "C/jet_secp_schnorr_challenge_literal.v",
        "schnorr_tag": COQ / "C/jet_secp_schnorr_tagged_spec.v",
        "schnorr_hash": COQ / "C/jet_secp_schnorr_challenge_hash.v",
        "schnorr_startup": COQ / "C/jet_secp_schnorr_startup.v",
        "schnorr_jet": COQ / "C/jet_secp_bip0340_local.v",
        "checksig_program": REPO / "Haskell/Core/Simplicity/Programs/CheckSig.hs",
        "checksig_tags": REPO / "Haskell/Core/Simplicity/Tags.hs",
        "checksig_literal": COQ / "C/jet_secp_checksig_literal.v",
        "checksig_hash": COQ / "C/jet_secp_checksig_hash.v",
        "checksig_tag": COQ / "C/jet_secp_checksig_tag.v",
        "schnorr_digest": REPO / "Haskell/Core/Simplicity/Digest.hs",
        "scale_ffi": REPO / "Haskell/Core/Simplicity/FFI/Jets.hs",
        "scale_ffi_test": REPO / "Haskell/Tests/Simplicity/FFI/Tests.hs",
        "scale_arith": REPO / "Haskell/Core/Simplicity/Programs/Arith.hs",
        "port": COQ / "C/jet_secp_rescale_literal.v",
        "jet": COQ / "C/jet_secp_rescale_local.v",
        "double_port": COQ / "C/jet_secp_double_literal.v",
        "double_jet": COQ / "C/jet_secp_double_local.v",
        "add_port": COQ / "C/jet_secp_add_literal.v",
        "mixed_jet": COQ / "C/jet_secp_mixed_local.v",
        "projective_jet": COQ / "C/jet_secp_gej_add_local.v",
        "root_port": COQ / "C/jet_secp_root_literal.v",
        "root_jet": COQ / "C/jet_secp_root_local.v",
        "equiv_port": COQ / "C/jet_secp_gej_ge_equiv_literal.v",
        "equiv_jet": COQ / "C/jet_secp_gej_ge_equiv_local.v",
        "projective_equiv_port": COQ / "C/jet_secp_gej_equiv_literal.v",
        "projective_equiv_jet": COQ / "C/jet_secp_gej_equiv_local.v",
        "bit_program": REPO / "Haskell/Core/Simplicity/Programs/Bit.hs",
        "decompress_port": COQ / "C/jet_secp_decompress_literal.v",
        "decompress_jet": COQ / "C/jet_secp_decompress_local.v",
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
    check_gej_ge_equiv(s)
    mutations = [
        ("catalog", "specificationSecp256k1 GejGeEquiv = Secp256k1.gej_ge_equiv",
                    "specificationSecp256k1 GejGeEquiv = Secp256k1.gej_equiv"),
        ("catalog", "GejGeEquiv :: Secp256k1Jet (Secp256k1.GEJ, Secp256k1.GE) Bit",
                    "GejGeEquiv :: Secp256k1Jet (Secp256k1.GEJ, Secp256k1.GE) Word256"),
        ("program", "gej_ge_equiv = take (gej_negate)", "gej_ge_equiv = drop (gej_negate)"),
        ("equiv_port", "O (@literal_gej_negate term)", "I (@literal_gej_negate term)"),
        ("equiv_port", ">>> @literal_gej_ge_add term", ">>> @literal_gej_add term"),
        ("equiv_port", ">>> @literal_gej_is_infinity term", ">>> @literal_gej_x_equiv term"),
        ("catalog", "implementationSecp256k1 GejGeEquiv = \\(a,b) -> return . toBit $ LibSecp256k1.gej_ge_equiv",
                    "implementationSecp256k1 GejGeEquiv = \\(a,b) -> return . toBit $ LibSecp256k1.gej_equiv"),
        ("types", "type GEJ = (GE, FE)", "type GEJ = (FE, GE)"),
        ("equiv_jet", "secp_jet_local_spec f_simplicity_gej_ge_equiv",
                      "False -> secp_jet_local_spec f_simplicity_gej_ge_equiv"),
        ("equiv_jet", "f_simplicity_gej_ge_equiv", "f_simplicity_gej_equiv"),
        ("equiv_jet", "(Word 8)", "(Word 7)"),
        ("equiv_jet", "(Ty.Sum Ty.Unit Ty.Unit)", "(Word 8)"),
        ("equiv_jet", "@literal_gej_ge_equiv Alg.CoreFunSem", "@literal_gej_x_equiv Alg.CoreFunSem"),
    ]
    for key, old, new in mutations:
        if old not in s[key]:
            raise ValueError("inactive mixed-equivalence mutation fixture: " + old)
        changed = dict(s)
        changed[key] = s[key].replace(old, new, 1)
        try:
            check_gej_ge_equiv(changed)
        except ValueError:
            continue
        raise ValueError("accepted mixed-equivalence source mutation: " + old)
    print(f"GejGeEquiv catalog/literal/full contract match; {len(mutations)} targeted mutations rejected")

    check_decompress(s)
    mutations = [
        ("catalog", "specificationSecp256k1 Decompress = Secp256k1.decompress",
                    "specificationSecp256k1 Decompress = Secp256k1.ge_normalize"),
        ("catalog", "implementationSecp256k1 Decompress = FFI.decompress",
                    "implementationSecp256k1 Decompress = FFI.ge_negate"),
        ("catalog", "Decompress :: Secp256k1Jet Secp256k1.Point (Either () Secp256k1.GE)",
                    "Decompress :: Secp256k1Jet Secp256k1.Point Secp256k1.GE"),
        ("types", "type Point = (Bit, FE)", "type Point = (FE, Bit)"),
        ("program", "k = drop (drop fe_normalize)", "k = take (drop fe_normalize)"),
        ("program", "cond fe_negate iden)", "cond iden fe_negate)"),
        ("program", "y_from_x = (unit >>> scribe256 7)", "y_from_x = (unit >>> scribe256 8)"),
        ("bit_program", "xor s t = s &&& iden >>> cond (not t) t",
                        "xor s t = s &&& iden >>> cond t (not t)"),
        ("decompress_port", "Bit.not (I (O H))", "Bit.not (O (I H))"),
        ("decompress_port", "I (I (@canonical_fe_normalize term))", "O (I (@canonical_fe_normalize term))"),
        ("decompress_port", "case (injl unit) (injr (@literal_decompress_point term))",
                            "case (injr (@literal_decompress_point term)) (injl unit)"),
        ("decompress_jet", "secp_jet_local_spec f_simplicity_decompress",
                           "False -> secp_jet_local_spec f_simplicity_decompress"),
        ("decompress_jet", "f_simplicity_decompress", "f_simplicity_ge_negate"),
        ("decompress_jet", "(Word 8)", "(Word 7)"),
        ("decompress_jet", "(@literal_decompress Simplicity.Alg.CoreFunSem)",
                           "(@literal_y_from_x Simplicity.Alg.CoreFunSem)"),
    ]
    for key, old, new in mutations:
        if old not in s[key]:
            raise ValueError("inactive decompression mutation fixture: " + old)
        changed = dict(s)
        changed[key] = s[key].replace(old, new, 1)
        try:
            check_decompress(changed)
        except ValueError:
            continue
        raise ValueError("accepted decompression source mutation: " + old)
    print(f"Decompress catalog/literal/full contract match; {len(mutations)} targeted mutations rejected")

    check_projective(s)
    mutations = [
        ("catalog", "specificationSecp256k1 GejAdd = Secp256k1.gej_add",
                    "specificationSecp256k1 GejAdd = Secp256k1.gej_ge_add"),
        ("catalog", "implementationSecp256k1 GejAdd = FFI.gej_add",
                    "implementationSecp256k1 GejAdd = FFI.gej_ge_add"),
        ("catalog", "GejAdd :: Secp256k1Jet (Secp256k1.GEJ,Secp256k1.GEJ) Secp256k1.GEJ",
                    "GejAdd :: Secp256k1Jet (Secp256k1.GEJ,Secp256k1.GE) Secp256k1.GEJ"),
        ("types", "type GEJ = (GE, FE)", "type GEJ = (FE, GE)"),
        ("program", "gej_add = gej_add_ex >>> ih", "gej_add = gej_add_ex >>> oh"),
        ("add_port", "@literal_gej_add_ex term >>> I H", "@literal_gej_add_ex term >>> O H"),
        ("projective_jet", "secp_jet_local_spec f_simplicity_gej_add",
                           "False -> secp_jet_local_spec f_simplicity_gej_add"),
        ("projective_jet", "f_simplicity_gej_add", "f_secp256k1_gej_add_var"),
        ("projective_jet", "(Word 8)", "(Word 7)"),
        ("projective_jet", "@literal_gej_add Alg.CoreFunSem", "@literal_gej_ge_add Alg.CoreFunSem"),
    ]
    for key, old, new in mutations:
        if old not in s[key]:
            raise ValueError("inactive projective-addition mutation fixture: " + old)
        changed = dict(s)
        changed[key] = s[key].replace(old, new, 1)
        try:
            check_projective(changed)
        except ValueError:
            continue
        raise ValueError("accepted projective-addition source mutation: " + old)
    print(f"GejAdd catalog/literal/full contract match; {len(mutations)} targeted mutations rejected")

    check_gej_equiv(s)
    mutations = [
        ("catalog", "specificationSecp256k1 GejEquiv = Secp256k1.gej_equiv",
                    "specificationSecp256k1 GejEquiv = Secp256k1.gej_ge_equiv"),
        ("catalog", "GejEquiv :: Secp256k1Jet (Secp256k1.GEJ, Secp256k1.GEJ) Bit",
                    "GejEquiv :: Secp256k1Jet (Secp256k1.GEJ, Secp256k1.GE) Bit"),
        ("catalog", "LibSecp256k1.gej_equiv (fromGEJ a) (fromGEJ b)",
                    "LibSecp256k1.gej_equiv (fromGEJ a) (fromGE b)"),
        ("program", "gej_equiv = take (gej_negate)", "gej_equiv = drop (gej_negate)"),
        ("program", "gej_equiv = take (gej_negate) &&& ih >>> gej_add",
                    "gej_equiv = take (gej_negate) &&& ih >>> gej_ge_add"),
        ("projective_equiv_port", "O (@literal_gej_negate term)", "I (@literal_gej_negate term)"),
        ("projective_equiv_port", ">>> @literal_gej_add term", ">>> @literal_gej_ge_add term"),
        ("projective_equiv_port", ">>> @literal_gej_is_infinity term", ">>> @literal_gej_x_equiv term"),
        ("projective_equiv_jet", "secp_jet_local_spec f_simplicity_gej_equiv",
                               "False -> secp_jet_local_spec f_simplicity_gej_equiv"),
        ("projective_equiv_jet", "f_simplicity_gej_equiv", "f_secp256k1_gej_eq_var"),
        ("projective_equiv_jet", "(Word 8)", "(Word 7)"),
        ("projective_equiv_jet", "(Ty.Sum Ty.Unit Ty.Unit)", "(Word 8)"),
        ("projective_equiv_jet", "@literal_gej_equiv Alg.CoreFunSem", "@literal_gej_ge_equiv Alg.CoreFunSem"),
    ]
    for key, old, new in mutations:
        if old not in s[key]:
            raise ValueError("inactive projective-equivalence mutation fixture: " + old)
        changed = dict(s)
        changed[key] = s[key].replace(old, new, 1)
        try:
            check_gej_equiv(changed)
        except ValueError:
            continue
        raise ValueError("accepted projective-equivalence source mutation: " + old)
    print(f"GejEquiv catalog/literal/full contract match; {len(mutations)} targeted mutations rejected")


    port_count = check_off_curve_scale(s)
    mutations = [
        ("types", "type Scalar = Word256", "type Scalar = Word128"),
        ("program", "off_curve_scale :: term (Scalar, GEJ) GEJ", "off_curve_scale :: term (Scalar, GE) GEJ"),
        ("scale_ffi", "off_curve_scale = unsafeLocalCoreJet c_off_curve_scale",
                      "off_curve_scale = unsafeLocalCoreJet c_scale"),
        ("scale_ffi", 'foreign import ccall unsafe "" c_off_curve_scale',
                      'foreign import ccall unsafe "" c_scale_wrong'),
        ("scale_ffi_test", "testCoreEval Prog.off_curve_scale", "testCoreEval Prog.scale"),
        ("program", "off_curve_scale = iden &&& (unit >>> zero256)",
                    "off_curve_scale = iden &&& (unit >>> fe_one)"),
        ("program", ">>> cond (drop generate) body", ">>> cond body (drop generate)"),
        ("program", ">>> ioh &&& (oh &&& iih >>> fe_multiply)",
                    ">>> ioh &&& (iih &&& oh >>> fe_multiply)"),
        ("program", ">>> lookupTable5 >>> ge_scale_lambda", ">>> lookupTable5 >>> ge_negate"),
        ("program", "scalarTable5 = iden &&& gej_double", "scalarTable5 = iden &&& gej_negate"),
        ("program", "g1 = scribe256 0x3086", "g1 = scribe256 0x3087"),
        ("program", "negB1 = scribe128 0xe443", "negB1 = scribe128 0xe444"),
        ("program", "c1 &&& c2 >>> sub256", "c2 &&& c1 >>> sub256"),
        ("program", "wnaf5step1 = drop lsb128", "wnaf5step1 = drop msb128"),
        ("program", "wnaf5step1 = drop lsb128 &&& (oh &&& fullShift128)",
                    "wnaf5step1 = drop lsb128 &&& iden"),
        ("program", "lookupTable5 = oooh &&& ooih", "lookupTable5 = ooih &&& oooh"),
        ("program", "ge_scale_lambda = take fe_multiply_beta &&& drop fe_normalize",
                    "ge_scale_lambda = take fe_multiply_beta &&& ih"),
        ("scale_complete", "Bit.cond (I (@literal_generate term)) (@literal_strauss_body term)",
                           "Bit.cond (@literal_strauss_body term) (I (@literal_generate term))"),
        ("scale_complete", "unit >>> @Word.zero 8 term", "unit >>> @Word.zero 7 term"),
        ("scale_complete", "O H &&& I I H", "I I H &&& O H"),
        ("scale_steps", ">>> @literal_strauss_block 7 term", ">>> @literal_strauss_block 6 term"),
        ("scale_steps", ">>> @literal_strauss_step term", ">>> @literal_strauss_block 0 term"),
        ("scale_steps", ">>> @literal_lookup5 term >>> @literal_ge_scale_lambda term",
                        ">>> @literal_lookup5 term"),
        ("scale_table", "I O H &&& (O O O H &&& I I O H)", "I O H &&& (I I O H &&& O O O H)"),
        ("scale_table", "O H &&& I I H >>> @literal_fe_multiply term",
                        "I I H &&& O H >>> @literal_fe_multiply term"),
        ("scale_split", "literal_split_product Datatypes.true term &&& @literal_split_product Datatypes.false",
                        "literal_split_product Datatypes.false term &&& @literal_split_product Datatypes.true"),
        ("scale_round", "@full_increment_word_spec term 7", "@full_increment_word_spec term 6"),
        ("scale_wnaf5", "@left_extend_word_spec 2 5 term", "@left_extend_word_spec 2 4 term"),
        ("scale_wnaf5", "I (I (I (I I I H)))", "I (I (I (I I O H)))"),
        ("scale_wnaf", "rec >>> (O rec &&& I H)", "rec >>> (I H &&& O rec)"),
        ("scale_wnaf", "@literal_wnaf_block 4 term", "@literal_wnaf_block 3 term"),
        ("scale_lookup", "Bit.cond", "Bit.or"),
        ("scale_ge_lambda", "I (@canonical_fe_normalize term)", "I H"),
        ("scale_startup", "strauss_zero_global_state m", "False /\\ strauss_zero_global_state m"),
        ("scale_jet", "memset_model -> secp_jet_initialized_local_spec",
                      "memset_model -> False -> secp_jet_initialized_local_spec"),
        ("scale_jet", "f_simplicity_off_curve_scale", "f_simplicity_scale"),
        ("scale_jet", "(Word 8)", "(Word 7)"),
        ("scale_jet", "@literal_off_curve_scale Alg.CoreFunSem", "@literal_generate Alg.CoreFunSem"),
    ]
    for key, old, new in mutations:
        if old not in s[key]:
            raise ValueError("inactive off-curve scale mutation fixture: " + old)
        changed = dict(s)
        changed[key] = s[key].replace(old, new, 1)
        try:
            check_off_curve_scale(changed)
        except ValueError:
            continue
        raise ValueError("accepted off-curve scale source mutation: " + old)
    print(f"off_curve_scale library/FFI/{port_count} literal ports/full contract match; "
          f"{len(mutations)} targeted mutations rejected")

    check_off_curve_linear(s)
    mutations = [
        ('program', 'term ((Scalar, GEJ), Scalar) GEJ', 'term ((Scalar, GE), Scalar) GEJ'),
        ('scale_ffi', 'off_curve_linear_combination_1 = unsafeLocalCoreJet c_off_curve_linear_combination_1',
                      'off_curve_linear_combination_1 = unsafeLocalCoreJet c_off_curve_scale'),
        ('scale_ffi', 'foreign import ccall unsafe "" c_off_curve_linear_combination_1',
                      'foreign import ccall unsafe "" c_off_curve_linear_combination_2'),
        ('scale_ffi_test', 'testCoreEval Prog.off_curve_linear_combination_1', 'testCoreEval Prog.off_curve_scale'),
        ('program', '>>> cond (drop generate) body', '>>> cond body (drop generate)'),
        ('program', 'go SingleV = cond (gej_double', 'go SingleV = cond (gej_negate'),
        ('program', 'scaleConstant generate128 w', 'scaleConstant generate0 w'),
        ('program', 'generateSigned word16 >>> gej_norm', 'generateSigned word8 >>> gej_norm'),
        ('program', '0x8f68b9d2f63b5f339239c1ad981f162ee88c5678723ea3351b7b444c9ec4c0da', '0x8f68b9d2f63b5f339239c1ad981f162ee88c5678723ea3351b7b444c9ec4c0db'),
        ('linear_generator', '0x79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798', '0x79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81799'),
        ('linear_generator', '(O (I H) &&& ((O (O H) &&& I H) >>> rec))', '(I H &&& ((O (O H) &&& I H) >>> rec))'),
        ('linear_generator', '@literal_generate_signed 4 term', '@literal_generate_signed 3 term'),
        ('linear_generator', 'Alg.Core.Combinators.copair (@literal_gej_infinity term)', 'Alg.Core.Combinators.copair (@literal_gej_double term)'),
        ('linear_norm', 'I (@literal_fe_invert term)', 'I (@literal_fe_normalize term)'),
        ('linear_startup', 'split_constants_ready m /\\ beta_initialized m', 'False /\\ split_constants_ready m /\\ beta_initialized m'),
        ('linear_startup', '(forall h,generator_table_state h m)', '(forall h,generator_table_state h m) /\\ False'),
        ('linear_jet', 'memset_model -> secp_jet_initialized_local_spec', 'memset_model -> False -> secp_jet_initialized_local_spec'),
        ('linear_jet', 'f_simplicity_off_curve_linear_combination_1', 'f_simplicity_off_curve_scale'),
        ('linear_jet', 'literal_strauss_args literal_table_gej', '(Word 8) literal_table_gej'),
        ('linear_jet', '@literal_off_curve_linear_combination_1 Alg.CoreFunSem', '@literal_strauss_body Alg.CoreFunSem'),
    ]
    for key, old, new in mutations:
        if old not in s[key]:
            raise ValueError('inactive linear-combination mutation fixture: ' + old)
        changed = dict(s)
        changed[key] = s[key].replace(old, new, 1)
        try:
            check_off_curve_linear(changed)
        except ValueError:
            continue
        raise ValueError('accepted linear-combination source mutation: ' + old)
    print(f'off_curve_linear_combination_1 library/FFI/generator ports/full contract match; {len(mutations)} targeted mutations rejected')



    check_checked_scale(s)
    mutations = [
        ("catalog", "specificationSecp256k1 Scale = Secp256k1.scale",
                    "specificationSecp256k1 Scale = Secp256k1.gej_double"),
        ("catalog", "implementationSecp256k1 Scale = FFI.scale",
                    "implementationSecp256k1 Scale = FFI.off_curve_scale"),
        ("catalog", "Scale :: Secp256k1Jet (Secp256k1.Scalar,Secp256k1.GEJ) Secp256k1.GEJ",
                    "Scale :: Secp256k1Jet (Secp256k1.Scalar,Secp256k1.GE) Secp256k1.GEJ"),
        ("program", "scale m = drop (gej_is_on_curve m)", "scale m = take (gej_is_on_curve m)"),
        ("program", "scale m = drop (gej_is_on_curve m) &&& (off_curve_scale m) >>> assertr cmrFail0 ih",
                    "scale m = drop (gej_is_on_curve m) &&& (off_curve_scale m) >>> assertl ih cmrFail0"),
        ("scale_ffi", "scale = unsafeLocalCoreJet c_scale", "scale = unsafeLocalCoreJet c_generate"),
        ("checked_literal", "SC.drop (@literal_gej_is_on_curve term)", "SC.take (@literal_gej_is_on_curve term)"),
        ("checked_literal", "SC.pair (SC.drop", "SC.pair (SC.take"),
        ("checked_literal", "assertr assertion_cmr_fail0", "assertr assertion_hash0"),
        ("checked_literal", "(SC.drop SC.iden)", "(SC.take SC.iden)"),
        ("checked_startup", "secp_symbol_block _ng__1", "secp_symbol_block _ng"),
        ("checked_startup", "scale_startup_at checked_zero_block m", "False /\\ scale_startup_at checked_zero_block m"),
        ("checked_ready", "zero_scalar_state bng m /\\", "False /\\ zero_scalar_state bng m /\\"),
        ("checked_zero", "readonly_region_bounds m bng 0 32", "True"),
        ("checked_contract", "jet_partial_return (spec a)", "Vint Int.one"),
        ("checked_contract", "| None=>True end", "| None=>False end"),
        ("checked_contract", "Mem.load chunk mf b ofs=Mem.load chunk m b ofs", "True"),
        ("checked_contract", "Ready m -> frame_base_valid", "Ready m -> False -> frame_base_valid"),
        ("checked_jet", "memset_model -> secp_jet_initialized_partial_local_spec",
                        "memset_model -> False -> secp_jet_initialized_partial_local_spec"),
        ("checked_jet", "f_simplicity_scale", "f_simplicity_off_curve_scale"),
        ("checked_jet", "Alg.AssertionSem option_Monad_Zero", "Alg.CoreFunSem"),
    ]
    for key, old, new in mutations:
        if old not in s[key]:
            raise ValueError("inactive checked Scale mutation fixture: " + old)
        changed = dict(s)
        changed[key] = s[key].replace(old, new, 1)
        try:
            check_checked_scale(changed)
        except ValueError:
            continue
        raise ValueError("accepted checked Scale source mutation: " + old)
    print(f"Scale catalog/assertion/initialized partial contract match; {len(mutations)} targeted mutations rejected")
    check_checked_linear(s)
    mutations = [
        ('catalog', 'specificationSecp256k1 LinearCombination1 = Secp256k1.linear_combination_1',
                    'specificationSecp256k1 LinearCombination1 = Secp256k1.scale'),
        ('catalog', 'implementationSecp256k1 LinearCombination1 = FFI.linear_combination_1',
                    'implementationSecp256k1 LinearCombination1 = FFI.off_curve_linear_combination_1'),
        ('catalog', 'LinearCombination1 :: Secp256k1Jet ((Secp256k1.Scalar,Secp256k1.GEJ),Secp256k1.Scalar)',
                    'LinearCombination1 :: Secp256k1Jet ((Secp256k1.Scalar,Secp256k1.GE),Secp256k1.Scalar)'),
        ('program', 'linear_combination_1 m = take (drop (gej_is_on_curve m))',
                    'linear_combination_1 m = drop (drop (gej_is_on_curve m))'),
        ('program', '(off_curve_linear_combination_1 m) >>> assertr cmrFail0 ih',
                    '(off_curve_linear_combination_1 m) >>> assertl ih cmrFail0'),
        ('scale_ffi', 'linear_combination_1 = unsafeLocalCoreJet c_linear_combination_1',
                      'linear_combination_1 = unsafeLocalCoreJet c_off_curve_linear_combination_1'),
        ('scale_ffi', 'foreign import ccall unsafe "" c_linear_combination_1',
                      'foreign import ccall unsafe "" c_linear_combination_2'),
        ('checked_linear_literal', 'SC.take (SC.drop (@literal_gej_is_on_curve term))',
                                  'SC.drop (SC.drop (@literal_gej_is_on_curve term))'),
        ('checked_linear_literal', 'assertr assertion_cmr_fail0', 'assertr assertion_hash0'),
        ('checked_linear_literal', '(@literal_off_curve_linear_combination_1 term)', '(@literal_strauss_body term)'),
        ('linear_startup', '(forall h,generator_table_state h m)', '(forall h,generator_table_state h m) /\\ False'),
        ('checked_contract', '| None=>True end', '| None=>False end'),
        ('checked_linear_jet', 'memset_model -> secp_jet_initialized_partial_local_spec',
                              'memset_model -> secp_jet_initialized_local_spec'),
        ('checked_linear_jet', 'memset_model -> secp_jet_initialized_partial_local_spec',
                              'memset_model -> False -> secp_jet_initialized_partial_local_spec'),
        ('checked_linear_jet', 'f_simplicity_linear_combination_1', 'f_simplicity_off_curve_linear_combination_1'),
        ('checked_linear_jet', 'literal_strauss_args literal_table_gej', '(Word 8) literal_table_gej'),
        ('checked_linear_jet', '@literal_checked_linear (Alg.AssertionSem option_Monad_Zero)',
                              '@literal_checked_linear Alg.CoreFunSem'),
    ]
    for key, old, new in mutations:
        if old not in s[key]:
            raise ValueError('inactive checked linear mutation fixture: ' + old)
        changed = dict(s)
        changed[key] = s[key].replace(old, new, 1)
        try:
            check_checked_linear(changed)
        except ValueError:
            continue
        raise ValueError('accepted checked linear source mutation: ' + old)
    print(f'LinearCombination1 catalog/assertion/initialized partial contract match; {len(mutations)} targeted mutations rejected')

    check_linear_verify(s)
    mutations = [
        ('catalog', 'specificationSecp256k1 LinearVerify1 = Secp256k1.linear_verify_1', 'specificationSecp256k1 LinearVerify1 = Secp256k1.point_verify_1'),
        ('catalog', 'implementationSecp256k1 LinearVerify1 = FFI.linear_verify_1', 'implementationSecp256k1 LinearVerify1 = FFI.point_verify_1'),
        ('program', 'linear_verify_1 m = assert (linear_check_1 m)', 'linear_verify_1 m = assert (point_check_1 m)'),
        ('program', 'linear_check_1 = and (drop ge_is_on_curve)', 'linear_check_1 = and (take ge_is_on_curve)'),
        ('program', 'take (take (drop ge_is_on_curve))', 'take (drop (drop ge_is_on_curve))'),
        ('scale_ffi', 'linear_verify_1 = unsafeLocalCoreJet c_linear_verify_1', 'linear_verify_1 = unsafeLocalCoreJet c_point_verify_1'),
        ('linear_verify_literal', 'I (@literal_ge_is_on_curve term)', 'O (@literal_ge_is_on_curve term)'),
        ('linear_verify_literal', '@literal_fe_one256 term', '@literal_fe_zero256 term'),
        ('linear_verify_literal', '@literal_ge_negate term', '@literal_ge_scale_lambda term'),
        ('linear_verify_literal', '@literal_gej_ge_add term', '@literal_gej_add term'),
        ('linear_verify_literal', 'assertr assertion_cmr_fail0', 'assertr assertion_hash0'),
        ('linear_verify_jet', 'memset_model -> secp_jet_initialized_partial_local_spec', 'memset_model -> False -> secp_jet_initialized_partial_local_spec'),
        ('linear_verify_jet', 'f_simplicity_linear_verify_1', 'f_simplicity_point_verify_1'),
        ('linear_verify_jet', 'literal_linear_verify_args Ty.Unit', 'literal_strauss_args Ty.Unit'),
    ]
    for key, old, new in mutations:
        if old not in s[key]:
            raise ValueError('inactive linear verifier mutation fixture: ' + old)
        changed = dict(s)
        changed[key] = s[key].replace(old, new, 1)
        try:
            check_linear_verify(changed)
        except ValueError:
            continue
        raise ValueError('accepted linear verifier source mutation: ' + old)
    print(f'LinearVerify1 catalog/assertion/initialized partial contract match; {len(mutations)} targeted mutations rejected')


    check_point_verify(s)
    mutations = [
        ('catalog', 'PointVerify1 :: Secp256k1Jet (((Secp256k1.Scalar,Secp256k1.Point),Secp256k1.Scalar),Secp256k1.Point) ()',
                    'PointVerify1 :: Secp256k1Jet (((Secp256k1.Scalar,Secp256k1.GE),Secp256k1.Scalar),Secp256k1.GE) ()'),
        ('catalog', 'specificationSecp256k1 PointVerify1 = Secp256k1.point_verify_1', 'specificationSecp256k1 PointVerify1 = Secp256k1.linear_verify_1'),
        ('catalog', 'implementationSecp256k1 PointVerify1 = FFI.point_verify_1', 'implementationSecp256k1 PointVerify1 = FFI.linear_verify_1'),
        ('program', 'point_verify_1 m = assert (point_check_1 m)', 'point_verify_1 m = assert (linear_check_1 m)'),
        ('program', 'drop (take (drop decompress))', 'drop (drop (take decompress))'),
        ('program', 'drop decompress &&& oh >>> match false k1', 'drop decompress &&& oh >>> match true k1'),
        ('program', '((iooh &&& oh) &&& ioih) &&& iih >>> linear_check_1', '((ioih &&& oh) &&& iooh) &&& iih >>> linear_check_1'),
        ('scale_ffi', 'point_verify_1 = unsafeLocalCoreJet c_point_verify_1', 'point_verify_1 = unsafeLocalCoreJet c_linear_verify_1'),
        ('point_verify_literal', 'Ty.Prod Bit (Word 8)', 'Ty.Prod (Word 8) Bit'),
        ('point_verify_literal', 'I (O (O H)) &&& O H', 'I (O (I H)) &&& O H'),
        ('point_verify_literal', 'case Bit.false (@literal_point_check_k2 term)', 'case Bit.true (@literal_point_check_k2 term)'),
        ('point_verify_literal', 'I (@literal_decompress term) &&& O H', 'O (@literal_decompress term) &&& O H'),
        ('point_verify_literal', 'assertr assertion_cmr_fail0', 'assertr assertion_hash0'),
        ('point_verify_jet', 'memset_model -> secp_jet_initialized_partial_local_spec', 'memset_model -> False -> secp_jet_initialized_partial_local_spec'),
        ('point_verify_jet', 'f_simplicity_point_verify_1', 'f_simplicity_linear_verify_1'),
        ('point_verify_jet', 'literal_point_verify_args Ty.Unit', 'literal_linear_verify_args Ty.Unit'),
    ]
    for key, old, new in mutations:
        if old not in s[key]:
            raise ValueError('inactive point verifier mutation fixture: ' + old)
        changed = dict(s)
        changed[key] = s[key].replace(old, new, 1)
        try:
            check_point_verify(changed)
        except ValueError:
            continue
        raise ValueError('accepted point verifier source mutation: ' + old)
    print(f'PointVerify1 catalog/assertion/initialized partial contract match; {len(mutations)} targeted mutations rejected')

    check_bip0340(s)
    mutations = [
        ('catalog', 'Bip0340Verify :: SignatureJet ((Secp256k1.PubKey, Word256),Secp256k1.Sig) ()',
         'Bip0340Verify :: SignatureJet ((Secp256k1.PubKey, Word512),Secp256k1.Sig) ()'),
        ('catalog', 'specificationSignature Bip0340Verify = Secp256k1.bip_0340_verify',
         'specificationSignature Bip0340Verify = CheckSig.checkSigVerify'),
        ('catalog', 'implementationSignature Bip0340Verify a = FFI.bip_0340_verify a',
         'implementationSignature Bip0340Verify a = FFI.check_sig_verify a'),
        ('types', 'type Sig = (Word256, Word256)', 'type Sig = (Word128, Word256)'),
        ('scale_ffi', 'bip_0340_verify = unsafeLocalCoreJet c_bip_0340_verify',
         'bip_0340_verify = unsafeLocalCoreJet c_check_sig_verify'),
        ('program', 'bip_0340_verify m = assert (bip_0340_check m)', 'bip_0340_verify m = assert true'),
        ('program', 'pubkey_check >>> cond (injr ((unit >>> true) &&& iden))',
         'pubkey_check >>> cond (injr ((unit >>> false) &&& iden))'),
        ('program', 'iih &&& (ioh &&& oh)', 'iih &&& (oih &&& oh)'),
        ('program', 'm >>> (iv &&& oh >>> hashBlock) &&& ih >>> hashBlock >>> scalar_normalize',
         'm >>> (iv &&& ih >>> hashBlock) &&& oh >>> hashBlock >>> scalar_normalize'),
        ('program', 'toWord256 0x8000000000000000000000000000000000000000000000000000000000000500',
         'toWord256 0x8000000000000000000000000000000000000000000000000000000000000300'),
        ('schnorr_digest', 'tagIv tag = compress noTagIv (tagDigest, tagDigest)',
         'tagIv tag = compress noTagIv (tagDigest, hash0)'),
        ('schnorr_literal', 'Alg.scribe canonical_group_word', 'Alg.scribe canonical_field_word'),
        ('schnorr_literal', 'I (I H) &&& (I (O H) &&& O H)', 'I (I H) &&& (O (I H) &&& O H)'),
        ('schnorr_literal', 'case Bit.false (@literal_bip0340_k1 term)', 'case Bit.true (@literal_bip0340_k1 term)'),
        ('schnorr_literal', 'assertr assertion_cmr_fail0', 'assertr assertion_hash0'),
        ('schnorr_challenge', 'I (O H) &&& O (O H)', 'O (I H) &&& O (O H)'),
        ('schnorr_challenge', '>>> @canonical_scalar_normalize term', '>>> @canonical_fe_normalize term'),
        ('schnorr_tag', '"BIP0340/challenge"', '"BIP0340/Challenge"'),
        ('schnorr_hash', '0x8000000000000000000000000000000000000000000000000000000000000500',
         '0x8000000000000000000000000000000000000000000000000000000000000300'),
        ('schnorr_startup', r'linear_startup m /\modinfo_fe_state m /\secp_sha_startup m', 'False'),
        ('schnorr_jet', 'memcpy_model ->memset_model ->ctz_model ->', 'memcpy_model ->memset_model ->ctz_model ->False ->'),
        ('schnorr_jet', 'f_simplicity_bip_0340_verify', 'f_secp256k1_schnorrsig_verify'),
        ('schnorr_jet', 'literal_bip0340_args Ty.Unit', '(Word 8) Ty.Unit'),
    ]
    for key, old, new in mutations:
        if old not in s[key]:
            raise ValueError('inactive BIP340 mutation fixture: ' + old)
        changed = dict(s)
        changed[key] = s[key].replace(old, new, 1)
        try:
            check_bip0340(changed)
        except ValueError:
            continue
        raise ValueError('accepted BIP340 source mutation: ' + old)
    print(f'BIP340 catalog/tag/challenge/assertion/complete public contract match; {len(mutations)} targeted mutations rejected')


    check_checksig(s)
    mutations = [
        ('catalog', 'specificationSignature CheckSigVerify = CheckSig.checkSigVerify', 'specificationSignature CheckSigVerify = Secp256k1.bip_0340_verify'),
        ('scale_ffi', 'check_sig_verify = unsafeLocalCoreJet c_check_sig_verify', 'check_sig_verify = unsafeLocalCoreJet c_bip_0340_verify'),
        ('checksig_tags', 'prefix = ["Simplicity"]', 'prefix = ["simplicity"]'),
        ('checksig_tags', 'signatureTag = tag $ prefix ++ ["Signature"]', 'signatureTag = tag $ prefix ++ ["signature"]'),
        ('checksig_tags', r'intercalate "\US"', r'intercalate "\NUL"'),
        ('checksig_program', 'take (oh &&& drop (sigHash sha256))', 'take (oh &&& drop iden)'),
        ('checksig_program', 'ivHash $ signatureTag', 'ivHash $ hiddenTag'),
        ('checksig_literal', 'CS.take CS.iden', 'CS.drop CS.iden'),
        ('checksig_literal', 'Ty.Prod (Ty.Prod (Word 8) (Word 9)) (Word 9)', 'Ty.Prod (Ty.Prod (Word 8) (Word 8)) (Word 9)'),
        ('checksig_hash', 'checksig_iv_word,(ir,h)', 'checksig_iv_word,(h,ir)'),
        ('checksig_tag', '["Signature"]', '["signature"]'),
    ]
    for key in ['checksig_program', 'checksig_hash']:
        pad = '0x8' + '0'*124 + '400'
        mutations.append((key, pad, '0x8' + '0'*124 + '200'))
    for key, old, new in mutations:
        if old not in s[key]:
            raise ValueError('inactive CheckSig mutation fixture: ' + old)
        changed = dict(s)
        changed[key] = s[key].replace(old, new, 1)
        try:
            check_checksig(changed)
        except ValueError:
            continue
        raise ValueError('accepted CheckSig source mutation: ' + old)
    print(f'CheckSig canonical tag/hash/composition port match (public C contract pending); {len(mutations)} targeted mutations rejected')


if __name__ == "__main__":
    test()
