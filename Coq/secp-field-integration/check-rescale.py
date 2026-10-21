"""Point rescale/doubling catalog/term/contract correspondence; not C execution.

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


def test():
    s = {key: p.read_code(path) for key, path in {
        "catalog": REPO / "Haskell/Core/Simplicity/CoreJets.hs",
        "types": REPO / "Haskell/Core/Simplicity/Ty/LibSecp256k1.hs",
        "program": REPO / "Haskell/Core/Simplicity/Programs/LibSecp256k1.hs",
        "port": COQ / "C/jet_secp_rescale_literal.v",
        "jet": COQ / "C/jet_secp_rescale_local.v",
        "double_port": COQ / "C/jet_secp_double_literal.v",
        "double_jet": COQ / "C/jet_secp_double_local.v",
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


if __name__ == "__main__":
    test()
