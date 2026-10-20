"""GejRescale catalog/term/contract correspondence; not a C execution proof.

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


def test():
    s = {key: p.read_code(path) for key, path in {
        "catalog": REPO / "Haskell/Core/Simplicity/CoreJets.hs",
        "types": REPO / "Haskell/Core/Simplicity/Ty/LibSecp256k1.hs",
        "program": REPO / "Haskell/Core/Simplicity/Programs/LibSecp256k1.hs",
        "port": COQ / "C/jet_secp_rescale_literal.v",
        "jet": COQ / "C/jet_secp_rescale_local.v",
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


if __name__ == "__main__":
    test()
