#!/usr/bin/env python3
"""Preserve the reviewed literal fe_normalize port and its public contract.

This is a source correspondence gate, supplementing Coq kernel checks. The
Haskell program uses the same subtraction, projections and conditional as the
Coq port. The field constant is compared numerically and the specialization is
checked at Word256; this gate does not prove C execution.
"""
import os
import re
from pathlib import Path

COQ = Path(__file__).resolve().parent
REPO = Path(os.environ.get("JET_C_REPO", COQ.parent))


def compact(text):
    return re.sub(r"\s+", "", text)


def definition(source, name):
    match = re.search(rf"\bDefinition\s+{name}\b.*?:=(.*?)\.\s*(?:\n|$)", source, re.S)
    if not match:
        raise ValueError(f"missing definition: {name}")
    return match[1]


def require(text, fragment, label):
    if compact(fragment) not in compact(text):
        raise ValueError(f"canonical fe_normalize correspondence differs: {label}")


def check(coq=COQ, repo=REPO):
    catalog = (repo / "Haskell/Core/Simplicity/CoreJets.hs").read_text()
    program = (repo / "Haskell/Core/Simplicity/Programs/LibSecp256k1.hs").read_text()
    types = (repo / "Haskell/Core/Simplicity/Ty/LibSecp256k1.hs").read_text()
    field = (repo / "Haskell/Core/Simplicity/LibSecp256k1/Spec.hs").read_text()
    port = (coq / "C/jet_secp_canonical_normalize.v").read_text()
    local = (coq / "C/jet_secp_normalize_local.v").read_text()
    require(catalog, "specificationSecp256k1 FeNormalize = Secp256k1.fe_normalize", "catalog")
    require(catalog, "FeNormalize :: Secp256k1Jet Secp256k1.FE Secp256k1.FE", "jet type")
    require(types, "type FE = Word256", "full input domain")
    require(program, "scribeFeOrder = scribe256 LibSecp256k1.fieldOrder", "field word")
    require(program, "sub256 = Arith.subtract word256", "subtraction specialization")
    # Select the implementation record, excluding the earlier mapLib adapter.
    implementation = program.split("lib@Lib{..} = Lib {", 1)
    hs = re.search(r"\bfe_normalize\s*=(.*?)\n\s*,\s*fe_zero\b",
                   implementation[1], re.S) if len(implementation) == 2 else None
    expected_hs = """(iden &&& (unit >>> scribeFeOrder) >>> sub256) &&& iden
        >>> ooh &&& (oih &&& ih) >>> cond ih oh"""
    if not hs or compact(hs[1]) != compact(expected_hs):
        raise ValueError("canonical fe_normalize program differs")
    expected_coq = """((iden &&& (unit >>> Alg.scribe canonical_field_word)
        >>> @subtract_word_spec term 8) &&& iden)
        >>> (O O H &&& (O I H &&& I H)) >>> cond (I H) (O H)"""
    if compact(definition(port, "canonical_fe_normalize")) != compact(expected_coq):
        raise ValueError("Coq fe_normalize literal port differs")
    require(port, "canonical_fe_normalize {term : Alg.Core.Algebra} : term (Word 8) (Word 8)", "Coq word types")
    if compact(definition(port, "canonical_field_word")) != compact("@fromZ (WordToZ 8) canonical_field_order"):
        raise ValueError("Coq canonical field word differs")
    prime = re.search(r"(?m)^fieldOrder\s*=\s*(0x[0-9a-fA-F]+)\s*$", field)
    value = definition(port, "canonical_field_order").strip()
    if not prime or not value.isdecimal() or int(prime[1], 16) != int(value):
        raise ValueError("canonical field order differs")
    # Same quantified frame/memory contract as the core, with the actual
    # secp global environment as the sole difference.
    common = (coq / "C/jet_bitmachine_rep.v").read_text()
    expected_contract = definition(common, "jet_local_spec").replace("eval_funcall ge0", "eval_funcall secp_ge")
    if compact(definition(local, "secp_jet_local_spec")) != compact(expected_contract):
        raise ValueError("secp public frame contract differs")
    statement = re.search(r"Theorem fe_normalize_local_spec\s*:(.*?)\bProof\.", local, re.S)
    expected_statement = """secp_jet_local_spec f_simplicity_fe_normalize (Word 8) (Word 8)
        (@canonical_fe_normalize Alg.CoreFunSem)."""
    if not statement or compact(statement[1]) != compact(expected_statement):
        raise ValueError("fe_normalize final canonical contract differs")
    return 1


if __name__ == "__main__":
    try:
        check()
    except (ValueError, OSError) as error:
        raise SystemExit(str(error))
    print("canonical fe_normalize catalog/literal program/full frame contract match")
