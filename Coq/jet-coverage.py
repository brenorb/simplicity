#!/usr/bin/env python3
"""Inventory every public C jet, without conflating helper proofs with coverage.

Proof entries are metadata pointing to frozen, audited public theorem types.
This script does not check proofs: run check-jets.sh for that. CSV lists every
declaration, including missing proofs, unregistered jets and legacy names.
"""
import argparse
import csv
import os
import re
import sys
from collections import Counter
from functools import lru_cache
from pathlib import Path

from importlib.util import module_from_spec, spec_from_file_location

sys.dont_write_bytecode = True
COQ = Path(__file__).resolve().parent
# The Nix proof derivations build an isolated Coq source tree. Supply the
# independently filtered, read-only C inventory there; normal checkouts need
# no override. Missing headers are an error, never silently reduced scope.
REPO = Path(os.environ.get("JET_C_REPO", COQ.parent))
HEADERS = {
    "core": "C/jets.h",
    "bitcoin": "C/bitcoin/bitcoinJets.h",
    "elements": "C/elements/elementsJets.h",
}
SPECIFICATIONS = {
    "core": "Haskell/Core/Simplicity/CoreJets.hs",
    "bitcoin": "Haskell/Simplicity/Bitcoin/Jets.hs",
    "elements": "Haskell/Simplicity/Elements/Jets.hs",
}


# Exact reviewed public boundaries outside the default translation unit/contracts.
RECOVERED_CONTRACTS = {'simplicity_asset_amount_hash': 'memcpy_model -> asset_elements_partial_local_spec '
                                 'f_simplicity_asset_amount_hash asset_amount_input_type '
                                 'sha256_ctx8_type (fun a => @elements_asset_amount_hash_spec '
                                 'optalg a).',
 'simplicity_calculate_asset': 'memcpy_model -> calculation_jet_local_spec '
                               'f_simplicity_calculate_asset (@calculate_asset_spec '
                               'Alg.CoreFunSem).',
 'simplicity_calculate_confidential_token': 'memcpy_model -> calculation_jet_local_spec '
                                            'f_simplicity_calculate_confidential_token '
                                            '(@calculate_confidential_token_spec Alg.CoreFunSem).',
 'simplicity_calculate_explicit_token': 'memcpy_model -> calculation_jet_local_spec '
                                        'f_simplicity_calculate_explicit_token '
                                        '(@calculate_explicit_token_spec Alg.CoreFunSem).',
 'simplicity_calculate_issuance_entropy': 'memcpy_model -> elements_entropy_local_spec '
                                          'f_simplicity_calculate_issuance_entropy (fun a => '
                                          '@calculate_issuance_entropy_spec Alg.CoreFunSem a).',
 'simplicity_fe_multiply': 'secp_jet_local_spec f_simplicity_fe_multiply (Ty.Prod (Word 8) (Word '
                           '8)) (Word 8) (@literal_fe_multiply Alg.CoreFunSem).',
 'simplicity_fe_multiply_beta': 'secp_jet_initialized_local_spec beta_initialized '
                                'f_simplicity_fe_multiply_beta (Word 8) (Word 8) '
                                '(@literal_fe_multiply_beta Alg.CoreFunSem).',
 'simplicity_fe_square': 'secp_jet_local_spec f_simplicity_fe_square (Word 8) (Word 8) '
                         '(@literal_fe_square Alg.CoreFunSem).',
 'simplicity_gej_rescale': 'secp_jet_local_spec f_simplicity_gej_rescale '
                            '(Ty.Prod (Ty.Prod (Ty.Prod (Word 8) (Word 8)) (Word 8)) (Word 8)) '
                            '(Ty.Prod (Ty.Prod (Word 8) (Word 8)) (Word 8)) '
                            '(@literal_gej_rescale Alg.CoreFunSem).',
 'simplicity_nonce_hash': 'memcpy_model -> nonce_elements_partial_local_spec '
                          'f_simplicity_nonce_hash nonce_hash_input_type sha256_ctx8_type (fun a '
                          '=> @nonce_hash_spec optalg a).',
 'simplicity_sha_256_block': 'sha_jet_local_spec f_simplicity_sha_256_block '
                               '(Ty.Prod Word256 Word512) Word256 '
                               '(@literal_sha_256_block Alg.CoreFunSem).',
 'simplicity_outpoint_hash': 'memcpy_model -> outpoint_elements_partial_local_spec '
                             'f_simplicity_outpoint_hash op_input_type sha256_ctx8_type (fun a => '
                             '@elements_outpoint_hash_spec optalg a).'}

# Literal context-add specializations; retain the whole assertion contract,
# exact input width, SHA-unit execution and explicit external memcpy premise.
for depth in range(10):
    size = 2 ** depth
    source_type = "(Word 3)" if depth == 0 else f"(Vector (Word 3) {depth})"
    program = "@literal_ctx8_add1 optalg" if depth == 0 else f"@literal_ctx8_addn {depth} optalg"
    RECOVERED_CONTRACTS[f"simplicity_sha_256_ctx_8_add_{size}"] = (
        f"memcpy_model -> sha_jet_partial_local_spec f_simplicity_sha_256_ctx_8_add_{size} "
        f"(Ty.Prod sha256_ctx8_type {source_type}) sha256_ctx8_type ({program}).")

RECOVERED_CONTRACTS.update({
    "simplicity_sha_256_ctx_8_add_buffer_511": (
        "memcpy_model -> sha_jet_partial_local_spec f_simplicity_sha_256_ctx_8_add_buffer_511 "
        "(Ty.Prod sha256_ctx8_type (buffer_type (Word 3) 8)) sha256_ctx8_type "
        "(@literal_ctx8_add_buffer 8 optalg)."),
    "simplicity_sha_256_ctx_8_finalize": (
        "memcpy_model -> sha_jet_partial_local_spec f_simplicity_sha_256_ctx_8_finalize "
        "sha256_ctx8_type (Word 8) (@literal_ctx8_finalize optalg)."),
    "simplicity_tapdata_init": (
        "memcpy_model -> sha_jet_local_spec_pre (fun m => sha_globals_ok m /\\ sha_tag_ok m) "
        "f_simplicity_tapdata_init Ty.Unit sha256_ctx8_type (@literal_tapdata_init Alg.CoreFunSem)."),
    "simplicity_bitcoin_build_tapleaf_simplicity": (
        "memcpy_model -> sha_jet_local_spec_pre sha_tapleaf_pre "
        "f_simplicity_bitcoin_build_tapleaf_simplicity (Word 8) (Word 8) "
        "(@literal_build_tapleaf Alg.CoreFunSem)."),
    "simplicity_bitcoin_build_tapbranch": (
        "memcpy_model -> sha_jet_local_spec_pre sha_tapbranch_pre "
        "f_simplicity_bitcoin_build_tapbranch (Word 9) (Word 8) "
        "(@literal_build_tapbranch Alg.CoreFunSem)."),
    "simplicity_bitcoin_outpoint_hash": (
        "memcpy_model -> sha_jet_partial_local_spec f_simplicity_bitcoin_outpoint_hash "
        "(Ty.Prod sha256_ctx8_type (Ty.Prod (Word 8) (Word 5))) sha256_ctx8_type "
        "(@literal_bitcoin_outpoint_hash optalg)."),
    "simplicity_bitcoin_annex_hash": (
        "memcpy_model -> sha_jet_partial_local_spec f_simplicity_bitcoin_annex_hash "
        "(Ty.Prod sha256_ctx8_type (Ty.Sum Ty.Unit (Word 8))) sha256_ctx8_type "
        "(@literal_bitcoin_annex_hash optalg)."),
    "simplicity_bitcoin_tappath_hash": (
        "application_jet_local_spec_sep f_simplicity_bitcoin_tappath_hash bitcoin_ge ext_environment "
        "Ty.Unit Word256 (hash_getter_rep (fun e => words_hash_of 5 3 (tappath_of e)) 8 40 176) "
        "(fun a environment => @literal_bitcoin_tappath_hash fullalg a environment)."),
})

for stem, depth, offset in [
        ("output_scripts", 5, 48), ("input_scripts", 5, 176),
        ("input_sequences", 2, 240), ("input_script_sigs", 5, 304)]:
    RECOVERED_CONTRACTS[f"simplicity_bitcoin_{stem}_hash"] = (
        f"application_jet_local_spec_sep f_simplicity_bitcoin_{stem}_hash bitcoin_ge ext_environment "
        f"Ty.Unit Word256 (hash_getter_rep (fun e => words_hash_of {depth} 5 ({stem}_of e)) 0 {offset} 432) "
        f"(fun a environment => @literal_bitcoin_{stem}_hash fullalg a environment).")


def records(path, fields):
    result = []
    for number, line in enumerate(path.read_text().splitlines(), 1):
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        row = line.split()
        if len(row) != fields:
            raise ValueError(f"{path}:{number}: expected {fields} fields")
        result.append(row)
    return result


def declarations(source):
    source = re.sub(r"/\*.*?\*/|//[^\n]*", "", source, flags=re.S)
    decls = re.findall(r"\bbool\s+(simplicity_\w+)\s*\(([^;{}]*)\)\s*;", source)
    names = []
    for name, args in decls:
        args = re.sub(r"\s+", "", args)
        if args != "frameItem*dst,frameItemsrc,consttxEnv*env":
            raise ValueError(f"unexpected public jet signature for {name}: {args}")
        names.append(name)
    return names


def top_level_connectives(statement):
    depth = 0
    arrows = []
    for token in re.finditer(r"<->|->|/\\|\\/|[(){}\[\]]", statement):
        if token[0] in "({[":
            depth += 1
        elif token[0] in ")}]":
            depth -= 1
        elif depth == 0:
            arrows.append(token.start())
    if depth != 0:
        raise ValueError("unbalanced public theorem statement")
    return arrows


@lru_cache(maxsize=256)
def checked_source_code(source):
    # Cache by exact source contents: changed fixtures always get parsed again.
    scanner_spec = spec_from_file_location("jet_scanner", Path(__file__).resolve().parent / "scan-jet-proofs.py")
    scanner = module_from_spec(scanner_spec)
    scanner_spec.loader.exec_module(scanner)
    return scanner.code_only(source)


def inventory():
    jets = {}
    for family, header in HEADERS.items():
        for name in declarations((REPO / header).read_text()):
            if name in jets:
                raise ValueError(f"duplicate public jet: {name}")
            jets[name] = {"family": family, "function": name, "header": header,
                          "specification_catalog": SPECIFICATIONS[family],
                          "registrations": [], "proof": "", "condition": ""}
    for application in ("bitcoin", "elements"):
        registry = REPO / f"C/{application}/primitiveJetNode.inc"
        source = registry.read_text()
        nodes = re.findall(r"\[(\w+)\]\s*=\s*\{(.*?)\n\}", source, re.S)
        parsed_functions = []
        for identifier, body in nodes:
            match = re.search(r"\.jet\s*=\s*(simplicity_\w+)", body)
            if not match:
                raise ValueError(f"unparsed jet node: {registry}:{identifier}")
            name = match[1]
            if name not in jets:
                raise ValueError(f"registered jet lacks public declaration: {name}")
            jets[name]["registrations"].append(f"{application}:{identifier}")
            parsed_functions.append(name)
        if Counter(parsed_functions) != Counter(re.findall(r"\.jet\s*=\s*(simplicity_\w+)", source)):
            raise ValueError(f"registry parser missed entries: {registry}")
    audited = {tuple(row) for row in records(COQ / "C/jet_public_theorems.txt", 2)}
    for name, module, theorem in records(COQ / "C/jet_coverage.tsv", 3):
        if name not in jets:
            raise ValueError(f"proof entry for unknown jet: {name}")
        if jets[name]["proof"]:
            raise ValueError(f"duplicate coverage entry: {name}")
        if (module, theorem) not in audited:
            raise ValueError(f"coverage theorem not publicly audited: {module}.{theorem}")
        code = checked_source_code((COQ / (module.replace(".", "/") + ".v")).read_text())
        statement = re.search(rf"\b(?:Theorem|Lemma|Corollary)\s+{re.escape(theorem)}\s*:(.*?)\bProof\.", code, re.S)
        if name in RECOVERED_CONTRACTS:
            body = statement[1].strip() if statement else ""
            compact = lambda text: re.sub(r"\s+", "", text)
            if compact(body) != compact(RECOVERED_CONTRACTS[name]):
                raise ValueError(f"coverage entry is not a direct canonical jet theorem: {module}.{theorem}")
            jets[name]["proof"] = f"{module}.{theorem}"
            jets[name]["condition"] = "memcpy_model" if body.startswith("memcpy_model") else ""
            continue
        # Application functions execute in their own linked global environment,
        # not the core ge0. Counting a core contract for them would lose the
        # physical/logical primitive-environment correspondence.
        family = jets[name]["family"]
        if family == "core":
            # Copy-family contracts retain an explicit library model;
            # record these separately from direct execution proofs.
            contract = (rf"\b(?:jet_local_spec|jet_partial_local_spec)\s+f_{re.escape(name)}\b|"
                        rf"\bmemcpy_model\s*->\s*jet_separated_local_spec\s+f_{re.escape(name)}\b")
            if name in {"simplicity_fe_normalize", "simplicity_fe_is_odd", "simplicity_fe_is_zero", "simplicity_fe_negate", "simplicity_fe_add", "simplicity_gej_infinity", "simplicity_gej_is_infinity", "simplicity_gej_negate", "simplicity_ge_negate", "simplicity_scalar_is_zero", "simplicity_scalar_normalize", "simplicity_scalar_negate", "simplicity_scalar_add", "simplicity_scalar_multiply", "simplicity_scalar_square"}:
                # This reviewed whole-function contract executes in the
                # original secp translation unit. Its full frame contract and
                # literal canonical specialization have their own source gate.
                contract = rf"\bsecp_jet_local_spec\s+f_{re.escape(name)}\b"
            elif name == "simplicity_scalar_multiply_lambda":
                # Named initialized-global contract; never arbitrary Ready.
                contract = (r"\bsecp_jet_initialized_local_spec\s+scalar_lambda_initialized\s+"
                            r"f_simplicity_scalar_multiply_lambda\s+\(Word\s+8\)\s+\(Word\s+8\)\s+"
                            r"\(@canonical_scalar_multiply_lambda\s+Alg\.CoreFunSem\)\s*\.$")
        elif family == "bitcoin":
            contract = (rf"\b(?:application_jet_local_spec|application_jet_partial_spec)\s+f_{re.escape(name)}\s+"
                        r"bitcoin_ge\s+Bitcoin\.env\b|"
                        rf"\bapplication_jet_local_spec_sep\s+f_{re.escape(name)}\s+"
                        r"bitcoin_ge\s+(?:Bitcoin\.env|raw_bitcoin_environment)\b")
        else:
            # Only these fifty-eight selected correspondences have a reviewed
            # literal target, environment relation and whole-C-contract gate.
            if name in {"simplicity_input_script_hash", "simplicity_input_script_sig_hash", "simplicity_issuance_asset_proof", "simplicity_issuance_token_proof"}:
                contract = (rf"\bapplication_jet_local_spec_sep\s+f_{re.escape(name)}\s+"
                            r"elements_ge\s+Elements\.env\s+Word32\s+\(Ty\.Sum\s+Ty\.Unit\s+Word256\)")
            elif name in {"simplicity_current_script_hash", "simplicity_current_script_sig_hash", "simplicity_current_issuance_asset_proof", "simplicity_current_issuance_token_proof"}:
                contract = (rf"\bapplication_jet_local_spec_sep\s+f_{re.escape(name)}\s+"
                            r"elements_ge\s+Elements\.env\s+Ty\.Unit\s+Word256\b")
            elif name in {"simplicity_input_annex_hash", "simplicity_reissuance_blinding", "simplicity_new_issuance_contract", "simplicity_reissuance_entropy"}:
                contract = (rf"\bapplication_jet_local_spec_sep\s+f_{re.escape(name)}\s+"
                            r"elements_ge\s+Elements\.env\s+Word32\s+\(Ty\.Sum\s+Ty\.Unit\s+\(Ty\.Sum\s+Ty\.Unit\s+Word256\)\)")
            elif name in {"simplicity_current_annex_hash", "simplicity_current_reissuance_blinding", "simplicity_current_new_issuance_contract", "simplicity_current_reissuance_entropy"}:
                contract = (rf"\bapplication_jet_local_spec_sep\s+f_{re.escape(name)}\s+"
                            r"elements_ge\s+Elements\.env\s+Ty\.Unit\s+\(Ty\.Sum\s+Ty\.Unit\s+Word256\)")
            elif name == "simplicity_input_prev_outpoint":
                contract = (rf"\bapplication_jet_local_spec_sep\s+f_{re.escape(name)}\s+"
                            r"elements_ge\s+Elements\.env\s+Word32\s+\(Ty\.Sum\s+Ty\.Unit\s+\(Ty\.Prod\s+Word256\s+Word32\)\)")
            elif name == "simplicity_current_prev_outpoint":
                contract = (rf"\bapplication_jet_local_spec_sep\s+f_{re.escape(name)}\s+"
                            r"elements_ge\s+Elements\.env\s+Ty\.Unit\s+\(Ty\.Prod\s+Word256\s+Word32\)")
            elif name in {"simplicity_output_script_hash", "simplicity_output_surjection_proof", "simplicity_output_range_proof"}:
                contract = (rf"\bapplication_jet_local_spec_sep\s+f_{re.escape(name)}\s+"
                            r"elements_ge\s+Elements\.env\s+Word32\s+\(Ty\.Sum\s+Ty\.Unit\s+Word256\)")
            elif name == "simplicity_internal_key":
                contract = (rf"\bapplication_jet_local_spec_sep\s+f_{re.escape(name)}\s+"
                            r"elements_ge\s+Elements\.env\s+Ty\.Unit\s+Word256\b")
            elif name == "simplicity_tappath":
                contract = (rf"\bapplication_jet_local_spec_sep\s+f_{re.escape(name)}\s+"
                            r"elements_ge\s+Elements\.env\s+Word8\s+\(Ty\.Sum\s+Ty\.Unit\s+Word256\)")
            elif name == "simplicity_lbtc_asset":
                contract = (rf"\bapplication_jet_local_spec_sep\s+f_{re.escape(name)}\s+"
                            r"elements_ge\s+Elements\.env\s+Ty\.Unit\s+Word256\b")
            elif name in {"simplicity_broken_do_not_use_tx_lock_distance", "simplicity_broken_do_not_use_tx_lock_duration"}:
                contract = (rf"\bapplication_jet_local_spec_sep\s+f_{re.escape(name)}\s+"
                            r"elements_ge\s+Elements\.env\s+Ty\.Unit\s+Word16\b")
            elif name in {"simplicity_broken_do_not_use_check_lock_distance", "simplicity_broken_do_not_use_check_lock_duration"}:
                contract = (rf"\bapplication_jet_partial_spec\s+f_{re.escape(name)}\s+"
                            r"elements_ge\s+Elements\.env\s+Word16\s+Ty\.Unit\b")
            elif name == "simplicity_output_nonce":
                contract = (rf"\bapplication_jet_local_spec_sep\s+f_{re.escape(name)}\s+"
                            r"elements_ge\s+Elements\.env\s+Word32\s+"
                            r"\(Ty\.Sum\s+Ty\.Unit\s+\(Ty\.Sum\s+Ty\.Unit\s+ConfNonce\)\)")
            elif name in {"simplicity_input_asset", "simplicity_output_asset"}:
                contract = (rf"\bapplication_jet_local_spec_sep\s+f_{re.escape(name)}\s+"
                            r"elements_ge\s+Elements\.env\s+Word32\s+\(Ty\.Sum\s+Ty\.Unit\s+AssetConf\)")
            elif name == "simplicity_current_asset":
                contract = (rf"\bapplication_jet_local_spec_sep\s+f_{re.escape(name)}\s+"
                            r"elements_ge\s+Elements\.env\s+Ty\.Unit\s+AssetConf\b")
            elif name in {"simplicity_input_amount", "simplicity_output_amount"}:
                contract = (rf"\bapplication_jet_local_spec_sep\s+f_{re.escape(name)}\s+"
                            r"elements_ge\s+Elements\.env\s+Word32\s+\(Ty\.Sum\s+Ty\.Unit\s+AmountPair\)")
            elif name == "simplicity_current_amount":
                contract = (rf"\bapplication_jet_local_spec_sep\s+f_{re.escape(name)}\s+"
                            r"elements_ge\s+Elements\.env\s+Ty\.Unit\s+AmountPair\b")
            elif name == "simplicity_issuance_asset_amount":
                contract = (rf"\bapplication_jet_local_spec_sep\s+f_{re.escape(name)}\s+"
                            r"elements_ge\s+Elements\.env\s+Word32\s+\(Ty\.Sum\s+Ty\.Unit\s+\(Ty\.Sum\s+Ty\.Unit\s+ConfAmount\)\)")
            elif name == "simplicity_current_issuance_asset_amount":
                contract = (rf"\bapplication_jet_local_spec_sep\s+f_{re.escape(name)}\s+"
                            r"elements_ge\s+Elements\.env\s+Ty\.Unit\s+\(Ty\.Sum\s+Ty\.Unit\s+ConfAmount\)")
            elif name == "simplicity_issuance_token_amount":
                contract = (rf"\bapplication_jet_local_spec_sep\s+f_{re.escape(name)}\s+"
                            r"elements_ge\s+Elements\.env\s+Word32\s+\(Ty\.Sum\s+Ty\.Unit\s+\(Ty\.Sum\s+Ty\.Unit\s+ConfAmount\)\)")
            elif name == "simplicity_current_issuance_token_amount":
                contract = (rf"\bapplication_jet_local_spec_sep\s+f_{re.escape(name)}\s+"
                            r"elements_ge\s+Elements\.env\s+Ty\.Unit\s+\(Ty\.Sum\s+Ty\.Unit\s+ConfAmount\)")
            elif name == "simplicity_output_null_datum":
                # Explicit contextual family: separated represented BM frames,
                # not the unrestricted application_jet_local_spec_sep API.
                contract = (rf"\bapplication_jet_bitmachine_spec\s+f_{re.escape(name)}\s+"
                            r"elements_ge\s+Elements\.env\s+\(Ty\.Prod\s+Word32\s+Word32\)\s+"
                            r"ResultTy\s+elements_null_data_environment_rep\s+"
                            r"elements_output_null_datum_literal_spec\s*\.$")
            elif name == "simplicity_transaction_id":
                contract = (rf"\bapplication_jet_local_spec_sep\s+f_{re.escape(name)}\s+"
                            r"elements_ge\s+Elements\.env\s+Ty\.Unit\s+Word256\b")
            elif name == "simplicity_tx_is_final":
                contract = (rf"\bapplication_jet_local_spec_sep\s+f_{re.escape(name)}\s+"
                            r"elements_ge\s+Elements\.env\s+Ty\.Unit\s+Bit\b")
            elif name in {"simplicity_tx_lock_height", "simplicity_tx_lock_time"}:
                contract = (rf"\bapplication_jet_local_spec_sep\s+f_{re.escape(name)}\s+"
                            r"elements_ge\s+Elements\.env\s+Ty\.Unit\s+Word32\b")
            elif name in {"simplicity_check_lock_height", "simplicity_check_lock_time"}:
                contract = (rf"\bapplication_jet_partial_spec\s+f_{re.escape(name)}\s+"
                            r"elements_ge\s+Elements\.env\s+\(Word\s+5\)\s+Ty\.Unit\b")
            elif name == "simplicity_input_pegin":
                contract = (rf"\bapplication_jet_local_spec_sep\s+f_{re.escape(name)}\s+"
                            r"elements_ge\s+Elements\.env\s+Word32\s+"
                            r"\(Ty\.Sum\s+Ty\.Unit\s+\(Ty\.Sum\s+Ty\.Unit\s+Word256\)\)")
            elif name == "simplicity_current_pegin":
                contract = (rf"\bapplication_jet_local_spec_sep\s+f_{re.escape(name)}\s+"
                            r"elements_ge\s+Elements\.env\s+Ty\.Unit\s+\(Ty\.Sum\s+Ty\.Unit\s+Word256\)")
            elif name in {"simplicity_tapleaf_version", "simplicity_script_cmr", "simplicity_genesis_block_hash"}:
                output = "Word8" if name == "simplicity_tapleaf_version" else "Word256"
                contract = (rf"\bapplication_jet_local_spec_sep\s+f_{re.escape(name)}\s+"
                            rf"elements_ge\s+Elements\.env\s+Ty\.Unit\s+{output}\b")
            elif name == "simplicity_input_sequence":
                contract = (rf"\bapplication_jet_local_spec_sep\s+f_{re.escape(name)}\s+"
                            r"elements_ge\s+Elements\.env\s+Word32\s+"
                            r"\(Ty\.Sum\s+Ty\.Unit\s+Word32\)")
            else:
                contract = (rf"\bapplication_jet_local_spec\s+f_{re.escape(name)}\s+"
                            r"elements_ge\s+Elements\.env\s+Ty\.Unit\s+Word32\b"
                            if name in {"simplicity_version", "simplicity_lock_time", "simplicity_current_index", "simplicity_num_inputs", "simplicity_num_outputs", "simplicity_current_sequence"} else r"(?!)")
        body = statement[1].strip() if statement else ""
        conditional = body.startswith("memcpy_model")
        arrows = top_level_connectives(body)
        # A direct contract must be the entire proposition. Searching anywhere
        # in a type accidentally accepts False -> contract and contract -> True.
        expected_arrows = 1 if family == "core" and conditional else 0
        if (not statement or not re.match(contract, body)
                or len(arrows) != expected_arrows):
            raise ValueError(f"coverage entry is not a direct canonical jet theorem: {module}.{theorem}")
        jets[name]["proof"] = f"{module}.{theorem}"
        jets[name]["condition"] = "memcpy_model" if conditional else ""
    return list(jets.values())


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--csv", action="store_true", help="list every jet, including all missing proofs")
    parser.add_argument("--require-complete", action="store_true",
                        help="fail if any declared jet lacks a registered final equivalence contract")
    args = parser.parse_args()
    try:
        jets = inventory()
    except (ValueError, OSError) as error:
        sys.exit(str(error))
    if args.csv:
        writer = csv.DictWriter(sys.stdout, fieldnames=list(jets[0]))
        writer.writeheader()
        for row in jets:
            writer.writerow({**row, "registrations": ";".join(row["registrations"])})
    else:
        for family in HEADERS:
            rows = [row for row in jets if row["family"] == family]
            direct = sum(bool(row["proof"]) and not row["condition"] for row in rows)
            conditional = sum(bool(row["condition"]) for row in rows)
            print(f"{family}: {direct} proof entries without an extra library premise; "
                  f"{conditional} conditional; {len(rows)} declared")
        missing = sum(not row["proof"] for row in jets)
        conditional = sum(bool(row["condition"]) for row in jets)
        unregistered = sum(not row["registrations"] for row in jets)
        print(f"total: {len(jets) - missing}/{len(jets)}; remaining: {missing}; unregistered declarations: {unregistered}")
        print(f"Of these entries: {len(jets) - missing - conditional} without an extra library premise, "
              f"{conditional} conditional on memcpy_model (libc implementation not proved).")
        print("Scope: public jet declarations in all three C headers. Proof validity requires check-jets.sh.")
    if args.require_complete and any(not row["proof"] for row in jets):
        sys.exit("Every-jet goal is incomplete: declared C jets lack registered final equivalence proofs.")


if __name__ == "__main__":
    main()
