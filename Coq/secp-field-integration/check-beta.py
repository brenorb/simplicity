import os
import importlib.util
from pathlib import Path
import re
COQ = Path(__file__).resolve().parents[1]
REPO = Path(os.environ.get("JET_C_REPO", COQ.parent))
spec = importlib.util.spec_from_file_location("scanner", COQ / "scan-jet-proofs.py")
scanner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(scanner)
def contract_source(code):
    code = scanner.code_only(code)
    header = code.split('Theorem fe_multiply_beta_initialized_local_spec', 1)
    if len(header) != 2:
        raise ValueError('missing beta public theorem')
    actual = header[1].split('Proof.', 1)[0]
    expected = ': secp_jet_initialized_local_spec beta_initialized f_simplicity_fe_multiply_beta '
    expected += '(Word 8) (Word 8) (@literal_fe_multiply_beta Alg.CoreFunSem).'
    if re.sub(r'\s+', '', actual) != re.sub(r'\s+', '', expected):
        raise ValueError('beta public contract was narrowed or retargeted')
source = (COQ / "C/jet_secp_beta_local.v").read_text()
contract_source(source)
fixtures = [source.replace("(Word 8) (Word 8)", "(Word 7) (Word 8)", 1),
 source.replace("(Word 8) (Word 8)", "(Word 8) (Word 7)", 1),
 source.replace("f_simplicity_fe_multiply_beta (Word", "f_secp256k1_fe_mul (Word", 1),
 source.replace("local_spec beta_initialized", "local_spec (fun _ => True)", 1),
 source.replace("@literal_fe_multiply_beta", "@canonical_fe_normalize", 1),
 source.replace("  secp_jet_initialized_local_spec beta_initialized", "  False -> secp_jet_initialized_local_spec beta_initialized", 1)]
for fixture in fixtures:
 assert fixture != source
 try: contract_source(fixture)
 except ValueError: continue
 raise ValueError("beta contract mutation accepted")
program = (REPO / "Haskell/Core/Simplicity/Programs/LibSecp256k1.hs").read_text()
assert "fe_multiply_beta = (unit >>> fe_beta) &&& iden >>> fe_multiply" in program
beta = re.findall(r"^beta = (0x[0-9a-f]+)$", (REPO / "Haskell/Core/Simplicity/LibSecp256k1/Spec.hs").read_text(), re.M)
value = re.findall(r"Definition beta_value\s*:\s*Z\s*:=\s*(\d+)\s*\.", (COQ / "C/jet_secp_beta_global.v").read_text())
assert len(beta) == 1 and value == [str(int(beta[0],16))]
print("beta canonical constant/wiring and full initialized contract match; six mutations rejected")

port = scanner.code_only((COQ / "C/jet_secp_beta_spec.v").read_text())
for declaration in [
 "Definition beta_word : Ty.tySem (Word 8) := @fromZ (WordToZ 8) beta_value.",
 "Definition literal_fe_beta {term : Alg.Core.Algebra} : term Ty.Unit (Word 8) := Alg.scribe beta_word.",
 "Definition literal_fe_multiply_beta {term : Alg.Core.Algebra} : term (Word 8) (Word 8) := (unit >>> @literal_fe_beta term) &&& iden >>> @literal_fe_multiply term."]:
 assert re.sub(r"\s+", "", declaration) in re.sub(r"\s+", "", port)
