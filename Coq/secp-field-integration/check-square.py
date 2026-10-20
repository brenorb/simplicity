import os
import importlib.util
from pathlib import Path
import re
from types import SimpleNamespace
COQ = Path(__file__).resolve().parents[1]
REPO = Path(os.environ.get("JET_C_REPO", COQ.parent))
spec = importlib.util.spec_from_file_location("scanner", COQ / "scan-jet-proofs.py")
scanner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(scanner)
s = SimpleNamespace(scanner=scanner)
def review_source(texts):
    compact = lambda txt: re.sub(r'\s+', '', s.scanner.code_only(txt))
    checks = {
        'Local': ['Theorem fe_square_local_spec : secp_jet_local_spec f_simplicity_fe_square '
            '(Word 8) (Word 8) (@literal_fe_square Alg.CoreFunSem).'],
        'Rest': ['Definition square_inplace_stmt := match fn_body f_simplicity_fe_square with '
            '| Ssequence _ (Ssequence _ (Ssequence squaring _)) => squaring | _ => Sskip end.',
            'Definition square_rest := match fn_body f_simplicity_fe_square with '
            '| Ssequence _ rest => rest | _ => Sskip end.',
            'Genv.find_symbol secp_ge _secp256k1_fe_sqr = Some (secp_symbol_block _secp256k1_fe_sqr)',
            'Genv.find_funct secp_ge (Vptr (secp_symbol_block _secp256k1_fe_sqr) Ptrofs.zero) '
            '= Some (Internal f_secp256k1_fe_sqr).',
            'Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_sqr) '
            '[Vptr ba Ptrofs.zero;Vptr ba Ptrofs.zero] E0 mf Vundef ->'],
        'Public': ['function_entry2 secp_ge f_simplicity_fe_square '
            '[Vptr bd (Ptrofs.repr dbase);Vptr bs (Ptrofs.repr sbase);v_env] m',
            'Clight2.eval_funcall secp_ge m0 (Internal f_simplicity_fe_square)'],
        'Chain': ['Clight2.eval_funcall secp_ge mr (Internal f_secp256k1_fe_sqr) '
            '[Vptr ba Ptrofs.zero;Vptr ba Ptrofs.zero] E0 mn Vundef'],
    }
    for name, fragments in checks.items():
        code = compact(texts[name])
        for fragment in fragments:
            if code.count(compact(fragment)) != 1:
                raise ValueError('square public target/contract/call differs: ' + name)
    if any(re.search(r'\b(?:beta_initialized|memcpy_model|memcmp_model)\b', s.scanner.code_only(t)) for t in texts.values()):
        raise ValueError('unexpected extra readiness/library premise')

def source_tests(texts):
    mutations = [
        ('Local', 'secp_jet_local_spec', 'secp_jet_initialized_local_spec'),
        ('Local', 'f_simplicity_fe_square', 'f_simplicity_fe_normalize'),
        ('Local', '(Word 8) (Word 8)', '(Word 7) (Word 8)'),
        ('Local', '(Word 8) (Word 8)', '(Word 8) (Word 7)'),
        ('Local', '@literal_fe_square', '@canonical_fe_normalize'),
        ('Rest', 'fn_body f_simplicity_fe_square', 'fn_body f_simplicity_fe_multiply_beta'),
        ('Rest', 'Internal f_secp256k1_fe_sqr', 'Internal f_secp256k1_fe_mul'),
        ('Rest', '[Vptr ba Ptrofs.zero;Vptr ba Ptrofs.zero] E0 mf', '[Vptr ba Ptrofs.zero] E0 mf'),
        ('Public', 'function_entry2 secp_ge f_simplicity_fe_square', 'function_entry2 secp_ge f_simplicity_fe_normalize'),
        ('Public', 'Internal f_simplicity_fe_square', 'Internal f_simplicity_fe_multiply'),
        ('Chain', 'Internal f_secp256k1_fe_sqr', 'Internal f_secp256k1_fe_mul'),
        ('Chain', '[] m ->', '[] m -> beta_initialized m ->'),
    ]
    for name, old, new in mutations:
        if old not in texts[name]:
            raise ValueError('missing square public mutation fixture: ' + old)
        changed = dict(texts)
        changed[name] = texts[name].replace(old, new, 1)
        try:
            review_source(changed)
        except ValueError:
            continue
        raise ValueError('square public source mutation escaped: ' + old)
    return len(mutations)

paths = {'Local': 'Coq/C/jet_secp_square_local.v', 'Rest': 'Coq/C/jet_secp_square_rest.v', 'Public': 'Coq/C/jet_secp_square_public.v', 'Chain': 'Coq/C/jet_secp_square_chain.v'}
texts = {name: (COQ / Path(path).relative_to("Coq")).read_text() for name, path in paths.items()}
review_source(texts)
print("square source contract checks passed; mutations rejected:", source_tests(texts))

# The public lifecycle is tied to the literal canonical square program.
catalog = (REPO / "Haskell/Core/Simplicity/CoreJets.hs").read_text()
program = (REPO / "Haskell/Core/Simplicity/Programs/LibSecp256k1.hs").read_text()
assert "FeSquare :: Secp256k1Jet Secp256k1.FE Secp256k1.FE" in catalog
assert "specificationSecp256k1 FeSquare = Secp256k1.fe_square" in catalog
assert "fe_square = iden &&& iden >>> fe_multiply" in program
port = scanner.code_only((COQ / "C/jet_secp_square_execution.v").read_text())
literal = re.search(r"Definition literal_fe_square\b.*?:=(.*?)\.\s*\n", port, re.S)
assert literal and re.sub(r"\s+", "", literal[1]) == "iden&&&iden>>>@literal_fe_multiplyterm"
