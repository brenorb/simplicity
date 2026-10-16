"""Read-only corruptions of the selected SHA program/contract/startup boundary."""
import importlib.util
from pathlib import Path
import re
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('sha_canonical_source_negative', HERE / 'check-source.py')
g = importlib.util.module_from_spec(sp)
sp.loader.exec_module(g)
repo = Path(sys.argv[1]).resolve()
model = g.load('sha_canonical_negative_fixed_model', HERE / 'source-model.py').MODEL
original = Path.read_text
fixtures = []


def add(path, before, after):
    path = repo / path
    if before not in original(path) or before == after:
        raise AssertionError('inactive SHA source corruption: ' + str(path) + ':' + before)
    fixtures.append((path, before, after))


for path, kind, name, _ in model['declarations']:
    head = re.search(r'\b(?:Definition|Fixpoint|Let|Record|Lemma|Theorem)\s+' + re.escape(name) + r"(?![\w'])", original(repo / path))
    if head is None:
        raise AssertionError('missing SHA record fixture: ' + name)
    add(path, head[0], head[0] + '_UNREVIEWED')
for path, start, _, _ in model['blocks']:
    add(path, start, start + '_UNREVIEWED')
for path, pattern, _ in model['lines']:
    match = re.search(pattern, original(repo / path), re.M)
    if match is None:
        raise AssertionError('missing SHA routing/type fixture: ' + path + ':' + pattern)
    altered = (match[0][:match.start(1)-match.start()] + '_UNREVIEWED ' + match[1]
               if match.lastindex else match[0] + '_UNREVIEWED')
    add(path, match[0], altered)
for path, _ in model['files']:
    add(path, 'module Simplicity.', 'module Unreviewed.')
for path, name, _ in model['c_functions']:
    add(path, 'bool ' + name + '(', 'bool ' + name + '_UNREVIEWED(')

sha = 'Haskell/Core/Simplicity/Programs/Sha256.hs'
port = 'Coq/C/jet_sha_ctx8_spec.v'
endpoint = 'Coq/C/jet_sha_canonical_startup.v'
for path, before, after in [
    (sha, 'rotateW32 (-13)', 'rotateW32 (-12)'),
    (sha, 'shiftW32 (-10)', 'shiftW32 (-9)'),
    (sha, '0x428a2f98', '0x428a2f99'),
    (sha, '0xc67178f2', '0xc67178f3'),
    (sha, 'foldr (\\k rec -> scribe32 k &&& step >>> rec)', 'foldr (\\k rec -> scribe32 k &&& step >>> step >>> rec)'),
    (sha, 'add32 = add word32 >>> ih', 'add32 = add word32 >>> oh'),
    (sha, '(oh &&& ioh >>> rec) &&& iih >>> rec', '(oh &&& iih >>> rec) &&& ioh >>> rec'),
    (sha, 'ctx8Addn (bufferVector b)', 'ctx8Addn vector32'),
    (sha, '(2^55)', '(2^54)'),
    (sha, '(2^63)', '(2^62)'),
    (sha, 'verifyNumCompression >>> zero word64', 'verifyNumCompression >>> one word64'),
    (sha, 'shift_const_by false word64 6', 'shift_const_by false word64 5'),
    (sha, 'shift_const_by false word64 3', 'shift_const_by false word64 2'),
    (sha, 'fromString "TapData"', 'fromString "TapData "'),
    (port, '@ctx8_addn_spec n term)', '@ctx8_addn_spec (S n) term)'),
    (port, 'assertion_cmr_fail0', 'wrong_assertion_cmr'),
    ('Coq/C/jet_sha256_count_assertion.v', '36028797018963968', '36028797018963969'),
    ('Coq/C/jet_sha_finalize_spec.v', '9223372036854775808', '4611686018427387904'),
    ('Coq/C/jet_sha_finalize_spec.v', '@Word.adder 6 term', '@Word.adder 5 term'),
    ('Coq/C/jet_sha_finalize_spec.v', '@ctx8_addn_spec 3 term', '@ctx8_addn_spec 2 term'),
    ('Coq/C/jet_sha_add_buffer_spec.v', '@ctx8_addn_spec (S d\') term', '@ctx8_addn_spec d\' term'),
    ('Coq/C/jet_bitcoin_ctx_hash_spec.v', '@ctx8_addn_spec 5 term', '@ctx8_addn_spec 6 term'),
    ('Coq/C/jet_bitcoin_ctx_hash_spec.v', '@fromZ (WordToZ 3) 1', '@fromZ (WordToZ 3) 0'),
    ('Coq/C/jet_bitcoin_build_tapleaf_spec.v', '(WordToZ 3) 190', '(WordToZ 3) 191'),
    ('Coq/C/jet_bitcoin_build_tapleaf_spec.v', '(WordToZ 7) 784', '(WordToZ 7) 783'),
    ('Coq/C/jet_bitcoin_build_tapbranch_spec.v', '(2 ^ 511 + 1024)', '(2 ^ 511 + 512)'),
    ('Coq/C/jet_bitcoin_build_tapbranch_spec.v', '@lt_word_spec term 8', '@lt_word_spec term 7'),
    ('Haskell/Core/Simplicity/Programs/Bitcoin.hs', 'fromString "TapLeaf"', 'fromString "TapLeaf/elements"'),
    ('Haskell/Core/Simplicity/Programs/Bitcoin.hs', 'fromString "TapBranch"', 'fromString "TapBranch/elements"'),
    ('Haskell/Core/Simplicity/Programs/Bitcoin.hs', 'ctx8Add32) &&& iih >>> ctx8Add4', 'ctx8Add4) &&& iih >>> ctx8Add32'),
    ('Haskell/Core/Simplicity/Digest.hs', '(tagDigest, tagDigest)', '(tagDigest, hash0)'),
    ('Haskell/Core/Simplicity/Ty/Word.hs', 'buffer63 = DoubleB buffer31', 'buffer63 = DoubleB buffer15'),
    ('Haskell/Core/Simplicity/Ty/Word.hs', 'buffer511 = DoubleB buffer255', 'buffer511 = DoubleB buffer127'),
    ('C/jets.c', 'read32s(block, 16, &src);', 'read32s(block, 15, &src);'),
    ('C/jets.c', 'return sha_256_ctx_8_add_n(dst, &src, 512);', 'return sha_256_ctx_8_add_n(dst, &src, 256);'),
    ('C/jets.c', 'simplicity_read_buffer8(buf, &buf_len, &src, 8);', 'simplicity_read_buffer8(buf, &buf_len, &src, 7);'),
    ('C/jets.c', 'static const unsigned char tagName[] = "TapData";', 'static const unsigned char tagName[] = "Tapdata";'),
    ('Coq/C/jet_sha_startup_state.v', 'sha_persistent_global_state m /\\ sha_tags_state m', 'sha_persistent_global_state m \\/ sha_tags_state m'),
    ('Coq/C/jet_sha_startup_globals.v', '~ Mem.perm m (sha_symbol_block _sha256_max_counter)', 'Mem.perm m (sha_symbol_block _sha256_max_counter)'),
    ('Coq/C/jet_sha_block_local.v', '(sha_symbol_block _sha256_compression_portable) Ptrofs.zero', '(sha_symbol_block _simplicity_sha256_compression) Ptrofs.zero'),
]:
    add(path, before, after)

parser = g.load('sha_canonical_negative_parser', repo / 'Coq/check-secp-predicates-specification.py')
for name in ['sha_256_block_canonical_startup_spec', 'sha_256_ctx_8_add_512_canonical_startup_spec',
             'bitcoin_annex_hash_canonical_startup_spec']:
    block = g.extract(parser.read_code(repo / endpoint), 'statement', name).strip()
    replacements = [('sha_startup_', 'wrong_startup_'), ('f_simplicity_', 'f_wrong_'),
                    ('spec :', 'spec : False ->')]
    if 'memcpy_model ->' in block:
        replacements += [('memcpy_model ->', 'False ->'), ('memcpy_model ->', '')]
    for before, after in replacements:
        if before not in block:
            raise AssertionError('inactive complete SHA contract fixture: ' + before)
        add(endpoint, block, block.replace(before, after, 1))
for name in ['sha_startup_total_spec', 'sha_startup_partial_spec']:
    path = 'Coq/C/jet_sha_startup_state.v'
    block = g.extract(parser.read_code(repo / path), 'declaration', name).strip()
    for before, after in [('sha_startup_state m ->', 'False ->'),
                          ('Clight2.eval_funcall sha_ge', 'True /\\ Clight2.eval_funcall wrong_ge'),
                          ('frame_output_cells_at mf', 'wrong_output_cells_at mf'),
                          ('sha_startup_state mf.', 'True.')]:
        if before not in block:
            raise AssertionError('inactive complete startup-state fixture: ' + before)
        add(path, block, block.replace(before, after, 1))

g.check(repo)
for path, before, after in fixtures:
    altered = original(path).replace(before, after, 1)
    def read(self, *args, **kwargs):
        return altered if self == path else original(self, *args, **kwargs)
    with patch.object(Path, 'read_text', read):
        try:
            g.check(repo)
        except ValueError:
            pass
        else:
            raise AssertionError('accepted SHA canonical-source corruption: ' + str(path) + ':' + before)
g.check(repo)
print(str(len(fixtures)) + ' SHA canonical-program/width/order/padding/tag/C/full-contract/startup corruptions rejected')
