"""One-time capture of the manually reviewed source boundary, not acceptance.

Refuses to overwrite a model. Do not use model regeneration to accommodate
changed canonical sources. The actual comparison and negative suites are
separate, and kernel/host-library/normal-admission claims remain separate.
"""
from pathlib import Path
import importlib.util
import pprint
import re
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('sha_fixed_model_capture', HERE / 'check-source.py')
g = importlib.util.module_from_spec(sp)
sp.loader.exec_module(g)
s = g.load('sha_fixed_model_patcher', HERE.parent / 'elements-count/support.py')


def main(work):
    if (HERE / 'source-model.py').exists():
        raise ValueError('fixed model exists; inspect/review it instead of regenerating')
    parser = g.load('sha_fixed_model_parser', work / 'Coq/check-secp-predicates-specification.py')
    model = dict(declarations=[], blocks=[], lines=[], files=[], c_functions=[])
    chosen = {
        'Coq/Simplicity/SHA256.v': ['scribe32', 'add32', 'xor3Word32', 'chWord32', 'majWord32', 'shift32', 'rotate32', 'hashBlock'],
        'Coq/Simplicity/Word.v': ['zero', 'adderBit', 'fullAdderBit', 'buildFullAdder', 'fullAdder', 'adder', 'bitwiseTri', 'shift_const_by', 'shift_const', 'left_rotate1', 'right_rotate1', 'rotate_const_list', 'foldr_comp', 'rotate_const'],
        'Coq/Simplicity/Bit.v': ['false', 'true', 'cond', 'ch', 'not', 'xor3', 'maj'],
        'Coq/C/jet_buffer_empty_spec.v': ['buffer_type', 'buffer_empty_spec'],
        'Coq/C/jet_sha256_ctx8_init_spec.v': ['sha256_ctx8_type', 'sha256_ctx8_init_spec'],
        'Coq/C/jet_sha256_iv_init.v': ['sha256_iv_constants', 'sha256_iv_words', 'sha256_iv_spec'],
        'Coq/C/jet_sha_ctx8_spec.v': ['buffer_snoc_spec', 'ctx8_buf', 'ctx8_tail', 'ctx8_add1_snoc', 'ctx8_add1_full', 'ctx8_add1_spec', 'ctx8_limit', 'ctx8_addn_spec'],
        'Coq/C/jet_sha_add_buffer_spec.v': ['ctx8_add_buffer_spec'],
        'Coq/C/jet_sha_finalize_spec.v': ['buffer_pad_spec', 'flag_spec', 'buffer63_size_spec', 'ctx8_bitlen_spec', 'pad_word64', 'ctx8_clear_count_spec', 'ctx8_finalize_pad_spec', 'ctx8_finalize_block_spec', 'ctx8_finalize_spec'],
        'Coq/C/jet_sha256_count_assertion.v': ['sha256_count_limit', 'sha256_count_check_spec', 'sha256_count_assertion_spec'],
        'Coq/C/jet_assertion_spec.v': ['assertion_hash0', 'assertion_cmr_fail0'],
        'Coq/C/jet_increment_spec.v': ['full_increment_word_spec', 'increment_word_spec'],
        'Coq/C/jet_bitcoin_ctx_hash_spec.v': ['outpoint_hash_spec', 'byte_one', 'annex_hash_spec'],
        'Coq/C/jet_sha_tapdata_spec.v': ['tapdata_prefix', 'one64_spec', 'tapdata_init_spec', 'iv_word', 'tag_word', 'tag_block', 'tag_bytes'],
        'Coq/C/jet_bitcoin_tapleaf_hash_spec.v': ['tapleaf_prefix', 'tapleaf_tag_word', 'tapleaf_tag_block', 'tapleaf_tag_bytes', 'byte32'],
        'Coq/C/jet_bitcoin_build_tapleaf_spec.v': ['tl_version', 'tl_w8000', 'tl_len', 'build_tapleaf_block', 'build_tapleaf_spec'],
        'Coq/C/jet_bitcoin_build_tapbranch_spec.v': ['tapbranch_prefix', 'tapbranch_tag_word', 'tapbranch_tag_block', 'tapbranch_tag_bytes', 'tb_padblock', 'build_tapbranch_spec'],
        'Coq/C/jet_sha_linkage.v': ['sha_ge'],
        'Coq/C/jet_sha_startup_state.v': ['sha_tag_extents', 'sha_tags_state', 'sha_startup_state', 'sha_startup_total_spec', 'sha_startup_partial_spec'],
        'Coq/C/jet_sha_startup_globals.v': ['sha_persistent_global_state'],
        'Coq/C/jet_sha_add_n_exec.v': ['sha_globals_ok'],
        'Coq/C/jet_sha_block_local.v': ['sha_dispatch_ok'],
        'Coq/C/jet_sha_tapdata_jet.v': ['sha_tag_ok'],
        'Coq/C/jet_bitcoin_make_tapleaf_exec.v': ['sha_tapleaf_tag_ok'],
        'Coq/C/jet_bitcoin_make_tapbranch_exec.v': ['sha_tapbranch_tag_ok'],
        'Coq/C/jet_sha_uchars_exec.v': ['sha_max_counter'],
        'Coq/C/jet_memcpy_model.v': ['memcpy_model'],
        'Coq/C/jet_order_spec.v': ['lt_word_spec'],
        'Coq/C/jet_core_pad_spec.v': ['left_pad_low_spec'],
    }
    for path, names in chosen.items():
        code = parser.read_code(work / path)
        for name in names:
            model['declarations'].append([path, 'declaration', name, g.extract(code, 'declaration', name)])
    statements = {
        'Coq/C/jet_sha_tapdata_spec.v': ['tag_hash_eval', 'tapdata_prefix_eval', 'tag_block_bytes', 'iv_word_regs'],
        'Coq/C/jet_bitcoin_tapleaf_hash_spec.v': ['tapleaf_tag_hash_eval', 'tapleaf_prefix_eval', 'tapleaf_tag_block_bytes'],
        'Coq/C/jet_bitcoin_build_tapbranch_spec.v': ['tapbranch_tag_hash_eval', 'tapbranch_prefix_eval', 'tapbranch_tag_block_bytes', 'tb_padblock_words'],
    }
    endpoint = 'Coq/C/jet_sha_canonical_startup.v'
    statements[endpoint] = re.findall(r'\bTheorem\s+(\w+)\s*:', parser.read_code(work / endpoint))
    if len(statements[endpoint]) != 19:
        raise ValueError('wrong whole-C/nonvacuity theorem inventory')
    for path, names in statements.items():
        code = parser.read_code(work / path)
        for name in names:
            model['declarations'].append([path, 'statement', name, g.extract(code, 'statement', name)])
    blocks = [
        ('Haskell/Core/Simplicity/Programs/Sha256.hs', 'lib = l\n', 'hashLoop ::'),
        ('Haskell/Core/Simplicity/Programs/Sha256.hs', 'mkLibAssert Lib{..}  = l\n', 'libAssert ::'),
        ('Haskell/Core/Simplicity/Programs/Bitcoin.hs', 'mkLib Sha256.Lib{..} = lib\n', 'lib ::'),
        ('Haskell/Core/Simplicity/Programs/Bitcoin.hs', 'mkLibAssert Sha256.Lib{..} Sha256.LibAssert{..} LibSecp256k1.Lib{..} = libAssert\n', 'libAssert ::'),
        ('Haskell/Core/Simplicity/Programs/Word.hs', 'bufferEmpty ::', 'forWhile ::'),
        ('Haskell/Core/Simplicity/Programs/Word.hs', 'rotate_const ::', 'left_rotate ::'),
        ('Haskell/Core/Simplicity/Programs/Arith.hs', '\nfull_add ::', '\nadd ::'),
        ('Haskell/Core/Simplicity/Programs/Arith.hs', '\nadd ::', '\nfull_increment ::'),
        ('Haskell/Core/Simplicity/Programs/Arith.hs', '\nfull_increment ::', '\nfull_subtract ::'),
        ('Haskell/Core/Simplicity/Programs/Bit.hs', '\ncond ::', '\nnot ::'),
        ('Haskell/Core/Simplicity/Programs/Bit.hs', '\nxor_xor ::', '\nmaj ::'),
        ('Haskell/Core/Simplicity/Digest.hs', 'tagIv ::', 'freeStart ::'),
        ('Haskell/Core/Simplicity/Digest.hs', 'bslHash ::', 'bslDoubleHash ::'),
        ('Haskell/Core/Simplicity/Ty/Word.hs', 'type Buffer1 x =', 'buffer1 ::'),
        ('Haskell/Core/Simplicity/Ty/Word.hs', 'buffer1 ::', 'bufferVector  ::'),
    ]
    for path, start, stop in blocks:
        code = parser.read_code(work / path)
        if code.count(start) != 1 or code.count(stop) != 1:
            raise ValueError('missing/ambiguous fixed block: ' + repr((path, start, stop)))
        model['blocks'].append([path, start, stop, code.split(start, 1)[1].split(stop, 1)[0]])

    def line(path, name, expected, kind='binding'):
        pattern = r'^\s*' + re.escape(name) + (r'\s*=([^\n]*)$' if kind == 'binding' else r'\s*::([^\n]*)$')
        found = re.findall(pattern, parser.read_code(work / path), re.M)
        if len(found) != 1 or g.compact(found[0]) != g.compact(expected):
            raise ValueError('fixed routing/type differs: ' + repr((path, name, found)))
        model['lines'].append([path, pattern, expected])

    core, bitcoin = 'Haskell/Core/Simplicity/CoreJets.hs', 'Haskell/Simplicity/Bitcoin/Jets.hs'
    line(core, 'specificationHash Sha256Block', 'Sha256.hashBlock')
    line(core, 'Sha256Block', 'HashJet (Sha256.Hash, Sha256.Block) Sha256.Hash', 'type')
    for power in range(10):
        n = 2**power
        name = 'Sha256Ctx8Add' + str(n)
        line(core, 'specificationHash ' + name, 'Sha256.ctx8Add1' if n == 1 else 'Sha256.ctx8Addn vector' + str(n))
        line(core, name, 'HashJet (Sha256.Ctx8, Word' + str(n*8) + ') Sha256.Ctx8', 'type')
    for constructor, spec, ty in [
        ('Sha256Ctx8AddBuffer511', 'Sha256.ctx8AddBuffer buffer511', 'HashJet (Sha256.Ctx8, Buffer511 Word8) Sha256.Ctx8'),
        ('Sha256Ctx8Finalize', 'Sha256.ctx8Finalize', 'HashJet Sha256.Ctx8 Sha256.Hash'),
    ]:
        line(core, 'specificationHash ' + constructor, spec)
        line(core, constructor, ty, 'type')
    line(core, 'specificationBitcoin TapdataInit', 'Sha256.tapdataInit')
    line(core, 'TapdataInit', 'BitcoinJet () Sha256.Ctx8', 'type')
    for constructor, selector, a, b in [
        ('AnnexHash', 'annexHash', '(Ctx8, S Word256)', 'Ctx8'),
        ('OutpointHash', 'outpointHash', '(Ctx8, (Word256, Word32))', 'Ctx8'),
        ('BuildTapleafSimplicity', 'buildTapleafSimplicity', 'Word256', 'Word256'),
        ('BuildTapbranch', 'buildTapbranch', '(Word256, Word256)', 'Word256'),
    ]:
        line(bitcoin, 'specificationSigHash ' + constructor, 'Prog.' + selector)
        line(bitcoin, constructor, 'SigHashJet ' + a + ' ' + b, 'type')
    for path, name, expected in [
        ('Haskell/Core/Simplicity/Programs/Sha256.hs', 'libAssert', 'mkLibAssert lib'),
        ('Haskell/Core/Simplicity/Programs/Bitcoin.hs', 'lib', 'mkLib Sha256.lib'),
        ('Haskell/Core/Simplicity/Programs/Bitcoin.hs', 'libAssert', 'mkLibAssert Sha256.lib Sha256.libAssert LibSecp256k1.lib'),
        ('Haskell/Core/Simplicity/Programs/Arith.hs', 'zero', 'low'),
        ('Haskell/Core/Simplicity/Programs/Arith.hs', 'one w', 'true >>> left_pad_low word1 w'),
        ('Haskell/Core/Simplicity/Programs/Word.hs', 'bitwise_maj', 'bitwise_tri maj'),
        ('Haskell/Core/Simplicity/Programs/Word.hs', 'bitwise_ch', 'bitwise_tri ch'),
        ('Haskell/Core/Simplicity/Programs/Word.hs', 'bitwise_xor_xor', 'bitwise_tri xor_xor'),
    ]:
        line(path, name, expected)
    for n in [1, 2, 4, 8, 16, 32, 64, 128, 256, 512]:
        line('Haskell/Core/Simplicity/Ty/Word.hs', 'vector' + str(n), 'SingleV' if n == 1 else 'DoubleV vector' + str(n//2))
    for n in [1, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096]:
        line('Haskell/Core/Simplicity/Ty/Word.hs', 'word' + str(n), 'vector' + str(n))
    for name, expected in [('Block', 'Word512'), ('Hash', 'Word256'), ('Ctx8', '(Buffer63 Word8, (Word64, Word256))')]:
        model['lines'].append(['Haskell/Core/Simplicity/Programs/Sha256.hs', r'^type ' + name + r'\s*=([^\n]*)$', expected])
    for path in ['Haskell/Core/Simplicity/Programs/Sha256/Lib.hs', 'Haskell/Core/Simplicity/Programs/Bitcoin/Lib.hs']:
        model['files'].append([path, parser.read_code(work / path)])
    core_names = ['simplicity_sha_256_block'] + ['simplicity_sha_256_ctx_8_add_' + str(2**n) for n in range(10)]
    core_names += ['simplicity_sha_256_ctx_8_add_buffer_511', 'simplicity_sha_256_ctx_8_finalize', 'simplicity_tapdata_init', 'sha_256_ctx_8_add_n']
    for path, names in [
        ('C/jets.c', core_names),
        ('C/bitcoin/bitcoinJets.c', ['simplicity_bitcoin_annex_hash', 'simplicity_bitcoin_outpoint_hash', 'simplicity_bitcoin_build_tapleaf_simplicity', 'simplicity_bitcoin_build_tapbranch']),
    ]:
        code = re.sub(r'/\*.*?\*/|//[^\n]*', ' ', (work / path).read_text(), flags=re.S)
        for name in names:
            model['c_functions'].append([path, name, g.c_function(code, name)])
    if len(model['c_functions']) != 19:
        raise ValueError('wrong selected C endpoint/helper inventory')
    s.changed({HERE / 'source-model.py': '"""Fixed reviewed SHA compression/context/Bitcoin/startup source boundary.\n\nDo not regenerate from changed candidates to make a failing gate pass.\nSee README.md for the correspondence and host-library limits.\n"""\nMODEL = ' + pprint.pformat(model, width=110, sort_dicts=False) + '\n'})
    print({n: len(v) for n, v in model.items()})
    print({n: v for n, v in g.check(work).items() if n != 'source_sha256'})


if __name__ == '__main__':
    if len(sys.argv) != 2:
        raise ValueError('usage: create-model.py COMPLETED_SHA_TREE')
    main(Path(sys.argv[1]).resolve())
