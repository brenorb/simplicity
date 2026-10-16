"""Fixed reviewed Elements tapEnvHash composition/source model."""
MODEL = {'declarations': [['Coq/C/jet_elements_tap_env_hash_program.v',
                   'declaration',
                   'elements_tap_env_hash_spec',
                   'Definition elements_tap_env_hash_spec {alg : EFP.Algebra} : EFP.domain alg Ty.Unit '
                   'Word256 :=\n'
                   '  let term := EFP.CanonicalStructures.toAssertion alg in\n'
                   '  let core := Alg.Assertion.toCore term in\n'
                   '  @AC.comp _ _ _ core\n'
                   '    (@AC.pair _ _ _ core\n'
                   '      (@AC.comp _ _ _ core\n'
                   '        (@AC.pair _ _ _ core (@sha256_ctx8_init_spec core) (@elements_tapleaf_hash_spec '
                   'alg))\n'
                   '        (@ctx8_addn_spec 5 term))\n'
                   '      (@AC.pair _ _ _ core\n'
                   '        (@elements_prim_words_hash_spec 5 3 Elements.Tappath alg)\n'
                   '        (@EFP.Combinators.prim _ _ alg Elements.InternalKey)))\n'
                   '    (@AC.comp _ _ _ core (@ctx8_addn_spec 6 term) (@ctx8_finalize_spec term)).\n'],
                  ['Coq/C/jet_elements_tap_env_hash_program.v',
                   'statement',
                   'elements_tap_env_hash_spec_parametric',
                   'Lemma elements_tap_env_hash_spec_parametric : EFP.Parametric '
                   '(@elements_tap_env_hash_spec).\n'],
                  ['Coq/C/jet_elements_tap_env_hash_program.v',
                   'declaration',
                   'elements_tap_env_hash_of',
                   'Definition elements_tap_env_hash_of (e : Elements.env) : hash256 :=\n'
                   '  sha256_bytes_of\n'
                   '    (vector_values (Word 3) 5 (from_hash256 (elements_tapleaf_hash_of e)) ++\n'
                   '     vector_values (Word 3) 6\n'
                   '       (from_hash256 (elements_words_hash_of 5 3 (elements_tappath_words e)),\n'
                   '        from_hash256 (tapInternalKey (Elements.envTap e)))).\n'],
                  ['Coq/C/jet_elements_tap_env_hash_program.v',
                   'statement',
                   'elements_tap_env_hash_spec_sem',
                   'Theorem elements_tap_env_hash_spec_sem e :\n'
                   '  @elements_tap_env_hash_spec elements_hash_alg tt e =\n'
                   '    Some (from_hash256 (elements_tap_env_hash_of e)).\n'],
                  ['Coq/C/jet_elements_tap_env_hash_program.v',
                   'statement',
                   'elements_tap_env_hash_program_local_spec',
                   'Theorem elements_tap_env_hash_program_local_spec :\n'
                   '  application_jet_local_spec_sep f_simplicity_tap_env_hash elements_ge Elements.env '
                   'Ty.Unit Word256\n'
                   '    (hash_getter_rep elements_tap_env_hash_of 8 72 176)\n'
                   '    (fun a e => @elements_tap_env_hash_spec elements_hash_alg a e).\n'],
                  ['Coq/C/jet_bitcoin_composite_hash.v',
                   'declaration',
                   'sha256_bytes_of',
                   'Definition sha256_bytes_of (bs : list (Ty.tySem (Word 3))) : hash256 :=\n'
                   '  mk_hash256 (sha_stream [] sha256_iv_words 0 bs).\n'
                   '\n'
                   ' '],
                  ['Coq/C/jet_bitcoin_composite_hash.v',
                   'statement',
                   'init_hash_sem',
                   'Lemma init_hash_sem (bs : list (Ty.tySem (Word 3))) :\n'
                   '  Z.of_nat (length bs) / 64 < ctx8_limit ->\n'
                   '  exists cf, ctx8_add_list (@sha256_ctx8_init_spec Alg.CoreFunSem tt) bs = Some cf /\\\n'
                   '    @ctx8_finalize_spec optalg cf = Some (from_hash256 (sha256_bytes_of bs)).\n'],
                  ['Coq/C/jet_bitcoin_composite_hash.v',
                   'statement',
                   'add_app_some',
                   'Lemma add_app_some c (bs1 bs2 : list (Ty.tySem (Word 3))) cf :\n'
                   '  ctx8_add_list c (bs1 ++ bs2) = Some cf ->\n'
                   '  exists c1, ctx8_add_list c bs1 = Some c1 /\\ ctx8_add_list c1 bs2 = Some cf.\n']],
 'blocks': []}
