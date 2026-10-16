"""Fixed reviewed literal Elements pegin/outpoint program/source model."""
MODEL = {'declarations': [['Coq/C/jet_elements_outpoints_hash_program.v',
                   'declaration',
                   'elements_outpoint_type',
                   'Definition elements_outpoint_type : Ty :=\n'
                   '  Ty.Prod (Ty.Sum Ty.Unit Word256) (Ty.Prod Word256 Word32).\n'],
                  ['Coq/C/jet_elements_outpoints_hash_program.v',
                   'declaration',
                   'elements_outpoint_add_spec',
                   'Definition elements_outpoint_add_spec {term : Alg.Assertion.Algebra} :\n'
                   '    term (Ty.Prod sha256_ctx8_type elements_outpoint_type) sha256_ctx8_type :=\n'
                   '  let core := Alg.Assertion.toCore term in\n'
                   '  let c := @AC.take sha256_ctx8_type elements_outpoint_type _ core (@AC.iden _ core) in\n'
                   '  let pg := @AC.drop sha256_ctx8_type elements_outpoint_type _ core\n'
                   '    (@AC.take (Ty.Sum Ty.Unit Word256) (Ty.Prod Word256 Word32) _ core (@AC.iden _ '
                   'core)) in\n'
                   '  let h := @AC.drop sha256_ctx8_type elements_outpoint_type _ core\n'
                   '    (@AC.drop (Ty.Sum Ty.Unit Word256) (Ty.Prod Word256 Word32) _ core\n'
                   '      (@AC.take Word256 Word32 _ core (@AC.iden _ core))) in\n'
                   '  let ix := @AC.drop sha256_ctx8_type elements_outpoint_type _ core\n'
                   '    (@AC.drop (Ty.Sum Ty.Unit Word256) (Ty.Prod Word256 Word32) _ core\n'
                   '      (@AC.drop Word256 Word32 _ core (@AC.iden _ core))) in\n'
                   '  @AC.comp _ _ _ core\n'
                   '    (@AC.pair _ _ _ core\n'
                   '      (@AC.comp _ _ _ core\n'
                   '        (@AC.pair _ _ _ core (@AC.comp _ _ _ core (@AC.pair _ _ _ core c pg) '
                   '(@annex_hash_spec term)) h)\n'
                   '        (@ctx8_addn_spec 5 term)) ix)\n'
                   '    (@ctx8_addn_spec 2 term).\n'],
                  ['Coq/C/jet_elements_outpoints_hash_program.v',
                   'statement',
                   'elements_outpoint_add_spec_parametric',
                   'Lemma elements_outpoint_add_spec_parametric : Alg.Assertion.Parametric '
                   '(@elements_outpoint_add_spec).\n'],
                  ['Coq/C/jet_elements_outpoints_hash_program.v',
                   'declaration',
                   'elements_outpoint_bytes',
                   'Definition elements_outpoint_bytes (x : Ty.tySem elements_outpoint_type) : list '
                   '(Ty.tySem Word8) :=\n'
                   '  annex_elem_bytes (fst x) ++ vector_values Word8 5 (fst (snd x)) ++ vector_values Word8 '
                   '2 (snd (snd x)).\n'],
                  ['Coq/C/jet_elements_outpoints_hash_program.v',
                   'statement',
                   'elements_outpoint_add_option',
                   'Lemma elements_outpoint_add_option c x :\n'
                   '  @elements_outpoint_add_spec optalg (c, x) = ctx8_add_list c (elements_outpoint_bytes '
                   'x).\n'],
                  ['Coq/C/jet_elements_outpoints_hash_program.v',
                   'statement',
                   'elements_outpoint_bytes_bound',
                   'Lemma elements_outpoint_bytes_bound x : Z.of_nat (List.length (elements_outpoint_bytes '
                   'x)) <= 69.\n'],
                  ['Coq/C/jet_elements_outpoints_hash_program.v',
                   'statement',
                   'elements_outpoint_loop_bound',
                   'Lemma elements_outpoint_loop_bound : 69 * wsize 5 / 64 < ctx8_limit.\n'],
                  ['Coq/C/jet_elements_outpoints_hash_program.v',
                   'declaration',
                   'elements_outpoints_array',
                   'Definition elements_outpoints_array {alg : EFP.Algebra} :\n'
                   '    EFP.domain alg (Ty.Prod Ty.Unit Word32) (Ty.Sum Ty.Unit elements_outpoint_type) :=\n'
                   '  let core := Alg.Assertion.toCore (EFP.CanonicalStructures.toAssertion alg) in\n'
                   '  @AC.comp _ _ _ core\n'
                   '    (@AC.pair _ _ _ core\n'
                   '      (@AC.drop Ty.Unit Word32 _ core (@EFP.Combinators.prim _ _ alg '
                   'Elements.InputPegin))\n'
                   '      (@AC.drop Ty.Unit Word32 _ core (@EFP.Combinators.prim _ _ alg '
                   'Elements.InputPrevOutpoint)))\n'
                   '    (@AC.case _ _ _ _ core (@AC.injl _ _ _ core (@AC.unit _ core))\n'
                   '      (@AC.comp _ _ _ core\n'
                   '        (@AC.pair _ _ _ core (AC.drop AC.iden) (AC.take AC.iden))\n'
                   '        (@AC.case _ _ _ _ core (@AC.injl _ _ _ core (@AC.unit _ core))\n'
                   '          (@AC.injr _ _ _ core (@AC.pair _ _ _ core (AC.drop AC.iden) (AC.take '
                   'AC.iden)))))).\n'
                   '\n'
                   ' '],
                  ['Coq/C/jet_elements_outpoints_hash_program.v',
                   'declaration',
                   'elements_outpoints_body',
                   'Definition elements_outpoints_body {alg : EFP.Algebra} :\n'
                   '    EFP.domain alg (Ty.Prod (Ty.Prod Ty.Unit Word32) sha256_ctx8_type)\n'
                   '      (Ty.Sum sha256_ctx8_type sha256_ctx8_type) :=\n'
                   '  let term := EFP.CanonicalStructures.toAssertion alg in\n'
                   '  let core := Alg.Assertion.toCore term in\n'
                   '  @AC.comp _ _ _ core\n'
                   '    (@AC.pair _ _ _ core\n'
                   '      (@AC.take _ _ _ core (@AC.drop Ty.Unit Word32 _ core (@EFP.Combinators.prim _ _ '
                   'alg Elements.InputPegin)))\n'
                   '      (@AC.pair _ _ _ core\n'
                   '        (@AC.take _ _ _ core (@AC.drop Ty.Unit Word32 _ core (@EFP.Combinators.prim _ _ '
                   'alg Elements.InputPrevOutpoint)))\n'
                   '        (AC.drop AC.iden)))\n'
                   '    (@AC.case _ _ _ _ core (@AC.injl _ _ _ core (AC.drop (AC.drop AC.iden)))\n'
                   '      (@AC.comp _ _ _ core\n'
                   '        (@AC.pair _ _ _ core (AC.drop (AC.take AC.iden))\n'
                   '          (@AC.pair _ _ _ core (AC.take AC.iden) (AC.drop (AC.drop AC.iden))))\n'
                   '        (@AC.case _ _ _ _ core (@AC.injl _ _ _ core (AC.drop (AC.drop AC.iden)))\n'
                   '          (@AC.injr _ _ _ core (@AC.comp _ _ _ core\n'
                   '            (@AC.pair _ _ _ core (AC.drop (AC.drop AC.iden))\n'
                   '              (@AC.pair _ _ _ core (AC.drop (AC.take AC.iden)) (AC.take AC.iden)))\n'
                   '            (@elements_outpoint_add_spec term)))))).\n'],
                  ['Coq/C/jet_elements_outpoints_hash_program.v',
                   'statement',
                   'elements_outpoints_array_parametric',
                   'Lemma elements_outpoints_array_parametric : EFP.Parametric '
                   '(@elements_outpoints_array).\n'],
                  ['Coq/C/jet_elements_outpoints_hash_program.v',
                   'statement',
                   'elements_outpoints_body_parametric',
                   'Lemma elements_outpoints_body_parametric : EFP.Parametric (@elements_outpoints_body).\n'],
                  ['Coq/C/jet_elements_outpoints_hash_program.v',
                   'declaration',
                   'elements_outpoints_of',
                   'Definition elements_outpoints_of (e : Elements.env) : list (Ty.tySem '
                   'elements_outpoint_type) :=\n'
                   '  map (fun txi =>\n'
                   '    (match sigTxiPegin txi with None => inl tt | Some h => inr (from_hash256 h) end,\n'
                   '     (from_hash256 (opHash (sigTxiPreviousOutpoint txi)),\n'
                   '      @fromZ (WordToZ 5) (Int.unsigned (opIndex (sigTxiPreviousOutpoint txi))))))\n'
                   '    (sigTxIn (Elements.envTx e)).\n'],
                  ['Coq/C/jet_elements_outpoints_hash_program.v',
                   'statement',
                   'elements_outpoints_array_sem',
                   'Lemma elements_outpoints_array_sem i e :\n'
                   '  @elements_outpoints_array elements_hash_alg (tt, i) e =\n'
                   '    Some (match nth_error (elements_outpoints_of e) (Z.to_nat (wz 5 i)) with\n'
                   '          Some x => inr x | None => inl tt end).\n'],
                  ['Coq/C/jet_elements_outpoints_hash_program.v',
                   'statement',
                   'elements_outpoints_body_reader_matches',
                   'Lemma elements_outpoints_body_reader_matches i c e :\n'
                   '  @elements_outpoints_body elements_hash_alg ((tt, i), c) e =\n'
                   '    @gen_loop_body elements_outpoint_type (fun term => @elements_outpoint_add_spec '
                   'term)\n'
                   '      (hash_reader_alg Elements.env) Ty.Unit Word32\n'
                   '      (@elements_outpoints_array elements_hash_alg) ((tt, i), c) e.\n'],
                  ['Coq/C/jet_elements_outpoints_hash_program.v',
                   'statement',
                   'elements_outpoints_body_reader_eq',
                   'Lemma elements_outpoints_body_reader_eq :\n'
                   '  @elements_outpoints_body elements_hash_alg =\n'
                   '    @gen_loop_body elements_outpoint_type (fun term => @elements_outpoint_add_spec '
                   'term)\n'
                   '      (hash_reader_alg Elements.env) Ty.Unit Word32 (@elements_outpoints_array '
                   'elements_hash_alg).\n'],
                  ['Coq/C/jet_elements_outpoints_hash_program.v',
                   'declaration',
                   'elements_input_outpoints_hash_spec',
                   'Definition elements_input_outpoints_hash_spec {alg : EFP.Algebra} : EFP.domain alg '
                   'Ty.Unit Word256 :=\n'
                   '  let term := EFP.CanonicalStructures.toAssertion alg in\n'
                   '  let core := Alg.Assertion.toCore term in\n'
                   '  @AC.comp _ _ _ core\n'
                   '    (@AC.pair _ _ _ core (@AC.unit _ core) (@sha256_ctx8_init_spec core))\n'
                   '    (@AC.comp _ _ _ core\n'
                   '      (@for_while_program 5 _ _ _ core (@elements_outpoints_body alg))\n'
                   '      (@AC.copair _ _ _ core (@ctx8_finalize_spec term) (@ctx8_finalize_spec term))).\n'],
                  ['Coq/C/jet_elements_outpoints_hash_program.v',
                   'statement',
                   'elements_input_outpoints_hash_spec_parametric',
                   'Lemma elements_input_outpoints_hash_spec_parametric : EFP.Parametric '
                   '(@elements_input_outpoints_hash_spec).\n'],
                  ['Coq/C/jet_elements_outpoints_hash_program.v',
                   'statement',
                   'elements_input_outpoints_hash_reader_program_matches',
                   'Lemma elements_input_outpoints_hash_reader_program_matches :\n'
                   '  @elements_input_outpoints_hash_spec elements_hash_alg =\n'
                   '    @hash_elems_spec elements_outpoint_type (fun term => @elements_outpoint_add_spec '
                   'term) 5\n'
                   '      (hash_reader_alg Elements.env) (@elements_outpoints_array elements_hash_alg).\n'],
                  ['Coq/C/jet_elements_outpoints_hash_program.v',
                   'declaration',
                   'elements_input_outpoints_hash_of',
                   'Definition elements_input_outpoints_hash_of (e : Elements.env) : hash256 :=\n'
                   '  elems_hash_of elements_outpoint_type elements_outpoint_bytes 5 (elements_outpoints_of '
                   'e).\n'],
                  ['Coq/C/jet_elements_outpoints_hash_program.v',
                   'statement',
                   'elements_input_outpoints_hash_spec_sem',
                   'Theorem elements_input_outpoints_hash_spec_sem e :\n'
                   '  @elements_input_outpoints_hash_spec elements_hash_alg tt e =\n'
                   '    Some (from_hash256 (elements_input_outpoints_hash_of e)).\n'],
                  ['Coq/C/jet_elements_outpoints_hash_program.v',
                   'statement',
                   'elements_input_outpoints_hash_program_local_spec',
                   'Theorem elements_input_outpoints_hash_program_local_spec :\n'
                   '  application_jet_local_spec_sep f_simplicity_input_outpoints_hash elements_ge '
                   'Elements.env Ty.Unit Word256\n'
                   '    (hash_getter_rep elements_input_outpoints_hash_of 0 216 760)\n'
                   '    (fun a e => @elements_input_outpoints_hash_spec elements_hash_alg a e).\n']],
 'blocks': [['Haskell/Core/Simplicity/Programs/Elements.hs',
             'outpointHash = ((oh &&& ioh >>> annexHash)',
             ', assetAmountHash = (oh &&& ioh >>> assetHash)',
             ' &&& iioh >>> ctx8Add32) &&& iiih >>> ctx8Add4\n  ']]}
