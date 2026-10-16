"""Fixed reviewed Elements issuance range-proof hash source model."""
MODEL = {'declarations': [['Coq/C/jet_elements_issuance_proofs_hash_program.v',
                   'statement',
                   'elements_issuance_proofs_bytes_bound',
                   'Lemma elements_issuance_proofs_bytes_bound (x : Ty.tySem Word512) :\n'
                   '  Z.of_nat (List.length (vector_values Word8 6 x)) <= 64.\n'],
                  ['Coq/C/jet_elements_issuance_proofs_hash_program.v',
                   'statement',
                   'elements_issuance_proofs_loop_bound',
                   'Lemma elements_issuance_proofs_loop_bound : 64 * wsize 5 / 64 < ctx8_limit.\n'],
                  ['Coq/C/jet_elements_issuance_proofs_hash_program.v',
                   'declaration',
                   'elements_issuance_proofs_array',
                   'Definition elements_issuance_proofs_array {alg : EFP.Algebra} :\n'
                   '    EFP.domain alg (Ty.Prod Ty.Unit Word32) (Ty.Sum Ty.Unit Word512) :=\n'
                   '  let core := Alg.Assertion.toCore (EFP.CanonicalStructures.toAssertion alg) in\n'
                   '  @AC.comp _ _ _ core\n'
                   '    (@AC.pair _ _ _ core\n'
                   '      (@AC.drop Ty.Unit Word32 _ core (@EFP.Combinators.prim _ _ alg '
                   'Elements.IssuanceAssetProof))\n'
                   '      (@AC.drop Ty.Unit Word32 _ core (@EFP.Combinators.prim _ _ alg '
                   'Elements.IssuanceTokenProof)))\n'
                   '    (@AC.case _ _ _ _ core (@AC.injl _ _ _ core (@AC.unit _ core))\n'
                   '      (@AC.comp _ _ _ core\n'
                   '        (@AC.pair _ _ _ core (AC.drop AC.iden) (AC.take AC.iden))\n'
                   '        (@AC.case _ _ _ _ core (@AC.injl _ _ _ core (@AC.unit _ core))\n'
                   '          (@AC.injr _ _ _ core (@AC.pair _ _ _ core (AC.drop AC.iden) (AC.take '
                   'AC.iden)))))).\n'
                   '\n'
                   ' '],
                  ['Coq/C/jet_elements_issuance_proofs_hash_program.v',
                   'declaration',
                   'elements_issuance_proofs_body',
                   'Definition elements_issuance_proofs_body {alg : EFP.Algebra} :\n'
                   '    EFP.domain alg (Ty.Prod (Ty.Prod Ty.Unit Word32) sha256_ctx8_type)\n'
                   '      (Ty.Sum sha256_ctx8_type sha256_ctx8_type) :=\n'
                   '  let term := EFP.CanonicalStructures.toAssertion alg in\n'
                   '  let core := Alg.Assertion.toCore term in\n'
                   '  @AC.comp _ _ _ core\n'
                   '    (@AC.pair _ _ _ core\n'
                   '      (@AC.take _ _ _ core (@AC.drop Ty.Unit Word32 _ core (@EFP.Combinators.prim _ _ '
                   'alg Elements.IssuanceAssetProof)))\n'
                   '      (@AC.pair _ _ _ core\n'
                   '        (@AC.take _ _ _ core (@AC.drop Ty.Unit Word32 _ core (@EFP.Combinators.prim _ _ '
                   'alg Elements.IssuanceTokenProof)))\n'
                   '        (AC.drop AC.iden)))\n'
                   '    (@AC.case _ _ _ _ core (@AC.injl _ _ _ core (AC.drop (AC.drop AC.iden)))\n'
                   '      (@AC.comp _ _ _ core\n'
                   '        (@AC.pair _ _ _ core (AC.drop (AC.take AC.iden))\n'
                   '          (@AC.pair _ _ _ core (AC.take AC.iden) (AC.drop (AC.drop AC.iden))))\n'
                   '        (@AC.case _ _ _ _ core (@AC.injl _ _ _ core (AC.drop (AC.drop AC.iden)))\n'
                   '          (@AC.injr _ _ _ core (@AC.comp _ _ _ core\n'
                   '            (@AC.pair _ _ _ core (AC.drop (AC.drop AC.iden))\n'
                   '              (@AC.pair _ _ _ core (AC.drop (AC.take AC.iden)) (AC.take AC.iden)))\n'
                   '            (@ctx8_addn_spec 6 term)))))).\n'],
                  ['Coq/C/jet_elements_issuance_proofs_hash_program.v',
                   'statement',
                   'elements_issuance_proofs_array_parametric',
                   'Lemma elements_issuance_proofs_array_parametric : EFP.Parametric '
                   '(@elements_issuance_proofs_array).\n'],
                  ['Coq/C/jet_elements_issuance_proofs_hash_program.v',
                   'statement',
                   'elements_issuance_proofs_body_parametric',
                   'Lemma elements_issuance_proofs_body_parametric : EFP.Parametric '
                   '(@elements_issuance_proofs_body).\n'],
                  ['Coq/C/jet_elements_issuance_proofs_hash_program.v',
                   'declaration',
                   'elements_issuance_asset_proof_bytes',
                   'Definition elements_issuance_asset_proof_bytes (txi : sigTxInput) : list byte :=\n'
                   '  match sigTxiIssuance txi with\n'
                   '  | None => []\n'
                   '  | Some i => viewPrf (match i with\n'
                   '      | inl ni => newIssuanceAmount ni | inr ri => reissuanceAmount ri end)\n'
                   '  end.\n'],
                  ['Coq/C/jet_elements_issuance_proofs_hash_program.v',
                   'declaration',
                   'elements_issuance_token_proof_bytes',
                   'Definition elements_issuance_token_proof_bytes (txi : sigTxInput) : list byte :=\n'
                   '  match sigTxiIssuance txi with\n'
                   '  | None => []\n'
                   '  | Some i => viewPrf (match i with\n'
                   '      | inl ni => newIssuanceTokenAmount ni | inr _ => Explicit Int64.zero end)\n'
                   '  end.\n'],
                  ['Coq/C/jet_elements_issuance_proofs_hash_program.v',
                   'declaration',
                   'elements_issuance_proofs_of',
                   'Definition elements_issuance_proofs_of (e : Elements.env) : list (Ty.tySem Word512) :=\n'
                   '  map (fun txi =>\n'
                   '    (from_hash256 (byteStringHash (elements_issuance_asset_proof_bytes txi)),\n'
                   '     from_hash256 (byteStringHash (elements_issuance_token_proof_bytes txi))))\n'
                   '    (sigTxIn (Elements.envTx e)).\n'],
                  ['Coq/C/jet_elements_issuance_proofs_hash_program.v',
                   'statement',
                   'elements_issuance_proofs_array_sem',
                   'Lemma elements_issuance_proofs_array_sem i e :\n'
                   '  @elements_issuance_proofs_array elements_hash_alg (tt, i) e =\n'
                   '    Some (match nth_error (elements_issuance_proofs_of e) (Z.to_nat (wz 5 i)) with\n'
                   '          Some x => inr x | None => inl tt end).\n'],
                  ['Coq/C/jet_elements_issuance_proofs_hash_program.v',
                   'statement',
                   'elements_issuance_proofs_body_reader_matches',
                   'Lemma elements_issuance_proofs_body_reader_matches i c e :\n'
                   '  @elements_issuance_proofs_body elements_hash_alg ((tt, i), c) e =\n'
                   '    @gen_loop_body Word512 (fun term => @ctx8_addn_spec 6 term)\n'
                   '      (hash_reader_alg Elements.env) Ty.Unit Word32\n'
                   '      (@elements_issuance_proofs_array elements_hash_alg) ((tt, i), c) e.\n'],
                  ['Coq/C/jet_elements_issuance_proofs_hash_program.v',
                   'statement',
                   'elements_issuance_proofs_body_reader_eq',
                   'Lemma elements_issuance_proofs_body_reader_eq :\n'
                   '  @elements_issuance_proofs_body elements_hash_alg =\n'
                   '    @gen_loop_body Word512 (fun term => @ctx8_addn_spec 6 term)\n'
                   '      (hash_reader_alg Elements.env) Ty.Unit Word32 (@elements_issuance_proofs_array '
                   'elements_hash_alg).\n'],
                  ['Coq/C/jet_elements_issuance_proofs_hash_program.v',
                   'declaration',
                   'elements_issuance_range_proofs_hash_spec',
                   'Definition elements_issuance_range_proofs_hash_spec {alg : EFP.Algebra} : EFP.domain alg '
                   'Ty.Unit Word256 :=\n'
                   '  let term := EFP.CanonicalStructures.toAssertion alg in\n'
                   '  let core := Alg.Assertion.toCore term in\n'
                   '  @AC.comp _ _ _ core\n'
                   '    (@AC.pair _ _ _ core (@AC.unit _ core) (@sha256_ctx8_init_spec core))\n'
                   '    (@AC.comp _ _ _ core\n'
                   '      (@for_while_program 5 _ _ _ core (@elements_issuance_proofs_body alg))\n'
                   '      (@AC.copair _ _ _ core (@ctx8_finalize_spec term) (@ctx8_finalize_spec term))).\n'],
                  ['Coq/C/jet_elements_issuance_proofs_hash_program.v',
                   'statement',
                   'elements_issuance_range_proofs_hash_spec_parametric',
                   'Lemma elements_issuance_range_proofs_hash_spec_parametric : EFP.Parametric '
                   '(@elements_issuance_range_proofs_hash_spec).\n'],
                  ['Coq/C/jet_elements_issuance_proofs_hash_program.v',
                   'statement',
                   'elements_issuance_range_proofs_hash_reader_program_matches',
                   'Lemma elements_issuance_range_proofs_hash_reader_program_matches :\n'
                   '  @elements_issuance_range_proofs_hash_spec elements_hash_alg =\n'
                   '    @hash_elems_spec Word512 (fun term => @ctx8_addn_spec 6 term) 5\n'
                   '      (hash_reader_alg Elements.env) (@elements_issuance_proofs_array '
                   'elements_hash_alg).\n'],
                  ['Coq/C/jet_elements_issuance_proofs_hash_program.v',
                   'declaration',
                   'elements_issuance_range_proofs_hash_of',
                   'Definition elements_issuance_range_proofs_hash_of (e : Elements.env) : hash256 :=\n'
                   '  elems_hash_of Word512 (vector_values Word8 6) 5 (elements_issuance_proofs_of e).\n'],
                  ['Coq/C/jet_elements_issuance_proofs_hash_program.v',
                   'statement',
                   'elements_issuance_range_proofs_hash_spec_sem',
                   'Theorem elements_issuance_range_proofs_hash_spec_sem e :\n'
                   '  @elements_issuance_range_proofs_hash_spec elements_hash_alg tt e =\n'
                   '    Some (from_hash256 (elements_issuance_range_proofs_hash_of e)).\n'],
                  ['Coq/C/jet_elements_issuance_proofs_hash_program.v',
                   'statement',
                   'elements_issuance_range_proofs_hash_program_local_spec',
                   'Theorem elements_issuance_range_proofs_hash_program_local_spec :\n'
                   '  application_jet_local_spec_sep f_simplicity_issuance_range_proofs_hash elements_ge '
                   'Elements.env Ty.Unit Word256\n'
                   '    (hash_getter_rep elements_issuance_range_proofs_hash_of 0 536 760)\n'
                   '    (fun a e => @elements_issuance_range_proofs_hash_spec elements_hash_alg a e).\n']],
 'blocks': [['Haskell/Simplicity/Elements/Programs/SigHash.hs',
             '  , issuanceRangeProofsHash =\n',
             '  , issuanceBlindingEntropyHash =\n',
             '     let\n'
             '      finalize = ctx8Finalize\n'
             '      body = take (drop (primitive IssuanceAssetProof)) &&& (take (drop (primitive '
             'IssuanceTokenProof)) &&& ih)\n'
             '         >>> match (injl iih) (ioh &&& (oh &&& iih)\n'
             '         >>> match (injl iih) (injr (iih &&& (ioh &&& oh) >>> ctx8Addn vector64)))\n'
             '     in\n'
             '      unit &&& ctx8Init >>> forWhile word32 body >>> copair finalize finalize\n'
             '\n']]}
