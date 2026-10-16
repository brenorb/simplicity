"""Fixed reviewed amount serializers, primitive pairing and complete C contracts.

Created once after reviewing canonical tags/routing and the packed-field interface.
No verifier regenerates this model from the candidate being checked.
"""
MODEL = {'declarations': [['Coq/C/jet_elements_asset_amount_hash_spec.v',
                   'declaration',
                   'elements_hash_conf_type',
                   'Definition elements_hash_conf_type (X : Ty) : Ty := Ty.Sum (Ty.Prod Bit Word256) '
                   'X.'],
                  ['Coq/C/jet_elements_asset_amount_hash_spec.v',
                   'declaration',
                   'elements_asset_hash_type',
                   'Definition elements_asset_hash_type : Ty := elements_hash_conf_type Word256.'],
                  ['Coq/C/jet_elements_asset_amount_hash_spec.v',
                   'declaration',
                   'elements_amount_hash_type',
                   'Definition elements_amount_hash_type : Ty := elements_hash_conf_type Word64.'],
                  ['Coq/C/jet_elements_asset_amount_hash_spec.v',
                   'declaration',
                   'elements_asset_amount_type',
                   'Definition elements_asset_amount_type : Ty := Ty.Prod elements_asset_hash_type '
                   'elements_amount_hash_type.'],
                  ['Coq/C/jet_elements_asset_amount_hash_spec.v',
                   'declaration',
                   'asset_byte_even',
                   'Definition asset_byte_even : Ty.tySem Word8 := @fromZ (WordToZ 3) 10.'],
                  ['Coq/C/jet_elements_asset_amount_hash_spec.v',
                   'declaration',
                   'asset_byte_odd',
                   'Definition asset_byte_odd : Ty.tySem Word8 := @fromZ (WordToZ 3) 11.'],
                  ['Coq/C/jet_elements_asset_amount_hash_spec.v',
                   'declaration',
                   'amount_byte_even',
                   'Definition amount_byte_even : Ty.tySem Word8 := @fromZ (WordToZ 3) 8.'],
                  ['Coq/C/jet_elements_asset_amount_hash_spec.v',
                   'declaration',
                   'amount_byte_odd',
                   'Definition amount_byte_odd : Ty.tySem Word8 := @fromZ (WordToZ 3) 9.\n'],
                  ['Coq/C/jet_elements_asset_amount_hash_spec.v',
                   'declaration',
                   'conf_tag_byte_spec',
                   'Definition conf_tag_byte_spec (prefix_even prefix_odd : Ty.tySem Word8)\n'
                   '    {term : Alg.Core.Algebra} : term Bit Word8 :=\n'
                   '  AC.copair (Alg.scribe prefix_even) (Alg.scribe prefix_odd).\n'],
                  ['Coq/C/jet_elements_asset_amount_hash_spec.v',
                   'statement',
                   'conf_tag_byte_spec_parametric',
                   'Lemma conf_tag_byte_spec_parametric prefix_even prefix_odd :\n'
                   '  Alg.Core.Parametric (@conf_tag_byte_spec prefix_even prefix_odd).\n'],
                  ['Coq/C/jet_elements_asset_amount_hash_spec.v',
                   'statement',
                   'conf_tag_byte_value',
                   'Lemma conf_tag_byte_value prefix_even prefix_odd b :\n'
                   '  @conf_tag_byte_spec prefix_even prefix_odd Alg.CoreFunSem b =\n'
                   '    match b with inl _ => prefix_even | inr _ => prefix_odd end.\n'],
                  ['Coq/C/jet_elements_asset_amount_hash_spec.v',
                   'statement',
                   'conf_tag_byte_option',
                   'Lemma conf_tag_byte_option prefix_even prefix_odd b :\n'
                   '  @conf_tag_byte_spec prefix_even prefix_odd (Alg.Assertion.toCore optalg) b =\n'
                   '    Some (match b with inl _ => prefix_even | inr _ => prefix_odd end).\n'],
                  ['Coq/C/jet_elements_asset_amount_hash_spec.v',
                   'declaration',
                   'asset_tag_payload_spec',
                   'Definition asset_tag_payload_spec {term : Alg.Core.Algebra} :\n'
                   '    term elements_asset_hash_type (Ty.Prod Word8 Word256) :=\n'
                   '  AC.copair\n'
                   '    (AC.pair (AC.take (@conf_tag_byte_spec asset_byte_even asset_byte_odd term)) '
                   '(AC.drop AC.iden))\n'
                   '    (AC.pair (AC.comp AC.unit (Alg.scribe byte_one)) AC.iden).\n'],
                  ['Coq/C/jet_elements_asset_amount_hash_spec.v',
                   'statement',
                   'asset_tag_payload_spec_parametric',
                   'Lemma asset_tag_payload_spec_parametric : Alg.Core.Parametric '
                   '(@asset_tag_payload_spec).\n'],
                  ['Coq/C/jet_elements_asset_amount_hash_spec.v',
                   'statement',
                   'asset_tag_payload_value',
                   'Lemma asset_tag_payload_value (v : Ty.tySem elements_asset_hash_type) :\n'
                   '  @asset_tag_payload_spec Alg.CoreFunSem v =\n'
                   '  match v with\n'
                   '  | inl (b, h) => (match b with inl _ => asset_byte_even | inr _ => asset_byte_odd '
                   'end, h)\n'
                   '  | inr h => (byte_one, h)\n'
                   '  end.\n'],
                  ['Coq/C/jet_elements_asset_amount_hash_spec.v',
                   'declaration',
                   'elements_asset_hash_spec',
                   'Definition elements_asset_hash_spec {term : Alg.Assertion.Algebra} :\n'
                   '    term (Ty.Prod sha256_ctx8_type elements_asset_hash_type) sha256_ctx8_type :=\n'
                   '  let core := Alg.Assertion.toCore term in\n'
                   '  @AC.comp _ _ _ core (AC.pair (AC.take AC.iden) (AC.drop (@asset_tag_payload_spec '
                   'core)))\n'
                   '    (@ctx8_tagged_word_spec 5 term).\n'],
                  ['Coq/C/jet_elements_asset_amount_hash_spec.v',
                   'statement',
                   'elements_asset_hash_spec_parametric',
                   'Lemma elements_asset_hash_spec_parametric : Alg.Assertion.Parametric '
                   '(@elements_asset_hash_spec).\n'],
                  ['Coq/C/jet_elements_asset_amount_hash_spec.v',
                   'declaration',
                   'elements_asset_bytes',
                   'Definition elements_asset_bytes (v : Ty.tySem elements_asset_hash_type) : list '
                   '(Ty.tySem Word8) :=\n'
                   '  match v with\n'
                   '  | inl (b, h) => (match b with inl _ => asset_byte_even | inr _ => asset_byte_odd '
                   'end) :: vector_values Word8 5 h\n'
                   '  | inr h => byte_one :: vector_values Word8 5 h\n'
                   '  end.\n'],
                  ['Coq/C/jet_elements_asset_amount_hash_spec.v',
                   'statement',
                   'elements_asset_hash_option',
                   'Lemma elements_asset_hash_option c v :\n'
                   '  @elements_asset_hash_spec optalg (c, v) = ctx8_add_list c (elements_asset_bytes '
                   'v).\n'],
                  ['Coq/C/jet_elements_asset_amount_hash_spec.v',
                   'declaration',
                   'elements_amount_hash_spec',
                   'Definition elements_amount_hash_spec {term : Alg.Assertion.Algebra} :\n'
                   '    term (Ty.Prod sha256_ctx8_type elements_amount_hash_type) sha256_ctx8_type :=\n'
                   '  let core := Alg.Assertion.toCore term in\n'
                   '  @AC.comp _ _ _ core (AC.pair (AC.drop AC.iden) (AC.take AC.iden))\n'
                   '    (@AC.case _ _ _ _ core\n'
                   '      (@AC.comp _ _ _ core\n'
                   '        (AC.pair\n'
                   '          (@AC.comp _ _ _ core\n'
                   '            (AC.pair (AC.drop AC.iden)\n'
                   '              (AC.take (AC.take (@conf_tag_byte_spec amount_byte_even '
                   'amount_byte_odd core))))\n'
                   '            (@ctx8_add1_spec term))\n'
                   '          (AC.take (AC.drop AC.iden)))\n'
                   '        (@ctx8_addn_spec 5 term))\n'
                   '      (@AC.comp _ _ _ core\n'
                   '        (AC.pair\n'
                   '          (@AC.comp _ _ _ core\n'
                   '            (AC.pair (AC.drop AC.iden) (AC.comp AC.unit (Alg.scribe byte_one)))\n'
                   '            (@ctx8_add1_spec term))\n'
                   '          (AC.take AC.iden))\n'
                   '        (@ctx8_addn_spec 3 term))).\n'],
                  ['Coq/C/jet_elements_asset_amount_hash_spec.v',
                   'statement',
                   'elements_amount_hash_spec_parametric',
                   'Lemma elements_amount_hash_spec_parametric : Alg.Assertion.Parametric '
                   '(@elements_amount_hash_spec).\n'],
                  ['Coq/C/jet_elements_asset_amount_hash_spec.v',
                   'declaration',
                   'elements_amount_bytes',
                   'Definition elements_amount_bytes (v : Ty.tySem elements_amount_hash_type) : list '
                   '(Ty.tySem Word8) :=\n'
                   '  match v with\n'
                   '  | inl (b, h) => (match b with inl _ => amount_byte_even | inr _ => '
                   'amount_byte_odd end) :: vector_values Word8 5 h\n'
                   '  | inr v => byte_one :: vector_values Word8 3 v\n'
                   '  end.\n'],
                  ['Coq/C/jet_elements_asset_amount_hash_spec.v',
                   'statement',
                   'elements_amount_hash_option',
                   'Lemma elements_amount_hash_option c v :\n'
                   '  @elements_amount_hash_spec optalg (c, v) = ctx8_add_list c (elements_amount_bytes '
                   'v).\n'],
                  ['Coq/C/jet_elements_asset_amount_hash_spec.v',
                   'declaration',
                   'elements_asset_amount_hash_spec',
                   'Definition elements_asset_amount_hash_spec {term : Alg.Assertion.Algebra} :\n'
                   '    term (Ty.Prod sha256_ctx8_type elements_asset_amount_type) sha256_ctx8_type :=\n'
                   '  let core := Alg.Assertion.toCore term in\n'
                   '  @AC.comp _ _ _ core\n'
                   '    (AC.pair\n'
                   '      (@AC.comp _ _ _ core (AC.pair (AC.take AC.iden) (AC.drop (AC.take AC.iden)))\n'
                   '        (@elements_asset_hash_spec term))\n'
                   '      (AC.drop (AC.drop AC.iden)))\n'
                   '    (@elements_amount_hash_spec term).\n'],
                  ['Coq/C/jet_elements_asset_amount_hash_spec.v',
                   'statement',
                   'elements_asset_amount_hash_spec_parametric',
                   'Lemma elements_asset_amount_hash_spec_parametric : Alg.Assertion.Parametric '
                   '(@elements_asset_amount_hash_spec).\n'],
                  ['Coq/C/jet_elements_asset_amount_hash_spec.v',
                   'declaration',
                   'elements_asset_amount_bytes',
                   'Definition elements_asset_amount_bytes (v : Ty.tySem elements_asset_amount_type) : '
                   'list (Ty.tySem Word8) :=\n'
                   '  elements_asset_bytes (fst v) ++ elements_amount_bytes (snd v).\n'],
                  ['Coq/C/jet_elements_asset_amount_hash_spec.v',
                   'statement',
                   'elements_asset_amount_hash_option',
                   'Lemma elements_asset_amount_hash_option c v :\n'
                   '  @elements_asset_amount_hash_spec optalg (c, v) = ctx8_add_list c '
                   '(elements_asset_amount_bytes v).\n'],
                  ['Coq/C/jet_elements_asset_amount_hash_spec.v',
                   'statement',
                   'elements_asset_bytes_length',
                   'Lemma elements_asset_bytes_length v : length (elements_asset_bytes v) = 33%nat.\n'],
                  ['Coq/C/jet_elements_asset_amount_hash_spec.v',
                   'statement',
                   'elements_amount_bytes_bound',
                   'Lemma elements_amount_bytes_bound v : (length (elements_amount_bytes v) <= '
                   '33)%nat.\n'],
                  ['Coq/C/jet_elements_asset_amount_hash_spec.v',
                   'statement',
                   'elements_asset_amount_bytes_bound',
                   'Lemma elements_asset_amount_bytes_bound v : Z.of_nat (length '
                   '(elements_asset_amount_bytes v)) <= 66.\n'],
                  ['Coq/C/jet_elements_amounts_hash_program.v',
                   'declaration',
                   'elements_amounts_hash_spec',
                   'Definition elements_amounts_hash_spec\n'
                   '    (pm : Elements.t Word32 (Ty.Sum Ty.Unit elements_amount_hash_type))\n'
                   '    (pa : Elements.t Word32 (Ty.Sum Ty.Unit elements_asset_hash_type))\n'
                   '    {alg : EFP.Algebra} : EFP.domain alg Ty.Unit Word256 :=\n'
                   '  let term := EFP.CanonicalStructures.toAssertion alg in\n'
                   '  let core := Alg.Assertion.toCore term in\n'
                   '  @hash_elems_spec elements_asset_amount_type (fun term => '
                   '@elements_asset_amount_hash_spec term) 5 term\n'
                   '    (@AC.drop Ty.Unit Word32 _ core\n'
                   '      (@elements_amount_pair_spec alg Word32 elements_amount_hash_type '
                   'elements_asset_hash_type\n'
                   '        (@EFP.Combinators.prim _ _ alg pm) (@EFP.Combinators.prim _ _ alg pa))).\n'],
                  ['Coq/C/jet_elements_amounts_hash_program.v',
                   'statement',
                   'elements_amounts_hash_spec_parametric',
                   'Lemma elements_amounts_hash_spec_parametric pm pa : EFP.Parametric '
                   '(@elements_amounts_hash_spec pm pa).\n'],
                  ['Coq/C/jet_elements_amounts_hash_program.v',
                   'statement',
                   'elements_amounts_loop_bound',
                   'Lemma elements_amounts_loop_bound : 66 * wsize 5 / 64 < ctx8_limit.\n'],
                  ['Coq/C/jet_elements_amounts_hash_program.v',
                   'statement',
                   'elements_amounts_hash_spec_sem',
                   'Theorem elements_amounts_hash_spec_sem pm pa\n'
                   '    (xs_of : Elements.env -> list (Ty.tySem elements_asset_amount_type)) :\n'
                   '  (forall i e,\n'
                   '    @elements_amount_pair_spec elements_hash_alg Word32 elements_amount_hash_type '
                   'elements_asset_hash_type\n'
                   '      (@EFP.Combinators.prim _ _ elements_hash_alg pm) (@EFP.Combinators.prim _ _ '
                   'elements_hash_alg pa) i e =\n'
                   '    Some (match nth_error (xs_of e) (Z.to_nat (wz 5 i)) with Some x => inr x | None '
                   '=> inl tt end)) ->\n'
                   '  forall e, @elements_amounts_hash_spec pm pa elements_hash_alg tt e =\n'
                   '    Some (from_hash256 (elems_hash_of elements_asset_amount_type '
                   'elements_asset_amount_bytes 5 (xs_of e))).\n'],
                  ['Coq/C/jet_elements_amounts_hash_program.v',
                   'statement',
                   'elements_tx_amounts_hash_jet',
                   'Theorem elements_tx_amounts_hash_jet pm pa xs_of (f : function) (field : ident) '
                   '(hdelta : Z) :\n'
                   '  (forall i e,\n'
                   '    @elements_amount_pair_spec elements_hash_alg Word32 elements_amount_hash_type '
                   'elements_asset_hash_type\n'
                   '      (@EFP.Combinators.prim _ _ elements_hash_alg pm) (@EFP.Combinators.prim _ _ '
                   'elements_hash_alg pa) i e =\n'
                   '    Some (match nth_error (xs_of e) (Z.to_nat (wz 5 i)) with Some x => inr x | None '
                   '=> inl tt end)) ->\n'
                   '  elements_wrapper_shape f (elements_simple_rest (elements_hash_mid_writeHash _tx '
                   '_elementsTransaction field)) ->\n'
                   '  elements_field_at _elementsTransaction field hdelta ->\n'
                   '  0 <= hdelta /\\ hdelta + 32 <= 760 ->\n'
                   '  application_jet_local_spec_sep f elements_ge Elements.env Ty.Unit Word256\n'
                   '    (hash_getter_rep (fun e => elems_hash_of elements_asset_amount_type '
                   'elements_asset_amount_bytes 5 (xs_of e)) 0 hdelta 760)\n'
                   '    (fun a e => @elements_amounts_hash_spec pm pa elements_hash_alg a e).\n'],
                  ['Coq/C/jet_elements_amounts_hash_program.v',
                   'declaration',
                   'elements_output_amounts_of',
                   'Definition elements_output_amounts_of (e : Elements.env) : list (Ty.tySem '
                   'elements_asset_amount_type) :=\n'
                   '  map (fun txo => (encode_asset (clearPrf (txoAsset txo)), encode_amount (clearPrf '
                   '(txoAmount txo))))\n'
                   '    (sigTxOut (Elements.envTx e)).\n'],
                  ['Coq/C/jet_elements_amounts_hash_program.v',
                   'statement',
                   'elements_output_amounts_of_sem',
                   'Lemma elements_output_amounts_of_sem i e :\n'
                   '  @elements_output_amount_spec elements_hash_alg i e =\n'
                   '    Some (match nth_error (elements_output_amounts_of e) (Z.to_nat (wz 5 i)) with '
                   'Some x => inr x | None => inl tt end).\n'],
                  ['Coq/C/jet_elements_amounts_hash_program.v',
                   'declaration',
                   'elements_output_amounts_hash_spec',
                   'Definition elements_output_amounts_hash_spec {alg : EFP.Algebra} : EFP.domain alg '
                   'Ty.Unit Word256 :=\n'
                   '  @elements_amounts_hash_spec Elements.OutputAmount Elements.OutputAsset alg.'],
                  ['Coq/C/jet_elements_amounts_hash_program.v',
                   'declaration',
                   'elements_output_amounts_hash_of',
                   'Definition elements_output_amounts_hash_of (e : Elements.env) : hash256 :=\n'
                   '  elems_hash_of elements_asset_amount_type elements_asset_amount_bytes 5 '
                   '(elements_output_amounts_of e).\n'],
                  ['Coq/C/jet_elements_amounts_hash_program.v',
                   'statement',
                   'elements_output_amounts_hash_program_local_spec',
                   'Theorem elements_output_amounts_hash_program_local_spec :\n'
                   '  application_jet_local_spec_sep f_simplicity_output_amounts_hash elements_ge '
                   'Elements.env Ty.Unit Word256\n'
                   '    (hash_getter_rep elements_output_amounts_hash_of 0 24 760)\n'
                   '    (fun a e => @elements_output_amounts_hash_spec elements_hash_alg a e).\n'],
                  ['Coq/C/jet_elements_amounts_hash_program.v',
                   'declaration',
                   'elements_input_amounts_of',
                   'Definition elements_input_amounts_of (e : Elements.env) : list (Ty.tySem '
                   'elements_asset_amount_type) :=\n'
                   '  map (fun txi => (encode_asset (utxoAsset (sigTxiTxo txi)), encode_amount '
                   '(utxoAmount (sigTxiTxo txi))))\n'
                   '    (sigTxIn (Elements.envTx e)).\n'],
                  ['Coq/C/jet_elements_amounts_hash_program.v',
                   'statement',
                   'elements_input_amounts_of_sem',
                   'Lemma elements_input_amounts_of_sem i e :\n'
                   '  @elements_input_amount_spec elements_hash_alg i e =\n'
                   '    Some (match nth_error (elements_input_amounts_of e) (Z.to_nat (wz 5 i)) with '
                   'Some x => inr x | None => inl tt end).\n'],
                  ['Coq/C/jet_elements_amounts_hash_program.v',
                   'declaration',
                   'elements_input_amounts_hash_spec',
                   'Definition elements_input_amounts_hash_spec {alg : EFP.Algebra} : EFP.domain alg '
                   'Ty.Unit Word256 :=\n'
                   '  @elements_amounts_hash_spec Elements.InputAmount Elements.InputAsset alg.'],
                  ['Coq/C/jet_elements_amounts_hash_program.v',
                   'declaration',
                   'elements_input_amounts_hash_of',
                   'Definition elements_input_amounts_hash_of (e : Elements.env) : hash256 :=\n'
                   '  elems_hash_of elements_asset_amount_type elements_asset_amount_bytes 5 '
                   '(elements_input_amounts_of e).\n'],
                  ['Coq/C/jet_elements_amounts_hash_program.v',
                   'statement',
                   'elements_input_amounts_hash_program_local_spec',
                   'Theorem elements_input_amounts_hash_program_local_spec :\n'
                   '  application_jet_local_spec_sep f_simplicity_input_amounts_hash elements_ge '
                   'Elements.env Ty.Unit Word256\n'
                   '    (hash_getter_rep elements_input_amounts_hash_of 0 248 760)\n'
                   '    (fun a e => @elements_input_amounts_hash_spec elements_hash_alg a e).\n'],
                  ['Coq/C/jet_elements_amount_jets.v',
                   'declaration',
                   'elements_amount_pair_spec',
                   'Definition elements_amount_pair_spec {alg : Primitive.Algebra} {A CM CA : Ty}\n'
                   '    (pm : alg A (Ty.Sum Ty.Unit CM)) (pa : alg A (Ty.Sum Ty.Unit CA)) :\n'
                   '    alg A (Ty.Sum Ty.Unit (Ty.Prod CA CM)) :=\n'
                   '  Alg.Core.Combinators.comp (Alg.Core.Combinators.pair pm pa)\n'
                   '    (Alg.Core.Combinators.case (Alg.Core.Combinators.injl '
                   'Alg.Core.Combinators.unit)\n'
                   '      (Alg.Core.Combinators.comp\n'
                   '        (Alg.Core.Combinators.pair (Alg.Core.Combinators.drop '
                   'Alg.Core.Combinators.iden)\n'
                   '          (Alg.Core.Combinators.take Alg.Core.Combinators.iden))\n'
                   '        (Alg.Core.Combinators.case (Alg.Core.Combinators.injl '
                   'Alg.Core.Combinators.unit)\n'
                   '          (Alg.Core.Combinators.injr Alg.Core.Combinators.iden)))).\n'],
                  ['Coq/C/jet_elements_amount_jets.v',
                   'declaration',
                   'amount_pair_result',
                   'Definition amount_pair_result {A} (elems : list A) (ga : A -> assetWith unit) (gm : '
                   'A -> amountWith unit)\n'
                   '    (a : Ty.tySem Word32) : Ty.tySem (Ty.Sum Ty.Unit (Ty.Prod (ConfTy Word256) '
                   '(ConfTy Word64))) :=\n'
                   '  match nth_error elems (Z.to_nat (toZ a)) with\n'
                   '  | Some x => inr (encode_asset (ga x), encode_amount (gm x))\n'
                   '  | None => inl tt\n'
                   '  end.\n'],
                  ['Coq/C/jet_elements_amount_jets.v',
                   'declaration',
                   'elements_input_amount_spec',
                   'Definition elements_input_amount_spec {alg : Primitive.Algebra} :\n'
                   '    alg Word32 (Ty.Sum Ty.Unit (Ty.Prod (ConfTy Word256) (ConfTy Word64))) :=\n'
                   '  elements_amount_pair_spec (Primitive.Combinators.prim Elements.InputAmount)\n'
                   '    (Primitive.Combinators.prim Elements.InputAsset).\n'],
                  ['Coq/C/jet_elements_amount_jets.v',
                   'declaration',
                   'elements_output_amount_spec',
                   'Definition elements_output_amount_spec {alg : Primitive.Algebra} :\n'
                   '    alg Word32 (Ty.Sum Ty.Unit (Ty.Prod (ConfTy Word256) (ConfTy Word64))) :=\n'
                   '  elements_amount_pair_spec (Primitive.Combinators.prim Elements.OutputAmount)\n'
                   '    (Primitive.Combinators.prim Elements.OutputAsset).\n'],
                  ['Coq/C/jet_elements_amount_jets.v',
                   'declaration',
                   'encode_amount',
                   'Definition encode_amount (a : amountWith unit) : Ty.tySem (ConfTy Word64) :=\n'
                   '  match a with\n'
                   '  | Explicit v => inr (@fromZ (WordToZ 6) (Int64.unsigned v))\n'
                   '  | Confidential (Point odd x) _ => inl (conf_toBit odd, from_hash256 x)\n'
                   '  end.\n'],
                  ['Coq/C/jet_elements_amount_jets.v',
                   'statement',
                   'elements_amount_pair_sem',
                   'Lemma elements_amount_pair_sem {A CM CA : Ty}\n'
                   '    (tm : Ty.tySem A -> Elements.env -> option (Ty.tySem (Ty.Sum Ty.Unit CM)))\n'
                   '    (ta : Ty.tySem A -> Elements.env -> option (Ty.tySem (Ty.Sum Ty.Unit CA))) (a : '
                   'Ty.tySem A) env :\n'
                   '  @elements_amount_pair_spec (PrimitivePrimSem option_Monad_Zero) A CM CA tm ta a '
                   'env =\n'
                   '    match tm a env, ta a env with\n'
                   '    | Some (inr am), Some (inr ast) => Some (inr (ast, am))\n'
                   '    | Some (inl _), Some _ => Some (inl tt)\n'
                   '    | Some (inr _), Some (inl _) => Some (inl tt)\n'
                   '    | _, _ => None\n'
                   '    end.\n'],
                  ['Coq/C/jet_elements_amount_jets.v',
                   'statement',
                   'elements_input_amount_sem',
                   'Lemma elements_input_amount_sem a environment :\n'
                   '  @elements_input_amount_spec (PrimitivePrimSem option_Monad_Zero) a environment =\n'
                   '    Some (amount_pair_result (sigTxIn (Elements.envTx environment))\n'
                   '      (fun txi => utxoAsset (sigTxiTxo txi)) (fun txi => utxoAmount (sigTxiTxo '
                   'txi)) a).\n'],
                  ['Coq/C/jet_elements_amount_jets.v',
                   'statement',
                   'elements_output_amount_sem',
                   'Lemma elements_output_amount_sem a environment :\n'
                   '  @elements_output_amount_spec (PrimitivePrimSem option_Monad_Zero) a environment '
                   '=\n'
                   '    Some (amount_pair_result (sigTxOut (Elements.envTx environment))\n'
                   '      (fun txo => clearPrf (txoAsset txo)) (fun txo => clearPrf (txoAmount txo)) '
                   'a).\n'],
                  ['Coq/C/jet_elements_asset_jets.v',
                   'declaration',
                   'encode_asset',
                   'Definition encode_asset (a : assetWith unit) : Ty.tySem (ConfTy Word256) :=\n'
                   '  match a with\n'
                   '  | Explicit h => inr (from_hash256 h)\n'
                   '  | Confidential (Point odd x) _ => inl (conf_toBit odd, from_hash256 x)\n'
                   '  end.\n'],
                  ['Coq/C/jet_elements_asset_literal.v',
                   'declaration',
                   'packed_fe_integer_literal',
                   'Definition packed_fe_integer_literal (packed : hash256) : Z :=\n'
                   '  haskell_word256_integer\n'
                   '    (haskell_be256_run (hash256_to_bytelist packed) (haskell_word256_from_integer '
                   '0)).\n'],
                  ['Coq/C/jet_elements_asset_literal.v',
                   'declaration',
                   'encode_confidential_literal',
                   'Definition encode_confidential_literal {A : Set} {B : Ty}\n'
                   '    (enc : A -> tySem B) (c : confidential unit A) : tySem (ConfLiteral B) :=\n'
                   '  match c with\n'
                   '  | Explicit x => inr (enc x)\n'
                   '  | Confidential (Point odd packed) _ =>\n'
                   '      inl ((if odd then inr tt else inl tt), haskell_to_word 8 '
                   '(packed_fe_integer_literal packed))\n'
                   '  end.\n'],
                  ['Coq/C/jet_elements_asset_literal.v',
                   'declaration',
                   'encode_asset_literal',
                   'Definition encode_asset_literal (a : assetWith unit) : tySem AssetConf :=\n'
                   '  encode_confidential_literal\n'
                   '    (fun h => haskell_to_word 8 (haskell_integer_hash256 (hash256_to_bytelist h))) '
                   'a.\n'],
                  ['Coq/C/jet_elements_asset_literal.v',
                   'statement',
                   'packed_fe_to_word_literal_matches',
                   'Lemma packed_fe_to_word_literal_matches packed :\n'
                   '  haskell_to_word 8 (packed_fe_integer_literal packed) = from_hash256 packed.\n'],
                  ['Coq/C/jet_elements_asset_literal.v',
                   'statement',
                   'encode_asset_literal_matches',
                   'Lemma encode_asset_literal_matches a : encode_asset a = encode_asset_literal a.\n'],
                  ['Coq/C/jet_elements_amount_literal.v',
                   'declaration',
                   'encode_amount_literal',
                   'Definition encode_amount_literal (a : amountWith unit) : tySem (ConfLiteral Word64) '
                   ':=\n'
                   '  encode_confidential_literal (fun v => haskell_to_word 6 (Int64.unsigned v)) a.\n'],
                  ['Coq/C/jet_elements_amount_literal.v',
                   'statement',
                   'encode_amount_literal_matches',
                   'Lemma encode_amount_literal_matches a : encode_amount a = encode_amount_literal '
                   'a.\n'],
                  ['Coq/C/jet_elements_amount_literal.v',
                   'statement',
                   'amount_pair_literal_matches',
                   'Lemma amount_pair_literal_matches {X : Type} (values : list X) asset_of amount_of a '
                   ':\n'
                   '  Some (amount_pair_result values asset_of amount_of a) =\n'
                   '    amount_pair_literal values asset_of amount_of a.\n'],
                  ['Coq/C/jet_elements_prim.v',
                   'declaration',
                   'encodeConfidential',
                   'Let encodeConfidential {A : Set} {B : Ty} (enc : A -> tySem B) (c : confidential '
                   'unit A) :\n'
                   '    tySem (Conf B) :=\n'
                   'match c with\n'
                   '| Explicit a => inr (enc a)\n'
                   '| Confidential (Point odd x) _ => inl (toBit odd, from_hash256 x)\n'
                   'end.\n'],
                  ['Coq/C/jet_elements_prim.v',
                   'declaration',
                   'encodeAsset',
                   'Let encodeAsset (a : assetWith unit) : tySem (Conf Word256) := encodeConfidential '
                   'encodeHash a.\n'],
                  ['Coq/C/jet_elements_prim.v',
                   'declaration',
                   'encodeAmount',
                   'Let encodeAmount (a : amountWith unit) : tySem (Conf Word64) :=\n'
                   '  encodeConfidential (fun v => fromZ (Int64.unsigned v) : tySem Word64) a.\n'],
                  ['Coq/C/jet_elements_prim.v',
                   'declaration',
                   'sem',
                   'Definition sem {A B} (p : t A B) (a : A) (e : env) : option B :=\n'
                   'let tx := envTx e in\n'
                   'let ix := envIx e in\n'
                   'let atInput {A : Ty} (f : sigTxInput -> A) (i : Word32) : option (tySem (S A)) :=\n'
                   '  Some (cast (option_map f (nth_error (sigTxIn tx) (Z.to_nat (toZ i))))) in\n'
                   'let atOutput {A : Ty} (f : txOutput -> A) (i : Word32) : option (tySem (S A)) :=\n'
                   '  Some (cast (option_map f (nth_error (sigTxOut tx) (Z.to_nat (toZ i))))) in\n'
                   '(match p in prim A B return A -> option B with\n'
                   ' | Version => fun _ => Some (fromZ (Int.unsigned (sigTxVersion tx)))\n'
                   ' | LockTime => fun _ => Some (fromZ (Int.unsigned (sigTxLock tx)))\n'
                   ' | InputPegin => atInput (fun txi => cast (option_map encodeHash (sigTxiPegin '
                   'txi)))\n'
                   ' | InputPrevOutpoint => atInput (fun txi => encodeOutpoint (sigTxiPreviousOutpoint '
                   'txi))\n'
                   ' | InputAsset => atInput (fun txi => encodeAsset (utxoAsset (sigTxiTxo txi)))\n'
                   ' | InputAmount => atInput (fun txi => encodeAmount (utxoAmount (sigTxiTxo txi)))\n'
                   ' | InputScriptHash => atInput (fun txi => encodeHash (byteStringHash (utxoScript '
                   '(sigTxiTxo txi))))\n'
                   ' | InputSequence => atInput (fun txi => fromZ (Int.unsigned (sigTxiSequence txi)))\n'
                   ' | InputAnnexHash => atInput (fun txi =>\n'
                   '     cast (option_map (fun x => encodeHash (byteStringHash x)) (sigTxiAnnex txi)))\n'
                   ' | InputScriptSigHash => atInput (fun txi => encodeHash (byteStringHash '
                   '(sigTxiScriptSig txi)))\n'
                   ' | ReissuanceBlinding => atInput (fun txi =>\n'
                   '     cast (option_map encodeHash\n'
                   '       (match sigTxiIssuance txi with\n'
                   '        | Some (inr re) => Some (reissuanceBlindingNonce re)\n'
                   '        | _ => None\n'
                   '        end)))\n'
                   ' | NewIssuanceContract => atInput (fun txi =>\n'
                   '     cast (option_map encodeHash\n'
                   '       (match sigTxiIssuance txi with\n'
                   '        | Some (inl new) => Some (newIssuanceContractHash new)\n'
                   '        | _ => None\n'
                   '        end)))\n'
                   ' | ReissuanceEntropy => atInput (fun txi =>\n'
                   '     cast (option_map encodeHash\n'
                   '       (match sigTxiIssuance txi with\n'
                   '        | Some (inr re) => Some (reissuanceEntropy re)\n'
                   '        | _ => None\n'
                   '        end)))\n'
                   ' | IssuanceAssetAmount => atInput (fun txi =>\n'
                   '     cast (option_map (fun i => encodeAmount (clearPrf (issuanceAmount i))) '
                   '(sigTxiIssuance txi)))\n'
                   ' | IssuanceTokenAmount => atInput (fun txi =>\n'
                   '     cast (option_map (fun i => encodeAmount (clearPrf (issuanceTokenAmount i))) '
                   '(sigTxiIssuance txi)))\n'
                   ' | IssuanceAssetProof => atInput (fun txi =>\n'
                   '     encodeHash (byteStringHash (issuanceProof issuanceAmount txi)))\n'
                   ' | IssuanceTokenProof => atInput (fun txi =>\n'
                   '     encodeHash (byteStringHash (issuanceProof issuanceTokenAmount txi)))\n'
                   ' | CurrentIndex => fun _ => Some (fromZ (Z.of_nat ix))\n'
                   ' | TapleafVersion => fun _ => Some (fromZ (Byte.unsigned (tapleafVersion (envTap '
                   'e))))\n'
                   ' | Tappath => fun i : Word8 =>\n'
                   '     Some (cast (option_map encodeHash (nth_error (tappath (envTap e)) (Z.to_nat '
                   '(toZ i)))))\n'
                   ' | InternalKey => fun _ => Some (from_hash256 (tapInternalKey (envTap e)))\n'
                   ' | OutputAsset => atOutput (fun txo => encodeAsset (clearPrf (txoAsset txo)))\n'
                   ' | OutputAmount => atOutput (fun txo => encodeAmount (clearPrf (txoAmount txo)))\n'
                   ' | OutputNonce => atOutput (fun txo => encodeNonce (txoNonce txo))\n'
                   ' | OutputScriptHash => atOutput (fun txo => encodeHash (byteStringHash (txoScript '
                   'txo)))\n'
                   ' | OutputNullDatum => fun ij =>\n'
                   '     let i : Word32 := fst ij in\n'
                   '     let j : Word32 := snd ij in\n'
                   '     Some (cast\n'
                   '       (match nth_error (sigTxOut tx) (Z.to_nat (toZ i)) with\n'
                   '        | Some txo =>\n'
                   '            match txNullData (txoScript txo) with\n'
                   '            | Some nullData =>\n'
                   '                Some (cast (option_map\n'
                   '                  (fun d => encodeNullDatum (mapNullDatum byteStringHash d))\n'
                   '                  (nth_error nullData (Z.to_nat (toZ j)))))\n'
                   '            | None => None\n'
                   '            end\n'
                   '        | None => None\n'
                   '        end))\n'
                   ' | OutputSurjectionProof => atOutput (fun txo => encodeHash (byteStringHash '
                   '(viewPrf (txoAsset txo))))\n'
                   ' | OutputRangeProof => atOutput (fun txo => encodeHash (byteStringHash (viewPrf '
                   '(txoAmount txo))))\n'
                   ' | GenesisBlockHash => fun _ => Some (encodeHash (envGenesisBlock e))\n'
                   ' | ScriptCMR => fun _ => Some (encodeHash (tapScriptCMR (envTap e)))\n'
                   ' | TransactionId => fun _ => Some (encodeHash (txid tx))\n'
                   ' end\n'
                   ') a.\n']],
 'blocks': [['Haskell/Core/Simplicity/Programs/Elements.hs',
             '\n  , assetAmountHash = ',
             '\n  , nonceHash = ',
             '(oh &&& ioh >>> assetHash) &&& iih >>> amountHash'],
            ['Haskell/Core/Simplicity/Programs/Elements.hs',
             '\n    assetHash = ',
             '\n    amountHash = ',
             'oh &&& drop (copair (take (copair (scribe (toWord8 0x0a)) (scribe (toWord8 0x0b))) &&& '
             'ih) ((unit >>> scribe (toWord8 0x01)) &&& iden))\n'
             '            >>> (oh &&& ioh >>> ctx8Add1) &&& iih >>> ctx8Add32'],
            ['Haskell/Core/Simplicity/Programs/Elements.hs',
             '\n    amountHash = ',
             '\n    taptweakPrefix = ',
             'ih &&& oh\n'
             '             >>> match ((ih &&& take (take (copair (scribe (toWord8 0x08)) (scribe '
             '(toWord8 0x09)))) >>> ctx8Add1) &&& oih >>> ctx8Add32)\n'
             '                       ((ih &&& (unit >>> scribe (toWord8 0x01)) >>> ctx8Add1) &&& oh >>> '
             'ctx8Add8)'],
            ['Haskell/Simplicity/Elements/Programs/SigHash.hs',
             '\n    outputAmountsHash =\n',
             '\n  , outputNoncesHash =',
             '     let\n'
             '       finalize = ctx8Finalize\n'
             '       body = take (drop outputAmount) &&& ih\n'
             '          >>> match (injl ih) (injr (ih &&& oh >>> assetAmountHash))\n'
             '     in\n'
             '      unit &&& ctx8Init >>> forWhile word32 body >>> copair finalize finalize\n'],
            ['Haskell/Simplicity/Elements/Programs/SigHash.hs',
             '\n  , inputAmountsHash =\n',
             '\n  , inputScriptsHash =',
             '     let\n'
             '      finalize = ctx8Finalize\n'
             '      body = take (drop inputAmount) &&& ih\n'
             '         >>> match (injl ih) (injr (ih &&& oh >>> assetAmountHash))\n'
             '     in\n'
             '      unit &&& ctx8Init >>> forWhile word32 body >>> copair finalize finalize\n'],
            ['Haskell/Simplicity/Elements/Programs/Transaction.hs',
             '\n  , outputAmount = primitive',
             '\n  , outputIsFee =',
             ' OutputAmount &&& primitive OutputAsset\n'
             '               >>> match (injl unit) (ih &&& oh >>> match (injl unit) (injr iden))\n'],
            ['Haskell/Simplicity/Elements/Programs/Transaction.hs',
             '\n  , inputAmount = primitive',
             '\n  , currentPegin =',
             ' InputAmount &&& primitive InputAsset\n'
             '              >>> match (injl unit) (ih &&& oh >>> match (injl unit) (injr iden))\n']],
 'lines': [['Haskell/Simplicity/Elements/Jets.hs',
            'specificationSigHash OutputAmountsHash',
            'SigHash.outputAmountsHash'],
           ['Haskell/Simplicity/Elements/Programs/SigHash/Lib.hs',
            'outputAmountsHash',
            'SigHash.outputAmountsHash SigHash.lib'],
           ['Haskell/Simplicity/Elements/Programs/Transaction/Lib.hs',
            'outputAmount',
            'Transaction.outputAmount Transaction.lib'],
           ['Haskell/Elements/Simplicity/Elements/Primitive.hs',
            'primName OutputAsset',
            '"outputAsset"'],
           ['Haskell/Elements/Simplicity/Elements/Primitive.hs',
            'primName OutputAmount',
            '"outputAmount"'],
           ['Haskell/Simplicity/Elements/Jets.hs',
            'specificationSigHash InputAmountsHash',
            'SigHash.inputAmountsHash'],
           ['Haskell/Simplicity/Elements/Programs/SigHash/Lib.hs',
            'inputAmountsHash',
            'SigHash.inputAmountsHash SigHash.lib'],
           ['Haskell/Simplicity/Elements/Programs/Transaction/Lib.hs',
            'inputAmount',
            'Transaction.inputAmount Transaction.lib'],
           ['Haskell/Elements/Simplicity/Elements/Primitive.hs', 'primName InputAsset', '"inputAsset"'],
           ['Haskell/Elements/Simplicity/Elements/Primitive.hs',
            'primName InputAmount',
            '"inputAmount"'],
           ['Haskell/Core/Simplicity/Programs/Elements/Lib.hs',
            'assetAmountHash',
            'Elements.assetAmountHash Elements.libAssert'],
           ['Haskell/Core/Simplicity/Programs/Elements.hs', 'ctx8Add8', 'ctx8Addn vector8'],
           ['Haskell/Core/Simplicity/Programs/Elements.hs', 'ctx8Add32', 'ctx8Addn vector32'],
           ['Haskell/Elements/Simplicity/Elements/Primitive.hs',
            'encodeConfidential enc (Explicit a)',
            'Right (enc a)'],
           ['Haskell/Elements/Simplicity/Elements/Primitive.hs',
            'encodeConfidential enc (Confidential (Point by x) ())',
            'Left (toBit by, toWord256 . Schnorr.fe_repr $ x)'],
           ['Haskell/Elements/Simplicity/Elements/Primitive.hs',
            'encodeAsset',
            'encodeConfidential encodeHash . view (under asset)'],
           ['Haskell/Elements/Simplicity/Elements/Primitive.hs',
            'encodeAmount',
            'encodeConfidential (toWord64 . toInteger) . view (under amount)'],
           ['Haskell/Elements/Simplicity/Elements/Primitive.hs',
            'interpret InputAsset',
            'return . (atInput $ encodeAsset . utxoAsset . sigTxiTxo)'],
           ['Haskell/Elements/Simplicity/Elements/Primitive.hs',
            'interpret InputAmount',
            'return . (atInput $ encodeAmount . utxoAmount . sigTxiTxo)'],
           ['Haskell/Elements/Simplicity/Elements/Primitive.hs',
            'interpret OutputAsset',
            'return . (atOutput $ encodeAsset . clearAssetPrf . txoAsset)'],
           ['Haskell/Elements/Simplicity/Elements/Primitive.hs',
            'interpret OutputAmount',
            'return . (atOutput $ encodeAmount . clearAmountPrf . txoAmount)']],
 'fragments': [('Haskell/Simplicity/Elements/Jets.hs', 'OutputAmountsHash :: SigHashJet () Word256'),
               ('Haskell/Elements/Simplicity/Elements/Primitive.hs',
                'OutputAsset :: Prim Word32 (S (Conf Word256))'),
               ('Coq/C/jet_elements_prim.v', '| OutputAsset : prim Word32 (S (Conf Word256))'),
               ('Haskell/Elements/Simplicity/Elements/Primitive.hs',
                'OutputAmount :: Prim Word32 (S (Conf Word64))'),
               ('Coq/C/jet_elements_prim.v', '| OutputAmount : prim Word32 (S (Conf Word64))'),
               ('Haskell/Simplicity/Elements/Jets.hs', 'InputAmountsHash :: SigHashJet () Word256'),
               ('Haskell/Elements/Simplicity/Elements/Primitive.hs',
                'InputAsset :: Prim Word32 (S (Conf Word256))'),
               ('Coq/C/jet_elements_prim.v', '| InputAsset : prim Word32 (S (Conf Word256))'),
               ('Haskell/Elements/Simplicity/Elements/Primitive.hs',
                'InputAmount :: Prim Word32 (S (Conf Word64))'),
               ('Coq/C/jet_elements_prim.v', '| InputAmount : prim Word32 (S (Conf Word64))')]}
