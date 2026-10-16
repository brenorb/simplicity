"""Fixed selected-source model for sixteen raw Bitcoin hash-program endpoints.

Reviewed alongside the execution proofs; not generated during checking.
This .py runtime input is included by normal audit fingerprints (unlike JSON).
"""
MODEL = {
  "declarations": [
    [
      "Coq/C/jet_bitcoin_raw_program.v",
      "declaration",
      "raw_full_sem",
      "Definition raw_full_sem {A B} (p : BitcoinFull.t A B) (a : Ty.tySem A)\n    (environment : raw_bitcoin_environment) : option (Ty.tySem B) :=\n  (match p in BitcoinFull.prim A B return Ty.tySem A -> option (Ty.tySem B) with\n   | BitcoinFull.Base q => fun a => Bitcoin.sem q a (raw_base environment)\n   | BitcoinFull.Ext q => fun a => raw_ext_sem q a environment\n   end) a."
    ],
    [
      "Coq/C/jet_bitcoin_raw_program.v",
      "declaration",
      "raw_fullalg",
      "Definition raw_fullalg : PF.Algebra :=\n  @PF._Pack (fun A B => Ty.tySem A -> raw_bitcoin_environment -> option (Ty.tySem B))\n    (@PF.Class _\n      (Alg.Assertion.class_of (Alg.AssertionSem (ReaderT_CIMonadZero raw_bitcoin_environment option_Monad_Zero)))\n      (@PF.Mixin _ (@raw_full_sem)))."
    ],
    [
      "Coq/C/jet_bitcoin_raw_program.v",
      "declaration",
      "raw_program_relation",
      "Definition raw_program_relation {A B} (f : PF.domain fullalg A B)\n    (g : PF.domain raw_fullalg A B) : Prop :=\n  forall a environment Hpath,\n    f a (project_raw_environment environment Hpath) = g a environment."
    ],
    [
      "Coq/C/jet_bitcoin_raw_program.v",
      "declaration",
      "raw_program_parametric_relation",
      "Definition raw_program_parametric_relation : PF.Parametric.Rel fullalg raw_fullalg :=\n  @PF.Parametric.Pack fullalg raw_fullalg (@raw_program_relation) raw_program_relation_class."
    ],
    [
      "Coq/C/jet_bitcoin_raw_program.v",
      "statement",
      "raw_full_projection",
      "Lemma raw_full_projection {A B} (p : BitcoinFull.t A B) a environment Hpath :\n  BitcoinFull.sem p a (project_raw_environment environment Hpath) = raw_full_sem p a environment."
    ],
    [
      "Coq/C/jet_bitcoin_raw_program.v",
      "statement",
      "raw_core_relation_class",
      "Lemma raw_core_relation_class :\n  @Alg.Core.Parametric.class fullcore (PF.CanonicalStructures.toCore raw_fullalg)\n    (@raw_program_relation)."
    ],
    [
      "Coq/C/jet_bitcoin_raw_program.v",
      "statement",
      "raw_assertion_relation_class",
      "Lemma raw_assertion_relation_class :\n  @Alg.Assertion.Parametric.class fullassert (PF.CanonicalStructures.toAssertion raw_fullalg)\n    (@raw_program_relation)."
    ],
    [
      "Coq/C/jet_bitcoin_raw_program.v",
      "statement",
      "raw_program_relation_class",
      "Lemma raw_program_relation_class :\n  @PF.Parametric.class fullalg raw_fullalg (@raw_program_relation)."
    ],
    [
      "Coq/C/jet_bitcoin_raw_program.v",
      "statement",
      "bitcoin_program_raw_projection",
      "Theorem bitcoin_program_raw_projection {A B : Ty}\n    (program : forall alg : PF.Algebra, PF.domain alg A B)\n    (Hprogram : PF.Parametric program) a environment Hpath :\n  program fullalg a (project_raw_environment environment Hpath) = program raw_fullalg a environment."
    ],
    [
      "Coq/C/jet_bitcoin_raw_program.v",
      "statement",
      "application_raw_program_local_spec_sep",
      "Theorem application_raw_program_local_spec_sep f ge A B rep\n    (program : forall alg : PF.Algebra, PF.domain alg A B)\n    (Hprogram : PF.Parametric program) :\n  application_jet_local_spec_sep f ge ext_environment A B rep (program fullalg) ->\n  application_jet_local_spec_sep f ge raw_bitcoin_environment A B\n    (raw_env_rep rep) (program raw_fullalg)."
    ],
    [
      "Coq/C/jet_bitcoin_hash_raw_program.v",
      "statement",
      "bitcoin_output_values_hash_raw_program_local_spec",
      "Theorem bitcoin_output_values_hash_raw_program_local_spec :\n  application_jet_local_spec_sep f_simplicity_bitcoin_output_values_hash bitcoin_ge raw_bitcoin_environment\n    Ty.Unit Word256\n    (raw_env_rep (hash_getter_rep (fun e => words_hash_of 3 5 (output_values_of e)) 0 16 432))\n    (fun a environment => @prim_words_hash_spec 3 5 (BitcoinFull.Base Bitcoin.OutputValue) raw_fullalg a environment)."
    ],
    [
      "Coq/C/jet_bitcoin_hash_raw_program.v",
      "statement",
      "bitcoin_output_scripts_hash_raw_program_local_spec",
      "Theorem bitcoin_output_scripts_hash_raw_program_local_spec :\n  application_jet_local_spec_sep f_simplicity_bitcoin_output_scripts_hash bitcoin_ge raw_bitcoin_environment\n    Ty.Unit Word256\n    (raw_env_rep (hash_getter_rep (fun e => words_hash_of 5 5 (output_scripts_of e)) 0 48 432))\n    (fun a environment => @prim_words_hash_spec 5 5 (BitcoinFull.Base Bitcoin.OutputScriptHash) raw_fullalg a environment)."
    ],
    [
      "Coq/C/jet_bitcoin_hash_raw_program.v",
      "statement",
      "bitcoin_input_values_hash_raw_program_local_spec",
      "Theorem bitcoin_input_values_hash_raw_program_local_spec :\n  application_jet_local_spec_sep f_simplicity_bitcoin_input_values_hash bitcoin_ge raw_bitcoin_environment\n    Ty.Unit Word256\n    (raw_env_rep (hash_getter_rep (fun e => words_hash_of 3 5 (input_values_of e)) 0 144 432))\n    (fun a environment => @prim_words_hash_spec 3 5 (BitcoinFull.Base Bitcoin.InputValue) raw_fullalg a environment)."
    ],
    [
      "Coq/C/jet_bitcoin_hash_raw_program.v",
      "statement",
      "bitcoin_input_scripts_hash_raw_program_local_spec",
      "Theorem bitcoin_input_scripts_hash_raw_program_local_spec :\n  application_jet_local_spec_sep f_simplicity_bitcoin_input_scripts_hash bitcoin_ge raw_bitcoin_environment\n    Ty.Unit Word256\n    (raw_env_rep (hash_getter_rep (fun e => words_hash_of 5 5 (input_scripts_of e)) 0 176 432))\n    (fun a environment => @prim_words_hash_spec 5 5 (BitcoinFull.Ext BitcoinExt.InputScriptHash) raw_fullalg a environment)."
    ],
    [
      "Coq/C/jet_bitcoin_hash_raw_program.v",
      "statement",
      "bitcoin_input_sequences_hash_raw_program_local_spec",
      "Theorem bitcoin_input_sequences_hash_raw_program_local_spec :\n  application_jet_local_spec_sep f_simplicity_bitcoin_input_sequences_hash bitcoin_ge raw_bitcoin_environment\n    Ty.Unit Word256\n    (raw_env_rep (hash_getter_rep (fun e => words_hash_of 2 5 (input_sequences_of e)) 0 240 432))\n    (fun a environment => @prim_words_hash_spec 2 5 (BitcoinFull.Base Bitcoin.InputSequence) raw_fullalg a environment)."
    ],
    [
      "Coq/C/jet_bitcoin_hash_raw_program.v",
      "statement",
      "bitcoin_input_script_sigs_hash_raw_program_local_spec",
      "Theorem bitcoin_input_script_sigs_hash_raw_program_local_spec :\n  application_jet_local_spec_sep f_simplicity_bitcoin_input_script_sigs_hash bitcoin_ge raw_bitcoin_environment\n    Ty.Unit Word256\n    (raw_env_rep (hash_getter_rep (fun e => words_hash_of 5 5 (input_script_sigs_of e)) 0 304 432))\n    (fun a environment => @prim_words_hash_spec 5 5 (BitcoinFull.Ext BitcoinExt.InputScriptSigHash) raw_fullalg a environment)."
    ],
    [
      "Coq/C/jet_bitcoin_hash_raw_program.v",
      "statement",
      "bitcoin_tappath_hash_raw_program_local_spec",
      "Theorem bitcoin_tappath_hash_raw_program_local_spec :\n  application_jet_local_spec_sep f_simplicity_bitcoin_tappath_hash bitcoin_ge raw_bitcoin_environment\n    Ty.Unit Word256\n    (raw_env_rep (hash_getter_rep (fun e => words_hash_of 5 3 (tappath_of e)) 8 40 176))\n    (fun a environment => @prim_words_hash_spec 5 3 (BitcoinFull.Ext BitcoinExt.Tappath) raw_fullalg a environment)."
    ],
    [
      "Coq/C/jet_bitcoin_hash_raw_program.v",
      "statement",
      "tapleaf_hash_literal_parametric",
      "Lemma tapleaf_hash_literal_parametric : PF.Parametric (@tapleaf_hash_literal_spec)."
    ],
    [
      "Coq/C/jet_bitcoin_hash_raw_program.v",
      "statement",
      "bitcoin_tapleaf_hash_raw_program_local_spec",
      "Theorem bitcoin_tapleaf_hash_raw_program_local_spec :\n  application_jet_local_spec_sep f_simplicity_bitcoin_tapleaf_hash bitcoin_ge raw_bitcoin_environment\n    Ty.Unit Word256 (raw_env_rep (hash_getter_rep tapleaf_hash_of 8 8 176))\n    (fun a environment => @tapleaf_hash_literal_spec raw_fullalg a environment)."
    ],
    [
      "Coq/C/jet_bitcoin_hash_raw_program.v",
      "statement",
      "bitcoin_outputs_hash_raw_program_local_spec",
      "Theorem bitcoin_outputs_hash_raw_program_local_spec :\n  application_jet_local_spec_sep f_simplicity_bitcoin_outputs_hash bitcoin_ge raw_bitcoin_environment\n    Ty.Unit Word256 (raw_env_rep (hash_getter_rep outputs_hash_of 0 80 432))\n    (fun a environment => @outputs_hash_spec raw_fullalg a environment)."
    ],
    [
      "Coq/C/jet_bitcoin_hash_raw_program.v",
      "statement",
      "bitcoin_input_utxos_hash_raw_program_local_spec",
      "Theorem bitcoin_input_utxos_hash_raw_program_local_spec :\n  application_jet_local_spec_sep f_simplicity_bitcoin_input_utxos_hash bitcoin_ge raw_bitcoin_environment\n    Ty.Unit Word256 (raw_env_rep (hash_getter_rep input_utxos_hash_of 0 208 432))\n    (fun a environment => @input_utxos_hash_spec raw_fullalg a environment)."
    ],
    [
      "Coq/C/jet_bitcoin_hash_raw_program.v",
      "statement",
      "bitcoin_tap_env_hash_raw_program_local_spec",
      "Theorem bitcoin_tap_env_hash_raw_program_local_spec :\n  application_jet_local_spec_sep f_simplicity_bitcoin_tap_env_hash bitcoin_ge raw_bitcoin_environment\n    Ty.Unit Word256 (raw_env_rep (hash_getter_rep tap_env_hash_of 8 72 176))\n    (fun a environment => @tap_env_hash_spec raw_fullalg a environment)."
    ],
    [
      "Coq/C/jet_bitcoin_hash_raw_program.v",
      "statement",
      "bitcoin_input_outpoints_hash_raw_program_local_spec",
      "Theorem bitcoin_input_outpoints_hash_raw_program_local_spec :\n  application_jet_local_spec_sep f_simplicity_bitcoin_input_outpoints_hash bitcoin_ge raw_bitcoin_environment\n    Ty.Unit Word256 (raw_env_rep (hash_getter_rep input_outpoints_hash_of 0 112 432))\n    (fun a environment => @input_outpoints_hash_spec raw_fullalg a environment)."
    ],
    [
      "Coq/C/jet_bitcoin_hash_raw_program.v",
      "statement",
      "bitcoin_input_annexes_hash_raw_program_local_spec",
      "Theorem bitcoin_input_annexes_hash_raw_program_local_spec :\n  application_jet_local_spec_sep f_simplicity_bitcoin_input_annexes_hash bitcoin_ge raw_bitcoin_environment\n    Ty.Unit Word256 (raw_env_rep (hash_getter_rep input_annexes_hash_of 0 272 432))\n    (fun a environment => @input_annexes_hash_spec raw_fullalg a environment)."
    ],
    [
      "Coq/C/jet_bitcoin_hash_raw_program.v",
      "statement",
      "bitcoin_inputs_hash_raw_program_local_spec",
      "Theorem bitcoin_inputs_hash_raw_program_local_spec :\n  application_jet_local_spec_sep f_simplicity_bitcoin_inputs_hash bitcoin_ge raw_bitcoin_environment\n    Ty.Unit Word256 (raw_env_rep (hash_getter_rep inputs_hash_of 0 336 432))\n    (fun a environment => @inputs_hash_spec raw_fullalg a environment)."
    ],
    [
      "Coq/C/jet_bitcoin_hash_raw_program.v",
      "statement",
      "bitcoin_tx_hash_raw_program_local_spec",
      "Theorem bitcoin_tx_hash_raw_program_local_spec :\n  application_jet_local_spec_sep f_simplicity_bitcoin_tx_hash bitcoin_ge raw_bitcoin_environment\n    Ty.Unit Word256 (raw_env_rep (hash_getter_rep tx_hash_of 0 368 432))\n    (fun a environment => @tx_hash_spec raw_fullalg a environment)."
    ],
    [
      "Coq/C/jet_bitcoin_hash_raw_program.v",
      "statement",
      "bitcoin_sig_all_hash_raw_program_local_spec",
      "Theorem bitcoin_sig_all_hash_raw_program_local_spec :\n  application_jet_local_spec_sep f_simplicity_bitcoin_sig_all_hash bitcoin_ge raw_bitcoin_environment\n    Ty.Unit Word256 (raw_env_rep (env_hash_rep sig_all_hash_of 16))\n    (fun a environment => @sig_all_hash_spec raw_fullalg a environment)."
    ],
    [
      "Coq/C/jet_bitcoin_words_hash.v",
      "declaration",
      "prim_words_hash_spec",
      "Definition prim_words_hash_spec (k w : nat)\n    (p : BitcoinFull.t (Word w) (Ty.Sum Ty.Unit (Vector (Word 3) k))) {alg : PF.Algebra} :\n    PF.domain alg Ty.Unit Word256 :=\n  let term := PF.CanonicalStructures.toAssertion alg in\n  let core := Alg.Assertion.toCore term in\n  @hash_words_spec k w term Ty.Unit\n    (@AC.drop Ty.Unit (Word w) _ core (@PF.Combinators.prim _ _ alg p))."
    ],
    [
      "Coq/C/jet_bitcoin_words_hash.v",
      "declaration",
      "words_hash_of",
      "Definition words_hash_of (k w : nat) (xs : list (Ty.tySem (Vector (Word 3) k))) : hash256 :=\n  hash_words_of k (firstn (Z.to_nat (wsize w)) xs)."
    ],
    [
      "Coq/C/jet_bitcoin_words_hash.v",
      "declaration",
      "output_values_of",
      "Definition output_values_of (e : ext_environment) : list (Ty.tySem (Vector (Word 3) 3)) :=\n  map (fun o => @fromZ (WordToZ 6) (Int64.signed (txoValue o)))\n    (sigTxOut (Bitcoin.envTx (extBase e)))."
    ],
    [
      "Coq/C/jet_bitcoin_words_hash.v",
      "declaration",
      "output_scripts_of",
      "Definition output_scripts_of (e : ext_environment) : list (Ty.tySem (Vector (Word 3) 5)) :=\n  map (fun x => from_hash256 (byteStringHash (txoScript x))) (sigTxOut (Bitcoin.envTx (extBase e)))."
    ],
    [
      "Coq/C/jet_bitcoin_words_hash.v",
      "declaration",
      "input_values_of",
      "Definition input_values_of (e : ext_environment) : list (Ty.tySem (Vector (Word 3) 3)) :=\n  map (fun x => @fromZ (WordToZ 6) (Int64.signed (sigTxiValue x))) (sigTxIn (Bitcoin.envTx (extBase e)))."
    ],
    [
      "Coq/C/jet_bitcoin_words_hash.v",
      "declaration",
      "input_scripts_of",
      "Definition input_scripts_of (e : ext_environment) : list (Ty.tySem (Vector (Word 3) 5)) :=\n  map (fun x => from_hash256 x) (extInScriptHash e)."
    ],
    [
      "Coq/C/jet_bitcoin_words_hash.v",
      "declaration",
      "input_sequences_of",
      "Definition input_sequences_of (e : ext_environment) : list (Ty.tySem (Vector (Word 3) 2)) :=\n  map (fun x => @fromZ (WordToZ 5) (Int.unsigned (sigTxiSequence x))) (sigTxIn (Bitcoin.envTx (extBase e)))."
    ],
    [
      "Coq/C/jet_bitcoin_words_hash.v",
      "declaration",
      "input_script_sigs_of",
      "Definition input_script_sigs_of (e : ext_environment) : list (Ty.tySem (Vector (Word 3) 5)) :=\n  map (fun x => from_hash256 x) (extInScriptSigHash e)."
    ],
    [
      "Coq/C/jet_bitcoin_words_hash.v",
      "declaration",
      "tappath_of",
      "Definition tappath_of (e : ext_environment) : list (Ty.tySem (Vector (Word 3) 5)) :=\n  map (fun x => from_hash256 x) (extTappath e)."
    ],
    [
      "Coq/C/jet_sha_hash_words.v",
      "declaration",
      "hash_words_spec",
      "Definition hash_words_spec (k w : nat) {term : Alg.Assertion.Algebra} {C : Ty}\n    (array : @Alg.Assertion.domain term (Ty.Prod C (Word w)) (Ty.Sum Ty.Unit (Vector (Word 3) k))) :\n    @Alg.Assertion.domain term C Word256 :=\n  let core := Alg.Assertion.toCore term in\n  @AC.comp _ _ _ core\n    (@AC.pair _ _ _ core (@AC.iden _ core)\n      (@AC.comp _ _ _ core (@AC.unit _ core) (@sha256_ctx8_init_spec core)))\n    (@AC.comp _ _ _ core (@hash_loop_spec k w term C array) (@ctx8_finalize_spec term))."
    ],
    [
      "Coq/C/jet_sha_hash_words.v",
      "declaration",
      "hash_words_of",
      "Definition hash_words_of (k : nat) (items : list (Ty.tySem (Vector (Word 3) k))) : hash256 :=\n  mk_hash256 (sha_stream [] sha256_iv_words 0 (loop_bytes k items))."
    ],
    [
      "Coq/C/jet_sha_hash_loop.v",
      "declaration",
      "hash_loop_body",
      "Definition hash_loop_body (k : nat) {term : Alg.Assertion.Algebra} {C W : Ty}\n    (array : @Alg.Assertion.domain term (Ty.Prod C W) (Ty.Sum Ty.Unit (Vector (Word 3) k))) :\n    @Alg.Assertion.domain term (Ty.Prod (Ty.Prod C W) sha256_ctx8_type)\n      (Ty.Sum sha256_ctx8_type sha256_ctx8_type) :=\n  let core := Alg.Assertion.toCore term in\n  @AC.comp _ _ _ core\n    (@AC.pair _ _ _ core (@AC.take _ _ _ core array) (@AC.drop _ _ _ core (@AC.iden _ core)))\n    (@AC.case _ _ _ _ core (@AC.injl _ _ _ core (@AC.drop _ _ _ core (@AC.iden _ core)))\n      (@AC.injr _ _ _ core (@AC.comp _ _ _ core\n        (@AC.pair _ _ _ core (@AC.drop _ _ _ core (@AC.iden _ core)) (@AC.take _ _ _ core (@AC.iden _ core)))\n        (@ctx8_addn_spec k term))))."
    ],
    [
      "Coq/C/jet_sha_hash_loop.v",
      "declaration",
      "hash_loop_spec",
      "Definition hash_loop_spec (k w : nat) {term : Alg.Assertion.Algebra} {C : Ty}\n    (array : @Alg.Assertion.domain term (Ty.Prod C (Word w)) (Ty.Sum Ty.Unit (Vector (Word 3) k))) :\n    @Alg.Assertion.domain term (Ty.Prod C sha256_ctx8_type) sha256_ctx8_type :=\n  let core := Alg.Assertion.toCore term in\n  @AC.comp _ _ _ core (@for_while_program w _ _ _ core (hash_loop_body k array))\n    (@AC.copair _ _ _ core (@AC.iden _ core) (@AC.iden _ core))."
    ],
    [
      "Coq/C/jet_sha_hash_loop.v",
      "declaration",
      "loop_bytes",
      "Definition loop_bytes (l : list (Ty.tySem (Vector (Word 3) k))) : list (Ty.tySem (Word 3)) :=\n  concat (map (vector_values (Word 3) k) l)."
    ],
    [
      "Coq/C/jet_sha_hash_loop_gen.v",
      "declaration",
      "gen_loop_body",
      "Definition gen_loop_body {term : Alg.Assertion.Algebra} {C W : Ty}\n    (array : @Alg.Assertion.domain term (Ty.Prod C W) (Ty.Sum Ty.Unit X)) :\n    @Alg.Assertion.domain term (Ty.Prod (Ty.Prod C W) sha256_ctx8_type)\n      (Ty.Sum sha256_ctx8_type sha256_ctx8_type) :=\n  let core := Alg.Assertion.toCore term in\n  @AC.comp _ _ _ core\n    (@AC.pair _ _ _ core (@AC.take _ _ _ core array) (@AC.drop _ _ _ core (@AC.iden _ core)))\n    (@AC.case _ _ _ _ core (@AC.injl _ _ _ core (@AC.drop _ _ _ core (@AC.iden _ core)))\n      (@AC.injr _ _ _ core (@AC.comp _ _ _ core\n        (@AC.pair _ _ _ core (@AC.drop _ _ _ core (@AC.iden _ core)) (@AC.take _ _ _ core (@AC.iden _ core)))\n        (add term))))."
    ],
    [
      "Coq/C/jet_sha_hash_loop_gen.v",
      "declaration",
      "gen_loop_run",
      "Definition gen_loop_run (w : nat) {term : Alg.Assertion.Algebra} {C : Ty}\n    (array : @Alg.Assertion.domain term (Ty.Prod C (Word w)) (Ty.Sum Ty.Unit X)) :\n    @Alg.Assertion.domain term (Ty.Prod C sha256_ctx8_type) (Ty.Sum sha256_ctx8_type sha256_ctx8_type) :=\n  @for_while_program w _ _ _ (Alg.Assertion.toCore term) (gen_loop_body array)."
    ],
    [
      "Coq/C/jet_forWhile_spec.v",
      "declaration",
      "for_while_program",
      "Fixpoint for_while_program (n : nat) {C B A : Ty} {alg : Core.Algebra}\n    (body : alg ((C * Word n) * A) (B + A)) : alg (C * A) (B + A) :=\n  match n as k return alg ((C * Word k) * A) (B + A) -> alg (C * A) (B + A) with\n  | 0 => fun body =>\n      ((((O H &&& Bit.false) &&& I H) >>> body) &&& O H) >>>\n        case (injl (O H)) (((I H &&& Bit.true) &&& O H) >>> body)\n  | S k => fun body =>\n      for_while_program k (for_while_program k\n        (((O O O H &&& (O O I H &&& O I H)) &&& I H) >>> body))\n  end body."
    ],
    [
      "Coq/C/jet_bitcoin_ctx_hash_spec.v",
      "declaration",
      "outpoint_hash_spec",
      "Definition outpoint_hash_spec {term : Alg.Assertion.Algebra} :\n    @Alg.Assertion.domain term (Ty.Prod sha256_ctx8_type (Ty.Prod (Word 8) (Word 5))) sha256_ctx8_type :=\n  @AC.comp _ _ _ (Alg.Assertion.toCore term)\n    (@AC.pair _ _ _ (Alg.Assertion.toCore term)\n      (@AC.comp _ _ _ (Alg.Assertion.toCore term)\n        (AC.pair (AC.take AC.iden) (AC.drop (AC.take AC.iden))) (@ctx8_addn_spec 5 term))\n      (AC.drop (AC.drop AC.iden)))\n    (@ctx8_addn_spec 2 term)."
    ],
    [
      "Coq/C/jet_bitcoin_ctx_hash_spec.v",
      "declaration",
      "annex_hash_spec",
      "Definition annex_hash_spec {term : Alg.Assertion.Algebra} :\n    @Alg.Assertion.domain term (Ty.Prod sha256_ctx8_type (Ty.Sum Ty.Unit (Word 8))) sha256_ctx8_type :=\n  @AC.comp _ _ _ (Alg.Assertion.toCore term) (AC.pair (AC.drop AC.iden) (AC.take AC.iden))\n    (@AC.case _ _ _ _ (Alg.Assertion.toCore term)\n      (@AC.comp _ _ _ (Alg.Assertion.toCore term)\n        (AC.pair (AC.drop AC.iden) (AC.take (@Word.zero 3 (Alg.Assertion.toCore term))))\n        (@ctx8_add1_spec term))\n      (@AC.comp _ _ _ (Alg.Assertion.toCore term)\n        (@AC.pair _ _ _ (Alg.Assertion.toCore term)\n          (@AC.comp _ _ _ (Alg.Assertion.toCore term)\n            (AC.pair (AC.drop AC.iden) (AC.comp AC.unit (Alg.scribe byte_one)))\n            (@ctx8_add1_spec term))\n          (AC.take AC.iden))\n        (@ctx8_addn_spec 5 term)))."
    ],
    [
      "Coq/C/jet_bitcoin_ctx_hash_spec.v",
      "declaration",
      "byte_one",
      "Definition byte_one : Ty.tySem (Word 3) := @fromZ (WordToZ 3) 1."
    ],
    [
      "Coq/C/jet_bitcoin_composite_hash.v",
      "declaration",
      "pair_hash_spec",
      "Definition pair_hash_spec {alg : PF.Algebra} (s t : PF.domain alg Ty.Unit Word256) :\n    PF.domain alg Ty.Unit Word256 :=\n  let term := PF.CanonicalStructures.toAssertion alg in\n  let core := Alg.Assertion.toCore term in\n  @AC.comp _ _ _ core\n    (@AC.pair _ _ _ core (@sha256_ctx8_init_spec core) (@AC.pair _ _ _ core s t))\n    (@AC.comp _ _ _ core (@ctx8_addn_spec 6 term) (@ctx8_finalize_spec term))."
    ],
    [
      "Coq/C/jet_bitcoin_composite_hash.v",
      "declaration",
      "outputs_hash_spec",
      "Definition outputs_hash_spec {alg : PF.Algebra} : PF.domain alg Ty.Unit Word256 :=\n  @pair_hash_spec alg\n    (@prim_words_hash_spec 3 5 (BitcoinFull.Base Bitcoin.OutputValue) alg)\n    (@prim_words_hash_spec 5 5 (BitcoinFull.Base Bitcoin.OutputScriptHash) alg)."
    ],
    [
      "Coq/C/jet_bitcoin_composite_hash.v",
      "declaration",
      "input_utxos_hash_spec",
      "Definition input_utxos_hash_spec {alg : PF.Algebra} : PF.domain alg Ty.Unit Word256 :=\n  @pair_hash_spec alg\n    (@prim_words_hash_spec 3 5 (BitcoinFull.Base Bitcoin.InputValue) alg)\n    (@prim_words_hash_spec 5 5 (BitcoinFull.Ext BitcoinExt.InputScriptHash) alg)."
    ],
    [
      "Coq/C/jet_bitcoin_composite_hash.v",
      "declaration",
      "tap_env_hash_spec",
      "Definition tap_env_hash_spec {alg : PF.Algebra} : PF.domain alg Ty.Unit Word256 :=\n  let term := PF.CanonicalStructures.toAssertion alg in\n  let core := Alg.Assertion.toCore term in\n  @AC.comp _ _ _ core\n    (@AC.pair _ _ _ core\n      (@AC.comp _ _ _ core\n        (@AC.pair _ _ _ core (@sha256_ctx8_init_spec core) (@tapleaf_hash_spec alg))\n        (@ctx8_addn_spec 5 term))\n      (@AC.pair _ _ _ core\n        (@prim_words_hash_spec 5 3 (BitcoinFull.Ext BitcoinExt.Tappath) alg)\n        (@PF.Combinators.prim _ _ alg (BitcoinFull.Ext BitcoinExt.InternalKey))))\n    (@AC.comp _ _ _ core (@ctx8_addn_spec 6 term) (@ctx8_finalize_spec term))."
    ],
    [
      "Coq/C/jet_bitcoin_tx_hash.v",
      "declaration",
      "elems_hash_spec",
      "Definition elems_hash_spec {alg : PF.Algebra} : PF.domain alg Ty.Unit Word256 :=\n  let term := PF.CanonicalStructures.toAssertion alg in\n  let core := Alg.Assertion.toCore term in\n  @AC.comp _ _ _ core\n    (@AC.pair _ _ _ core (@AC.unit _ core) (@sha256_ctx8_init_spec core))\n    (@AC.comp _ _ _ core\n      (@gen_loop_run X add w term Ty.Unit\n        (@AC.drop Ty.Unit (Word w) _ core (@PF.Combinators.prim _ _ alg p)))\n      (@AC.copair _ _ _ core (@ctx8_finalize_spec term) (@ctx8_finalize_spec term)))."
    ],
    [
      "Coq/C/jet_bitcoin_tx_hash.v",
      "declaration",
      "input_outpoints_hash_spec",
      "Definition input_outpoints_hash_spec {alg : PF.Algebra} : PF.domain alg Ty.Unit Word256 :=\n  @elems_hash_spec (Ty.Prod (Word 8) (Word 5)) (fun term => @outpoint_hash_spec term) 5\n    (BitcoinFull.Base Bitcoin.InputPrevOutpoint) alg."
    ],
    [
      "Coq/C/jet_bitcoin_tx_hash.v",
      "declaration",
      "input_annexes_hash_spec",
      "Definition input_annexes_hash_spec {alg : PF.Algebra} : PF.domain alg Ty.Unit Word256 :=\n  @elems_hash_spec (Ty.Sum Ty.Unit (Word 8)) (fun term => @annex_hash_spec term) 5\n    (BitcoinFull.Ext BitcoinExt.InputAnnexHash) alg."
    ],
    [
      "Coq/C/jet_bitcoin_tx_hash.v",
      "declaration",
      "inputs_hash_spec",
      "Definition inputs_hash_spec {alg : PF.Algebra} : PF.domain alg Ty.Unit Word256 :=\n  let term := PF.CanonicalStructures.toAssertion alg in\n  let core := Alg.Assertion.toCore term in\n  @AC.comp _ _ _ core\n    (@AC.pair _ _ _ core\n      (@AC.comp _ _ _ core\n        (@AC.pair _ _ _ core (@sha256_ctx8_init_spec core)\n          (@AC.pair _ _ _ core (@input_outpoints_hash_spec alg)\n            (@prim_words_hash_spec 2 5 (BitcoinFull.Base Bitcoin.InputSequence) alg)))\n        (@ctx8_addn_spec 6 term))\n      (@input_annexes_hash_spec alg))\n    (@AC.comp _ _ _ core (@ctx8_addn_spec 5 term) (@ctx8_finalize_spec term))."
    ],
    [
      "Coq/C/jet_bitcoin_tx_hash.v",
      "declaration",
      "tx_hash_spec",
      "Definition tx_hash_spec {alg : PF.Algebra} : PF.domain alg Ty.Unit Word256 :=\n  let term := PF.CanonicalStructures.toAssertion alg in\n  let core := Alg.Assertion.toCore term in\n  @AC.comp _ _ _ core\n    (@AC.pair _ _ _ core\n      (@AC.comp _ _ _ core\n        (@AC.pair _ _ _ core\n          (@AC.comp _ _ _ core\n            (@AC.pair _ _ _ core (@sha256_ctx8_init_spec core)\n              (@AC.pair _ _ _ core\n                (@PF.Combinators.prim _ _ alg (BitcoinFull.Base Bitcoin.Version))\n                (@PF.Combinators.prim _ _ alg (BitcoinFull.Base Bitcoin.LockTime))))\n            (@ctx8_addn_spec 3 term))\n          (@AC.pair _ _ _ core (@inputs_hash_spec alg) (@outputs_hash_spec alg)))\n        (@ctx8_addn_spec 6 term))\n      (@input_utxos_hash_spec alg))\n    (@AC.comp _ _ _ core (@ctx8_addn_spec 5 term) (@ctx8_finalize_spec term))."
    ],
    [
      "Coq/C/jet_bitcoin_sig_all_hash.v",
      "declaration",
      "sig_all_hash_spec",
      "Definition sig_all_hash_spec {alg : PF.Algebra} : PF.domain alg Ty.Unit Word256 :=\n  let term := PF.CanonicalStructures.toAssertion alg in\n  let core := Alg.Assertion.toCore term in\n  @AC.comp _ _ _ core\n    (@AC.pair _ _ _ core\n      (@AC.comp _ _ _ core\n        (@AC.pair _ _ _ core (@sha256_ctx8_init_spec core)\n          (@AC.pair _ _ _ core (@tx_hash_spec alg) (@tap_env_hash_spec alg)))\n        (@ctx8_addn_spec 6 term))\n      (@PF.Combinators.prim _ _ alg (BitcoinFull.Base Bitcoin.CurrentIndex)))\n    (@AC.comp _ _ _ core (@ctx8_addn_spec 2 term) (@ctx8_finalize_spec term))."
    ],
    [
      "Coq/C/jet_bitcoin_sig_all_hash.v",
      "declaration",
      "env_hash_rep",
      "Definition env_hash_rep {E : Set} (hash_of : E -> hash256) (hdelta : Z)\n    (m : mem) (env : val) (e : E) (fp : list (block * Z * Z)) : Prop :=\n  exists be ebase,\n    env = Vptr be (Ptrofs.repr ebase) /\\\n    0 <= ebase /\\ ebase + 56 <= Ptrofs.max_unsigned /\\\n    uint32_array_at m be (ebase + hdelta) (hash256_reg (hash_of e)) /\\\n    fp = [(be, ebase + hdelta, ebase + hdelta + 32)]."
    ],
    [
      "Coq/C/jet_bitcoin_raw_env.v",
      "declaration",
      "raw_input_data",
      "Record raw_input_data :=\n{ raw_redeemed_script : list byte\n; raw_annex : option (list byte)\n; raw_script_sig : list byte\n}."
    ],
    [
      "Coq/C/jet_bitcoin_raw_env.v",
      "declaration",
      "raw_bitcoin_environment",
      "Record raw_bitcoin_environment :=\n{ raw_base : Bitcoin.environment\n; raw_inputs : list raw_input_data\n; raw_inputs_length : length raw_inputs = length (sigTxIn (Bitcoin.envTx raw_base))\n; raw_leaf_version : byte\n; raw_tap_path : list hash256\n; raw_internal_key : hash256\n}."
    ],
    [
      "Coq/C/jet_bitcoin_raw_env.v",
      "declaration",
      "raw_ext_sem",
      "Definition raw_ext_sem {A B} (p : BitcoinExt.t A B) (a : Ty.tySem A)\n    (environment : raw_bitcoin_environment) : option (Ty.tySem B) :=\n  let cast {C : Ty} (x : option (Ty.tySem C)) : Ty.tySem (Ty.Sum Ty.Unit C) :=\n    match x with Some c => inr c | None => inl tt end in\n  (match p in BitcoinExt.prim A B return Ty.tySem A -> option (Ty.tySem B) with\n   | BitcoinExt.CurrentIndex => fun _ =>\n       Some (fromZ (Z.of_nat (Bitcoin.envIx (raw_base environment))))\n   | BitcoinExt.InputScriptHash => fun i =>\n       Some (cast (option_map (fun data => from_hash256 (byteStringHash (raw_redeemed_script data)))\n         (nth_error (raw_inputs environment) (Z.to_nat (toZ i)))))\n   | BitcoinExt.InputAnnexHash => fun i =>\n       Some (match nth_error (raw_inputs environment) (Z.to_nat (toZ i)) with\n             | None => inl tt\n             | Some data => inr (cast (option_map (fun bytes => from_hash256 (byteStringHash bytes)) (raw_annex data)))\n             end)\n   | BitcoinExt.InputScriptSigHash => fun i =>\n       Some (cast (option_map (fun data => from_hash256 (byteStringHash (raw_script_sig data)))\n         (nth_error (raw_inputs environment) (Z.to_nat (toZ i)))))\n   | BitcoinExt.TapleafVersion => fun _ => Some (fromZ (Byte.unsigned (raw_leaf_version environment)))\n   | BitcoinExt.Tappath => fun i =>\n       Some (cast (option_map from_hash256 (nth_error (raw_tap_path environment) (Z.to_nat (toZ i)))))\n   | BitcoinExt.InternalKey => fun _ => Some (from_hash256 (raw_internal_key environment))\n   | BitcoinExt.TransactionId => fun _ => Some (from_hash256 (raw_transaction_id environment))\n   end) a."
    ],
    [
      "Coq/C/jet_bitcoin_raw_jets.v",
      "declaration",
      "raw_env_rep",
      "Definition raw_env_rep\n    (rep : Mem.mem -> val -> ext_environment -> list (block * Z * Z) -> Prop)\n    (m : Mem.mem) (env : val) (logical : raw_bitcoin_environment)\n    (fp : list (block * Z * Z)) : Prop :=\n  exists Hpath : (length (raw_tap_path logical) <= 128)%nat,\n    rep m env (project_raw_environment logical Hpath) fp."
    ],
    [
      "Coq/Simplicity/Primitive/Bitcoin.v",
      "declaration",
      "environment",
      "Record environment :=\n{ envTx : sigTx\n; envIx : nat\n; envScriptCMR : hash256\n; envIxBounded : envIx < length (sigTxIn envTx)\n}."
    ],
    [
      "Coq/Simplicity/Primitive/Bitcoin.v",
      "declaration",
      "sem",
      "Definition sem {A B} (p : t A B) (a : A) (e : env) : option B :=\nlet tx := envTx e in\nlet ix := envIx e in\nlet currentInput {A : Ty} (f : sigTxInput -> A) := option_map f (nth_error (sigTxIn tx) ix) in\nlet atInput {A : Ty} (f : sigTxInput -> A) (i : Word32) :=\n  Some (cast (option_map f (nth_error (sigTxIn tx) (Z.to_nat (toZ i))))) in\nlet atOutput {A : Ty} (f : txOutput -> A) (i : Word32) :=\n  Some (cast (option_map f (nth_error (sigTxOut tx) (Z.to_nat (toZ i))))) in\nlet outputsHash :=\n  let go i := putInt64le (txoValue i) ++ putHash256 (byteStringHash (txoScript i)) in\n  byteStringHash (concat (map go (sigTxOut tx))) in\nlet inputsHash :=\n  let go i := putOutpoint (sigTxiPreviousOutpoint i) ++ putInt64le (sigTxiValue i) ++ putInt32le (sigTxiSequence i) in\n  byteStringHash (concat (map go (sigTxIn tx))) in\n(match p in prim A B return A -> option B with\n | Version => fun _ => Some (fromZ (Int.signed (sigTxVersion tx)))\n | LockTime => fun _ => Some (fromZ (Int.unsigned (sigTxLock tx)))\n | InputsHash => fun _ => Some (from_hash256 inputsHash)\n | OutputsHash => fun _ => Some (from_hash256 outputsHash)\n | NumInputs => fun _ => Some (fromZ (Zlength (sigTxIn tx)))\n | TotalInputValue => fun _ => Some (fromZ (sigTxTotalInValue tx))\n | CurrentPrevOutpoint => fun _ => currentInput (fun txi => encodeOutpoint (sigTxiPreviousOutpoint txi))\n | CurrentValue => fun _ => currentInput (fun txi => fromZ (Int64.signed (sigTxiValue txi)))\n | CurrentSequence => fun _ => currentInput (fun txi => fromZ (Int.unsigned (sigTxiSequence txi)))\n | CurrentIndex => fun _ => Some (fromZ (Z.of_nat ix))\n | InputPrevOutpoint => atInput (fun txi => encodeOutpoint (sigTxiPreviousOutpoint txi))\n | InputValue => atInput (fun txi => fromZ (Int64.signed (sigTxiValue txi)))\n | InputSequence => atInput (fun txi => fromZ (Int.unsigned (sigTxiSequence txi)))\n | NumOutputs => fun _ => Some (fromZ (Zlength (sigTxOut tx)))\n | TotalOutputValue => fun _ => Some (fromZ (sigTxTotalOutValue tx))\n | OutputValue => atOutput (fun txout => fromZ (Int64.signed (txoValue txout)))\n | OutputScriptHash => atOutput (fun txout => from_hash256 (byteStringHash (txoScript txout)))\n | ScriptCMR => fun _ => Some (from_hash256 (envScriptCMR e))\n end\n) a."
    ],
    [
      "Coq/C/jet_elements_tap_getters_literal.v",
      "declaration",
      "haskell_encode_pubkey",
      "Definition haskell_encode_pubkey (h : hash256) : tySem Word256 :=\n  haskell_to_word 8 (haskell_word256_integer\n    (haskell_be256_run (hash256_to_bytelist h) (haskell_word256_from_integer 0)))."
    ],
    [
      "Coq/C/jet_bitcoin_raw_env.v",
      "proof_definition",
      "project_raw_environment",
      "Definition project_raw_environment (environment : raw_bitcoin_environment)\n    (Hpath : (length (raw_tap_path environment) <= 128)%nat) : ext_environment.\nProof.\n  refine {| extBase := raw_base environment;\n    extInScriptHash := map (fun i => byteStringHash (raw_redeemed_script i)) (raw_inputs environment);\n    extInAnnexHash := map (fun i => option_map byteStringHash (raw_annex i)) (raw_inputs environment);\n    extInScriptSigHash := map (fun i => byteStringHash (raw_script_sig i)) (raw_inputs environment);\n    extTapleafVersion := Byte.unsigned (raw_leaf_version environment);\n    extTappath := raw_tap_path environment;\n    extInternalKey := raw_internal_key environment;\n    extTxid := raw_transaction_id environment;\n    extTappath_len := Hpath |}.\n  - rewrite map_length. exact (raw_inputs_length environment).\n  - rewrite map_length. exact (raw_inputs_length environment).\n  - rewrite map_length. exact (raw_inputs_length environment).\n  - exact (Byte.unsigned_range (raw_leaf_version environment)).\nDefined."
    ],
    [
      "Coq/C/jet_bitcoin_input_value_spec.v",
      "statement",
      "word64_signed_unsigned",
      "Lemma word64_signed_unsigned v :\n  @fromZ (WordToZ 6) (Int64.signed v) =\n  @fromZ (WordToZ 6) (Int64.unsigned v)."
    ],
    [
      "Coq/C/jet_bitcoin_version_spec.v",
      "statement",
      "bitcoin_version_word_signed_unsigned",
      "Lemma bitcoin_version_word_signed_unsigned (version : Int.int) :\n  @fromZ (WordToZ 5) (Int.unsigned version) = @fromZ (WordToZ 5) (Int.signed version)."
    ],
    [
      "Coq/C/jet_elements_tap_getters_literal.v",
      "statement",
      "haskell_encode_pubkey_matches",
      "Lemma haskell_encode_pubkey_matches h : haskell_encode_pubkey h = from_hash256 h."
    ],
    [
      "Coq/C/jet_bitcoin_words_hash.v",
      "statement",
      "bitcoin_output_values_hash_local_spec",
      "Theorem bitcoin_output_values_hash_local_spec :\n  application_jet_local_spec_sep f_simplicity_bitcoin_output_values_hash bitcoin_ge ext_environment\n    Ty.Unit Word256\n    (hash_getter_rep (fun e => words_hash_of 3 5 (output_values_of e)) 0 16 432)\n    (fun a environment =>\n      @prim_words_hash_spec 3 5 (BitcoinFull.Base Bitcoin.OutputValue) fullalg a environment)."
    ],
    [
      "Coq/C/jet_bitcoin_words_hash.v",
      "statement",
      "bitcoin_output_scripts_hash_local_spec",
      "Theorem bitcoin_output_scripts_hash_local_spec :\n  application_jet_local_spec_sep f_simplicity_bitcoin_output_scripts_hash bitcoin_ge ext_environment\n    Ty.Unit Word256\n    (hash_getter_rep (fun e => words_hash_of 5 5 (output_scripts_of e)) 0 48 432)\n    (fun a environment =>\n      @prim_words_hash_spec 5 5 (BitcoinFull.Base Bitcoin.OutputScriptHash) fullalg a environment)."
    ],
    [
      "Coq/C/jet_bitcoin_words_hash.v",
      "statement",
      "bitcoin_input_values_hash_local_spec",
      "Theorem bitcoin_input_values_hash_local_spec :\n  application_jet_local_spec_sep f_simplicity_bitcoin_input_values_hash bitcoin_ge ext_environment\n    Ty.Unit Word256\n    (hash_getter_rep (fun e => words_hash_of 3 5 (input_values_of e)) 0 144 432)\n    (fun a environment =>\n      @prim_words_hash_spec 3 5 (BitcoinFull.Base Bitcoin.InputValue) fullalg a environment)."
    ],
    [
      "Coq/C/jet_bitcoin_words_hash.v",
      "statement",
      "bitcoin_input_scripts_hash_local_spec",
      "Theorem bitcoin_input_scripts_hash_local_spec :\n  application_jet_local_spec_sep f_simplicity_bitcoin_input_scripts_hash bitcoin_ge ext_environment\n    Ty.Unit Word256\n    (hash_getter_rep (fun e => words_hash_of 5 5 (input_scripts_of e)) 0 176 432)\n    (fun a environment =>\n      @prim_words_hash_spec 5 5 (BitcoinFull.Ext BitcoinExt.InputScriptHash) fullalg a environment)."
    ],
    [
      "Coq/C/jet_bitcoin_words_hash.v",
      "statement",
      "bitcoin_input_sequences_hash_local_spec",
      "Theorem bitcoin_input_sequences_hash_local_spec :\n  application_jet_local_spec_sep f_simplicity_bitcoin_input_sequences_hash bitcoin_ge ext_environment\n    Ty.Unit Word256\n    (hash_getter_rep (fun e => words_hash_of 2 5 (input_sequences_of e)) 0 240 432)\n    (fun a environment =>\n      @prim_words_hash_spec 2 5 (BitcoinFull.Base Bitcoin.InputSequence) fullalg a environment)."
    ],
    [
      "Coq/C/jet_bitcoin_words_hash.v",
      "statement",
      "bitcoin_input_script_sigs_hash_local_spec",
      "Theorem bitcoin_input_script_sigs_hash_local_spec :\n  application_jet_local_spec_sep f_simplicity_bitcoin_input_script_sigs_hash bitcoin_ge ext_environment\n    Ty.Unit Word256\n    (hash_getter_rep (fun e => words_hash_of 5 5 (input_script_sigs_of e)) 0 304 432)\n    (fun a environment =>\n      @prim_words_hash_spec 5 5 (BitcoinFull.Ext BitcoinExt.InputScriptSigHash) fullalg a environment)."
    ],
    [
      "Coq/C/jet_bitcoin_words_hash.v",
      "statement",
      "bitcoin_tappath_hash_local_spec",
      "Theorem bitcoin_tappath_hash_local_spec :\n  application_jet_local_spec_sep f_simplicity_bitcoin_tappath_hash bitcoin_ge ext_environment\n    Ty.Unit Word256\n    (hash_getter_rep (fun e => words_hash_of 5 3 (tappath_of e)) 8 40 176)\n    (fun a environment =>\n      @prim_words_hash_spec 5 3 (BitcoinFull.Ext BitcoinExt.Tappath) fullalg a environment)."
    ],
    [
      "Coq/C/jet_bitcoin_composite_hash.v",
      "statement",
      "bitcoin_outputs_hash_local_spec",
      "Theorem bitcoin_outputs_hash_local_spec :\n  application_jet_local_spec_sep f_simplicity_bitcoin_outputs_hash bitcoin_ge ext_environment\n    Ty.Unit Word256 (hash_getter_rep outputs_hash_of 0 80 432)\n    (fun a environment => @outputs_hash_spec fullalg a environment)."
    ],
    [
      "Coq/C/jet_bitcoin_composite_hash.v",
      "statement",
      "bitcoin_input_utxos_hash_local_spec",
      "Theorem bitcoin_input_utxos_hash_local_spec :\n  application_jet_local_spec_sep f_simplicity_bitcoin_input_utxos_hash bitcoin_ge ext_environment\n    Ty.Unit Word256 (hash_getter_rep input_utxos_hash_of 0 208 432)\n    (fun a environment => @input_utxos_hash_spec fullalg a environment)."
    ],
    [
      "Coq/C/jet_bitcoin_composite_hash.v",
      "statement",
      "bitcoin_tap_env_hash_local_spec",
      "Theorem bitcoin_tap_env_hash_local_spec :\n  application_jet_local_spec_sep f_simplicity_bitcoin_tap_env_hash bitcoin_ge ext_environment\n    Ty.Unit Word256 (hash_getter_rep tap_env_hash_of 8 72 176)\n    (fun a environment => @tap_env_hash_spec fullalg a environment)."
    ],
    [
      "Coq/C/jet_bitcoin_tx_hash.v",
      "statement",
      "bitcoin_input_outpoints_hash_local_spec",
      "Theorem bitcoin_input_outpoints_hash_local_spec :\n  application_jet_local_spec_sep f_simplicity_bitcoin_input_outpoints_hash bitcoin_ge ext_environment\n    Ty.Unit Word256 (hash_getter_rep input_outpoints_hash_of 0 112 432)\n    (fun a environment => @input_outpoints_hash_spec fullalg a environment)."
    ],
    [
      "Coq/C/jet_bitcoin_tx_hash.v",
      "statement",
      "bitcoin_input_annexes_hash_local_spec",
      "Theorem bitcoin_input_annexes_hash_local_spec :\n  application_jet_local_spec_sep f_simplicity_bitcoin_input_annexes_hash bitcoin_ge ext_environment\n    Ty.Unit Word256 (hash_getter_rep input_annexes_hash_of 0 272 432)\n    (fun a environment => @input_annexes_hash_spec fullalg a environment)."
    ],
    [
      "Coq/C/jet_bitcoin_tx_hash.v",
      "statement",
      "bitcoin_inputs_hash_local_spec",
      "Theorem bitcoin_inputs_hash_local_spec :\n  application_jet_local_spec_sep f_simplicity_bitcoin_inputs_hash bitcoin_ge ext_environment\n    Ty.Unit Word256 (hash_getter_rep inputs_hash_of 0 336 432)\n    (fun a environment => @inputs_hash_spec fullalg a environment)."
    ],
    [
      "Coq/C/jet_bitcoin_tx_hash.v",
      "statement",
      "bitcoin_tx_hash_local_spec",
      "Theorem bitcoin_tx_hash_local_spec :\n  application_jet_local_spec_sep f_simplicity_bitcoin_tx_hash bitcoin_ge ext_environment\n    Ty.Unit Word256 (hash_getter_rep tx_hash_of 0 368 432)\n    (fun a environment => @tx_hash_spec fullalg a environment)."
    ],
    [
      "Coq/C/jet_bitcoin_sig_all_hash.v",
      "statement",
      "bitcoin_sig_all_hash_local_spec",
      "Theorem bitcoin_sig_all_hash_local_spec :\n  application_jet_local_spec_sep f_simplicity_bitcoin_sig_all_hash bitcoin_ge ext_environment\n    Ty.Unit Word256 (env_hash_rep sig_all_hash_of 16)\n    (fun a environment => @sig_all_hash_spec fullalg a environment)."
    ],
    [
      "Coq/C/jet_bitcoin_composite_hash.v",
      "declaration",
      "sha256_bytes_of",
      "Definition sha256_bytes_of (bs : list (Ty.tySem (Word 3))) : hash256 :=\n  mk_hash256 (sha_stream [] sha256_iv_words 0 bs).\n\n "
    ],
    [
      "Coq/C/jet_bitcoin_composite_hash.v",
      "declaration",
      "pair_hash_of",
      "Definition pair_hash_of (a b : hash256) : hash256 :=\n  sha256_bytes_of (vector_values (Word 3) 6 (from_hash256 a, from_hash256 b)).\n"
    ],
    [
      "Coq/C/jet_bitcoin_composite_hash.v",
      "declaration",
      "outputs_hash_of",
      "Definition outputs_hash_of (e : ext_environment) : hash256 :=\n  pair_hash_of (words_hash_of 3 5 (output_values_of e)) (words_hash_of 5 5 (output_scripts_of e)).\n"
    ],
    [
      "Coq/C/jet_bitcoin_composite_hash.v",
      "declaration",
      "input_utxos_hash_of",
      "Definition input_utxos_hash_of (e : ext_environment) : hash256 :=\n  pair_hash_of (words_hash_of 3 5 (input_values_of e)) (words_hash_of 5 5 (input_scripts_of e)).\n"
    ],
    [
      "Coq/C/jet_bitcoin_composite_hash.v",
      "declaration",
      "tap_env_hash_of",
      "Definition tap_env_hash_of (e : ext_environment) : hash256 :=\n  sha256_bytes_of\n    (vector_values (Word 3) 5 (from_hash256 (tapleaf_hash_of e)) ++\n     vector_values (Word 3) 6\n       (from_hash256 (words_hash_of 5 3 (tappath_of e)), from_hash256 (extInternalKey e))).\n"
    ],
    [
      "Coq/C/jet_bitcoin_tx_hash.v",
      "declaration",
      "elems_hash_of",
      "Definition elems_hash_of (xs : list (Ty.tySem X)) : hash256 :=\n  sha256_bytes_of (gen_bytes X bytes_of (firstn (Z.to_nat (wsize w)) xs)).\n"
    ],
    [
      "Coq/C/jet_bitcoin_tx_hash.v",
      "declaration",
      "outpoint_bytes",
      "Definition outpoint_bytes (x : Ty.tySem (Ty.Prod (Word 8) (Word 5))) : list (Ty.tySem (Word 3)) :=\n  vector_values (Word 3) 5 (fst x) ++ vector_values (Word 3) 2 (snd x).\n"
    ],
    [
      "Coq/C/jet_bitcoin_tx_hash.v",
      "declaration",
      "outpoints_of",
      "Definition outpoints_of (e : ext_environment) : list (Ty.tySem (Ty.Prod (Word 8) (Word 5))) :=\n  map (fun x => (from_hash256 (opHash (sigTxiPreviousOutpoint x)),\n                 @fromZ (WordToZ 5) (Int.unsigned (opIndex (sigTxiPreviousOutpoint x)))))\n    (sigTxIn (Bitcoin.envTx (extBase e))).\n"
    ],
    [
      "Coq/C/jet_bitcoin_tx_hash.v",
      "declaration",
      "input_outpoints_hash_of",
      "Definition input_outpoints_hash_of (e : ext_environment) : hash256 :=\n  elems_hash_of (Ty.Prod (Word 8) (Word 5)) outpoint_bytes 5 (outpoints_of e).\n"
    ],
    [
      "Coq/C/jet_bitcoin_tx_hash.v",
      "declaration",
      "annex_elem_bytes",
      "Definition annex_elem_bytes (a : Ty.tySem (Ty.Sum Ty.Unit (Word 8))) : list (Ty.tySem (Word 3)) :=\n  match a with\n  | inl _ => [byte_zero]\n  | inr h => byte_one :: vector_values (Word 3) 5 h\n  end.\n"
    ],
    [
      "Coq/C/jet_bitcoin_tx_hash.v",
      "declaration",
      "annexes_of",
      "Definition annexes_of (e : ext_environment) : list (Ty.tySem (Ty.Sum Ty.Unit (Word 8))) :=\n  map (fun o : option hash256 => match o with\n                | None => inl tt\n                | Some h => inr (from_hash256 h)\n                end) (extInAnnexHash e).\n"
    ],
    [
      "Coq/C/jet_bitcoin_tx_hash.v",
      "declaration",
      "input_annexes_hash_of",
      "Definition input_annexes_hash_of (e : ext_environment) : hash256 :=\n  elems_hash_of (Ty.Sum Ty.Unit (Word 8)) annex_elem_bytes 5 (annexes_of e).\n"
    ],
    [
      "Coq/C/jet_bitcoin_tx_hash.v",
      "declaration",
      "inputs_hash_of",
      "Definition inputs_hash_of (e : ext_environment) : hash256 :=\n  sha256_bytes_of\n    (vector_values (Word 3) 6\n       (from_hash256 (input_outpoints_hash_of e),\n        from_hash256 (words_hash_of 2 5 (input_sequences_of e))) ++\n     vector_values (Word 3) 5 (from_hash256 (input_annexes_hash_of e))).\n"
    ],
    [
      "Coq/C/jet_bitcoin_tx_hash.v",
      "declaration",
      "tx_version_word",
      "Definition tx_version_word (e : ext_environment) : Ty.tySem (Word 5) :=\n  @fromZ (WordToZ 5) (Int.signed (sigTxVersion (Bitcoin.envTx (extBase e))))."
    ],
    [
      "Coq/C/jet_bitcoin_tx_hash.v",
      "declaration",
      "tx_locktime_word",
      "Definition tx_locktime_word (e : ext_environment) : Ty.tySem (Word 5) :=\n  @fromZ (WordToZ 5) (Int.unsigned (sigTxLock (Bitcoin.envTx (extBase e)))).\n"
    ],
    [
      "Coq/C/jet_bitcoin_tx_hash.v",
      "declaration",
      "tx_hash_of",
      "Definition tx_hash_of (e : ext_environment) : hash256 :=\n  sha256_bytes_of\n    (vector_values (Word 3) 3 (tx_version_word e, tx_locktime_word e) ++\n     vector_values (Word 3) 6 (from_hash256 (inputs_hash_of e), from_hash256 (outputs_hash_of e)) ++\n     vector_values (Word 3) 5 (from_hash256 (input_utxos_hash_of e))).\n"
    ],
    [
      "Coq/C/jet_bitcoin_sig_all_hash.v",
      "declaration",
      "current_index_word",
      "Definition current_index_word (e : ext_environment) : Ty.tySem (Word 5) :=\n  @fromZ (WordToZ 5) (Z.of_nat (Bitcoin.envIx (extBase e))).\n"
    ],
    [
      "Coq/C/jet_bitcoin_sig_all_hash.v",
      "declaration",
      "sig_all_hash_of",
      "Definition sig_all_hash_of (e : ext_environment) : hash256 :=\n  sha256_bytes_of\n    (vector_values (Word 3) 6 (from_hash256 (tx_hash_of e), from_hash256 (tap_env_hash_of e)) ++\n     vector_values (Word 3) 2 (current_index_word e)).\n"
    ]
  ],
  "blocks": [
    [
      "Haskell/Simplicity/Bitcoin/Programs/SigHash.hs",
      "mkLib Sha256.Lib{..} Sha256.LibAssert{..} Transaction.Lib{..} = lib",
      "lib :: (Assert term, Primitive term) => Lib term",
      "where\n  lib@Lib{..} = Lib {\n    outputValuesHash = hashWord64s (drop (primitive OutputValue))\n\n  , outputScriptsHash = hashWord256s32 (drop (primitive OutputScriptHash))\n\n  , outputsHash = ctx8Init &&& (outputValuesHash &&& outputScriptsHash) >>> ctx8Add64 >>> ctx8Finalize\n\n  , outputHash = (primitive OutputValue &&& primitive OutputScriptHash)\n             >>> match (injl unit)\n                       (injr (((unit >>> ctx8Init) &&& oh >>> ctx8Add8)\n                         &&& (drop . assert $ iden) >>> ctx8Add32 >>> ctx8Finalize))\n\n  , inputValuesHash = hashWord64s (drop (primitive InputValue))\n\n  , inputScriptsHash = hashWord256s32 (drop (primitive InputScriptHash))\n\n  , inputUtxosHash = ctx8Init &&& (inputValuesHash &&& inputScriptsHash) >>> ctx8Addn vector64 >>> ctx8Finalize\n\n  , inputUtxoHash = (primitive InputValue &&& primitive InputScriptHash)\n             >>> match (injl unit)\n                       (injr (((unit >>> ctx8Init) &&& oh >>> ctx8Add8)\n                         &&& (drop . assert $ iden) >>> ctx8Add32 >>> ctx8Finalize))\n\n  , inputOutpointsHash =\n     let\n      finalize = ctx8Finalize\n      body = (take (drop (primitive InputPrevOutpoint)) &&& ih)\n         >>> match (injl ih) (injr (ih &&& oh >>> outpointHash))\n     in\n      unit &&& ctx8Init >>> forWhile word32 body >>> copair finalize finalize\n\n  , inputSequencesHash = hashWord32s (drop (primitive InputSequence))\n\n  , inputAnnexesHash =\n     let\n      finalize = ctx8Finalize\n      body = take (drop (primitive InputAnnexHash)) &&& ih\n         >>> match (injl ih) (injr (ih &&& oh >>> annexHash))\n     in\n      unit &&& ctx8Init >>> forWhile word32 body >>> copair finalize finalize\n\n  , inputScriptSigsHash = hashWord256s32 (drop (primitive InputScriptSigHash))\n\n  , inputsHash = (ctx8Init &&& (inputOutpointsHash &&& inputSequencesHash) >>> ctx8Addn vector64)\n             &&& inputAnnexesHash >>> ctx8Addn vector32 >>> ctx8Finalize\n\n  , inputHash = (primitive InputPrevOutpoint &&& (primitive InputSequence &&& primitive InputAnnexHash))\n            >>> match (injl unit)\n                      (injr ((((unit >>> ctx8Init) &&& oh >>> outpointHash)\n                    &&& (drop . take . assert $ iden) >>> ctx8Add4)\n                    &&& (drop . drop . assert $ iden) >>> annexHash >>> ctx8Finalize))\n\n  , txHash = ((ctx8Init &&& (primitive Version &&& primitive LockTime) >>> ctx8Addn vector8)\n         &&& (inputsHash &&& outputsHash) >>> ctx8Addn vector64)\n         &&& inputUtxosHash >>> ctx8Addn vector32 >>> ctx8Finalize\n\n  , tapleafHash = ((Sha256.ctx8InitTag \"TapLeaf\")\n              &&& (primitive TapleafVersion &&& scribe (toWord8 32)) >>> ctx8Addn vector2)\n              &&& (primitive ScriptCMR) >>> ctx8Addn vector32 >>> ctx8Finalize\n\n  , tappathHash = hashWord256s8 (drop (primitive Tappath))\n\n  , tapEnvHash = (ctx8Init &&& tapleafHash >>> ctx8Addn vector32)\n             &&& (tappathHash &&& primitive InternalKey) >>> ctx8Addn vector64 >>> ctx8Finalize\n\n  , sigAllHash = (ctx8Init &&& (txHash &&& tapEnvHash) >>> ctx8Addn vector64)\n             &&& primitive CurrentIndex >>> ctx8Addn vector4 >>> ctx8Finalize\n  }\n  hashLoop256 :: (TyC w, TyC c) => Word w -> term (c, w) (S Word256) -> term (c, Ctx8) Ctx8\n  hashLoop256 = Sha256.hashLoop vector32\n  hashWord256s :: (TyC w, TyC c) => Word w -> term (c, w) (S Word256) -> term c Word256\n  hashWord256s w array = iden &&& (unit >>> ctx8Init) >>> hashLoop256 w array >>> ctx8Finalize\n  hashWord256s32 = hashWord256s word32\n  hashWord256s8 = hashWord256s word8\n  hashWord64s array = iden &&& (unit >>> ctx8Init) >>> Sha256.hashLoop vector8 word32 array >>> ctx8Finalize\n  hashWord32s array = iden &&& (unit >>> ctx8Init) >>> Sha256.hashLoop vector4 word32 array >>> ctx8Finalize\n  ctx8Add4 = ctx8Addn vector4\n  ctx8Add8 = ctx8Addn vector8\n  ctx8Add32 = ctx8Addn vector32\n  ctx8Add64 = ctx8Addn vector64"
    ],
    [
      "Haskell/Core/Simplicity/Programs/Sha256.hs",
      "hashLoop v =",
      "ctx8InitTag ::",
      "\\w array ->\n  let body = take array &&& ih\n         >>> match (injl ih) (injr (ih &&& oh >>> ctx8Addv))\n  in forWhile w body >>> copair iden iden\n where\n  ctx8Addv = ctx8Addn libAssert v"
    ],
    [
      "Haskell/Core/Simplicity/Programs/Word.hs",
      "forWhile SingleV body =",
      "firstFail ::",
      "(((oh &&& false) &&& ih) >>> monobody) &&& oh\n                    >>> match (injl oh) (((ih &&& true) &&& oh) >>> monobody)\n where\n  monobody = body\nforWhile (DoubleV n) body = forWhile n (forWhile n ((oooh &&& (ooih &&& oih)) &&& ih >>> body))"
    ],
    [
      "Haskell/Core/Simplicity/Programs/Bitcoin.hs",
      "    outpointHash = (oh &&& ioh",
      "  , buildTaptweak = assert",
      ">>> ctx8Add32) &&& iih >>> ctx8Add4\n  , annexHash = ih &&& oh\n            >>> match (ih &&& take (zero word8) >>> ctx8Add1)\n                      ((ih &&& (unit >>> scribe (toWord8 0x01)) >>> ctx8Add1) &&& oh >>> ctx8Add32)"
    ]
  ]
}

