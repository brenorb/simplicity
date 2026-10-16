(** The Elements pegin/outpoint hash loop and the original C cache getter.
    The optional pegin and optional indexed outpoint are routed separately. *)
From Coq Require Import ZArith List Lia FunctionalExtensionality.
From compcert Require Import Integers AST Ctypes Clight.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest Simplicity.Alg.
Require Import Simplicity.Primitive Simplicity.Util.Option.
Require Import C.jet_elements_prim C.jets_elements C.jet_elements_linkage.
Require Import C.jet_application_sep C.jet_elements_field_eval C.jet_elements_wrapper.
Require Import C.jet_elements_hash_getters C.jet_elements_script_cmr_local.
Require Import C.jet_elements_hash_getter_local C.jet_elements_hash_getter_writehash.
Require Import C.jet_buffer_empty_spec C.jet_buffer_input C.jet_forWhile_seq C.jet_forWhile_spec.
Require Import C.jet_sha256_ctx8_init_spec C.jet_sha_ctx8_spec C.jet_sha_finalize_spec.
Require Import C.jet_bitcoin_ctx_hash_spec C.jet_sha_add_buffer_spec C.jet_sha_hash_loop_gen.
Require Import C.jet_bitcoin_tx_hash C.jet_sha_hash_words_reader C.jet_sha_hash_elems_reader.
Require Import C.jet_elements_words_hash_program.
Import ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition elements_outpoint_type : Ty :=
  Ty.Prod (Ty.Sum Ty.Unit Word256) (Ty.Prod Word256 Word32).

Definition elements_outpoint_add_spec {term : Alg.Assertion.Algebra} :
    term (Ty.Prod sha256_ctx8_type elements_outpoint_type) sha256_ctx8_type :=
  let core := Alg.Assertion.toCore term in
  let c := @AC.take sha256_ctx8_type elements_outpoint_type _ core (@AC.iden _ core) in
  let pg := @AC.drop sha256_ctx8_type elements_outpoint_type _ core
    (@AC.take (Ty.Sum Ty.Unit Word256) (Ty.Prod Word256 Word32) _ core (@AC.iden _ core)) in
  let h := @AC.drop sha256_ctx8_type elements_outpoint_type _ core
    (@AC.drop (Ty.Sum Ty.Unit Word256) (Ty.Prod Word256 Word32) _ core
      (@AC.take Word256 Word32 _ core (@AC.iden _ core))) in
  let ix := @AC.drop sha256_ctx8_type elements_outpoint_type _ core
    (@AC.drop (Ty.Sum Ty.Unit Word256) (Ty.Prod Word256 Word32) _ core
      (@AC.drop Word256 Word32 _ core (@AC.iden _ core))) in
  @AC.comp _ _ _ core
    (@AC.pair _ _ _ core
      (@AC.comp _ _ _ core
        (@AC.pair _ _ _ core (@AC.comp _ _ _ core (@AC.pair _ _ _ core c pg) (@annex_hash_spec term)) h)
        (@ctx8_addn_spec 5 term)) ix)
    (@ctx8_addn_spec 2 term).

Lemma elements_outpoint_add_spec_parametric : Alg.Assertion.Parametric (@elements_outpoint_add_spec).
Proof.
  intros alg1 alg2 R.
  pose proof (annex_hash_spec_parametric _ _ R) as HAnnex.
  pose proof (ctx8_addn_spec_parametric 5 _ _ R) as H32.
  pose proof (ctx8_addn_spec_parametric 2 _ _ R) as H4.
  destruct R as [R [HC HA]]. set (RC := Alg.Core.Parametric.Pack HC).
  unfold elements_outpoint_add_spec. cbv zeta.
  solve [repeat first [exact HAnnex | exact H32 | exact H4 |
    apply (Alg.comp_Parametric RC) | apply (Alg.pair_Parametric RC) |
    apply (Alg.take_Parametric RC) | apply (Alg.drop_Parametric RC) |
    apply Alg.iden_Parametric]].
Qed.

Definition elements_outpoint_bytes (x : Ty.tySem elements_outpoint_type) : list (Ty.tySem Word8) :=
  annex_elem_bytes (fst x) ++ vector_values Word8 5 (fst (snd x)) ++ vector_values Word8 2 (snd (snd x)).

Lemma elements_outpoint_add_option c x :
  @elements_outpoint_add_spec optalg (c, x) = ctx8_add_list c (elements_outpoint_bytes x).
Proof.
  destruct x as [pg [h ix]]. unfold elements_outpoint_add_spec, elements_outpoint_bytes. cbv zeta.
  opt_steps. rewrite annex_hash_option. fold (annex_elem_bytes pg).
  rewrite !ctx8_add_list_app.
  destruct (ctx8_add_list c (annex_elem_bytes pg)) as [c1 | ]; [ | reflexivity].
  opt_steps. rewrite (ctx8_addn_option 5), ctx8_add_list_app.
  destruct (ctx8_add_list c1 (vector_values Word8 5 h)) as [c2 | ]; [ | reflexivity].
  opt_steps. apply (ctx8_addn_option 2).
Qed.

Lemma elements_outpoint_bytes_bound x : Z.of_nat (List.length (elements_outpoint_bytes x)) <= 69.
Proof.
  unfold elements_outpoint_bytes. rewrite !app_length, !vector_values_length.
  rewrite Nat2Z.inj_add.
  change (Z.of_nat (List.length (annex_elem_bytes (fst x))) + 36 <= 69).
  pose proof (annex_bytes_bound (fst x)). lia.
Qed.

Lemma elements_outpoint_loop_bound : 69 * wsize 5 / 64 < ctx8_limit.
Proof. vm_compute. reflexivity. Qed.

Definition elements_outpoints_array {alg : EFP.Algebra} :
    EFP.domain alg (Ty.Prod Ty.Unit Word32) (Ty.Sum Ty.Unit elements_outpoint_type) :=
  let core := Alg.Assertion.toCore (EFP.CanonicalStructures.toAssertion alg) in
  @AC.comp _ _ _ core
    (@AC.pair _ _ _ core
      (@AC.drop Ty.Unit Word32 _ core (@EFP.Combinators.prim _ _ alg Elements.InputPegin))
      (@AC.drop Ty.Unit Word32 _ core (@EFP.Combinators.prim _ _ alg Elements.InputPrevOutpoint)))
    (@AC.case _ _ _ _ core (@AC.injl _ _ _ core (@AC.unit _ core))
      (@AC.comp _ _ _ core
        (@AC.pair _ _ _ core (AC.drop AC.iden) (AC.take AC.iden))
        (@AC.case _ _ _ _ core (@AC.injl _ _ _ core (@AC.unit _ core))
          (@AC.injr _ _ _ core (@AC.pair _ _ _ core (AC.drop AC.iden) (AC.take AC.iden)))))).

(** Same routing tree as the Haskell body, including both early exits. *)
Definition elements_outpoints_body {alg : EFP.Algebra} :
    EFP.domain alg (Ty.Prod (Ty.Prod Ty.Unit Word32) sha256_ctx8_type)
      (Ty.Sum sha256_ctx8_type sha256_ctx8_type) :=
  let term := EFP.CanonicalStructures.toAssertion alg in
  let core := Alg.Assertion.toCore term in
  @AC.comp _ _ _ core
    (@AC.pair _ _ _ core
      (@AC.take _ _ _ core (@AC.drop Ty.Unit Word32 _ core (@EFP.Combinators.prim _ _ alg Elements.InputPegin)))
      (@AC.pair _ _ _ core
        (@AC.take _ _ _ core (@AC.drop Ty.Unit Word32 _ core (@EFP.Combinators.prim _ _ alg Elements.InputPrevOutpoint)))
        (AC.drop AC.iden)))
    (@AC.case _ _ _ _ core (@AC.injl _ _ _ core (AC.drop (AC.drop AC.iden)))
      (@AC.comp _ _ _ core
        (@AC.pair _ _ _ core (AC.drop (AC.take AC.iden))
          (@AC.pair _ _ _ core (AC.take AC.iden) (AC.drop (AC.drop AC.iden))))
        (@AC.case _ _ _ _ core (@AC.injl _ _ _ core (AC.drop (AC.drop AC.iden)))
          (@AC.injr _ _ _ core (@AC.comp _ _ _ core
            (@AC.pair _ _ _ core (AC.drop (AC.drop AC.iden))
              (@AC.pair _ _ _ core (AC.drop (AC.take AC.iden)) (AC.take AC.iden)))
            (@elements_outpoint_add_spec term)))))).

Ltac elements_outpoints_parametric_step RC HP :=
  first [apply HP | apply (Alg.comp_Parametric RC) | apply (Alg.pair_Parametric RC) |
    apply (Alg.case_Parametric RC) | apply (Alg.injl_Parametric RC) | apply (Alg.injr_Parametric RC) |
    apply (Alg.take_Parametric RC) | apply (Alg.drop_Parametric RC) |
    apply Alg.unit_Parametric | apply Alg.iden_Parametric].

Lemma elements_outpoints_array_parametric : EFP.Parametric (@elements_outpoints_array).
Proof.
  intros alg1 alg2 R. destruct R as [R [HA [HP]]].
  destruct HA as [HC HAm]. set (RC := Alg.Core.Parametric.Pack HC).
  unfold elements_outpoints_array. cbv zeta.
  solve [repeat elements_outpoints_parametric_step RC HP].
Qed.

Lemma elements_outpoints_body_parametric : EFP.Parametric (@elements_outpoints_body).
Proof.
  intros alg1 alg2 R. destruct R as [R [HA [HP]]].
  set (RA := Alg.Assertion.Parametric.Pack HA).
  pose proof (elements_outpoint_add_spec_parametric _ _ RA) as HAdd.
  destruct HA as [HC HAm]. set (RC := Alg.Core.Parametric.Pack HC).
  unfold elements_outpoints_body. cbv zeta.
  solve [repeat first [exact HAdd | elements_outpoints_parametric_step RC HP]].
Qed.

Definition elements_outpoints_of (e : Elements.env) : list (Ty.tySem elements_outpoint_type) :=
  map (fun txi =>
    (match sigTxiPegin txi with None => inl tt | Some h => inr (from_hash256 h) end,
     (from_hash256 (opHash (sigTxiPreviousOutpoint txi)),
      @fromZ (WordToZ 5) (Int.unsigned (opIndex (sigTxiPreviousOutpoint txi))))))
    (sigTxIn (Elements.envTx e)).

Ltac elements_outpoints_reader_steps :=
  repeat progress (cbv beta iota zeta; cbn [fst snd];
    rewrite ?(hr_comp Elements.env), ?(hr_pair Elements.env), ?(hr_take Elements.env),
      ?(hr_drop Elements.env), ?(hr_iden Elements.env), ?(hr_unit Elements.env),
      ?(hr_case Elements.env), ?(hr_injl Elements.env), ?(hr_injr Elements.env), ?elements_hash_prim).

Lemma elements_outpoints_array_sem i e :
  @elements_outpoints_array elements_hash_alg (tt, i) e =
    Some (match nth_error (elements_outpoints_of e) (Z.to_nat (wz 5 i)) with
          Some x => inr x | None => inl tt end).
Proof.
  unfold elements_outpoints_array, elements_outpoints_of. cbv zeta.
  rewrite nth_error_map. elements_outpoints_reader_steps.
  unfold Elements.sem, wz.
  destruct (nth_error (sigTxIn (Elements.envTx e)) (Z.to_nat (@toZ (WordToZ 5) i))) as [txi | ];
    cbn [option_map]; elements_outpoints_reader_steps;
    [destruct (sigTxiPegin txi) | ]; reflexivity.
Qed.

Lemma elements_outpoints_body_reader_matches i c e :
  @elements_outpoints_body elements_hash_alg ((tt, i), c) e =
    @gen_loop_body elements_outpoint_type (fun term => @elements_outpoint_add_spec term)
      (hash_reader_alg Elements.env) Ty.Unit Word32
      (@elements_outpoints_array elements_hash_alg) ((tt, i), c) e.
Proof.
  unfold elements_outpoints_body, gen_loop_body, elements_outpoints_array. cbv zeta.
  elements_outpoints_reader_steps. unfold Elements.sem.
  destruct (nth_error (sigTxIn (Elements.envTx e)) (Z.to_nat (@toZ (WordToZ 5) i))) as [txi | ];
    cbn [option_map]; elements_outpoints_reader_steps; reflexivity.
Qed.

Lemma elements_outpoints_body_reader_eq :
  @elements_outpoints_body elements_hash_alg =
    @gen_loop_body elements_outpoint_type (fun term => @elements_outpoint_add_spec term)
      (hash_reader_alg Elements.env) Ty.Unit Word32 (@elements_outpoints_array elements_hash_alg).
Proof.
  apply functional_extensionality. intros [[[] i] c].
  apply functional_extensionality. intro e. apply elements_outpoints_body_reader_matches.
Qed.

Definition elements_input_outpoints_hash_spec {alg : EFP.Algebra} : EFP.domain alg Ty.Unit Word256 :=
  let term := EFP.CanonicalStructures.toAssertion alg in
  let core := Alg.Assertion.toCore term in
  @AC.comp _ _ _ core
    (@AC.pair _ _ _ core (@AC.unit _ core) (@sha256_ctx8_init_spec core))
    (@AC.comp _ _ _ core
      (@for_while_program 5 _ _ _ core (@elements_outpoints_body alg))
      (@AC.copair _ _ _ core (@ctx8_finalize_spec term) (@ctx8_finalize_spec term))).

Lemma elements_input_outpoints_hash_spec_parametric : EFP.Parametric (@elements_input_outpoints_hash_spec).
Proof.
  intros alg1 alg2 R. pose proof (elements_outpoints_body_parametric _ _ R) as HBody.
  destruct R as [R [HA [HP]]]. set (RA := Alg.Assertion.Parametric.Pack HA).
  pose proof (ctx8_finalize_spec_parametric _ _ RA) as HF.
  destruct HA as [HC HAm]. set (RC := Alg.Core.Parametric.Pack HC).
  unfold elements_input_outpoints_hash_spec. cbv zeta.
  apply (Alg.comp_Parametric RC).
  - apply (Alg.pair_Parametric RC); [apply Alg.unit_Parametric | apply (sha256_ctx8_init_spec_parametric _ _ RC)].
  - apply (Alg.comp_Parametric RC).
    + apply (for_while_program_parametric 5 RC). exact HBody.
    + apply (Alg.copair_Parametric RC); exact HF.
Qed.

Lemma elements_input_outpoints_hash_reader_program_matches :
  @elements_input_outpoints_hash_spec elements_hash_alg =
    @hash_elems_spec elements_outpoint_type (fun term => @elements_outpoint_add_spec term) 5
      (hash_reader_alg Elements.env) (@elements_outpoints_array elements_hash_alg).
Proof.
  unfold elements_input_outpoints_hash_spec, hash_elems_spec, gen_loop_run. cbv zeta.
  rewrite elements_outpoints_body_reader_eq. reflexivity.
Qed.

Definition elements_input_outpoints_hash_of (e : Elements.env) : hash256 :=
  elems_hash_of elements_outpoint_type elements_outpoint_bytes 5 (elements_outpoints_of e).

Theorem elements_input_outpoints_hash_spec_sem e :
  @elements_input_outpoints_hash_spec elements_hash_alg tt e =
    Some (from_hash256 (elements_input_outpoints_hash_of e)).
Proof.
  rewrite elements_input_outpoints_hash_reader_program_matches.
  apply (hash_elems_reader_sem Elements.env elements_outpoint_type
    (fun term => @elements_outpoint_add_spec term) elements_outpoint_add_spec_parametric
    elements_outpoint_bytes elements_outpoint_add_option 5 _ e (elements_outpoints_of e) 69).
  - intro i. exact (elements_outpoints_array_sem i e).
  - apply elements_outpoint_bytes_bound.
  - lia.
  - exact elements_outpoint_loop_bound.
Qed.

Theorem elements_input_outpoints_hash_program_local_spec :
  application_jet_local_spec_sep f_simplicity_input_outpoints_hash elements_ge Elements.env Ty.Unit Word256
    (hash_getter_rep elements_input_outpoints_hash_of 0 216 760)
    (fun a e => @elements_input_outpoints_hash_spec elements_hash_alg a e).
Proof.
  eapply elements_hash_getter_writeHash_local with (ptrfield := _tx) (sid := _elementsTransaction)
    (hashfield := _inputOutpointsHash).
  - exact elements_input_outpoints_hash_spec_sem.
  - elements_hash_getter_shape.
  - exact elements_txEnv_tx.
  - vm_compute; reflexivity.
  - lia.
  - lia.
Qed.
