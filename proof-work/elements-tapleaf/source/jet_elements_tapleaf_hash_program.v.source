(** Original Elements tapleaf_hash C getter against the literal tagged-hash
    program with TapleafVersion and ScriptCMR primitives.  The tag is derived
    from its ASCII bytes, not postulated as an unrelated numeric midstate. *)
From Coq Require Import ZArith List String Lia.
From compcert Require Import Integers AST Ctypes Clight.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest Simplicity.Alg.
Require Import Simplicity.Primitive Simplicity.Util.Option.
Require Import C.jet_elements_prim C.jets_elements C.jet_elements_linkage.
Require Import C.jet_application_sep C.jet_elements_field_eval C.jet_elements_wrapper.
Require Import C.jet_elements_hash_getters C.jet_elements_script_cmr_local.
Require Import C.jet_elements_hash_getter_local C.jet_elements_hash_getter_writehash.
Require Import C.jet_buffer_empty_spec C.jet_buffer_input C.jet_sha256_ctx8_init_spec.
Require Import C.jet_sha_ctx8_spec C.jet_sha_ctx8_model C.jet_sha_finalize_spec C.jet_sha_hash_closed.
Require Import C.jet_bitcoin_tapleaf_hash_spec C.jet_sha_hash_words_reader.
Require Import C.jet_elements_words_hash_program C.jet_haskell_word_conversion C.jet_haskell_hash_word.
Import ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition elements_tapleaf_ascii : list byte :=
  map Byte.repr [84; 97; 112; 76; 101; 97; 102; 47; 101; 108; 101; 109; 101; 110; 116; 115].
Definition elements_tapleaf_tag_digest := byteStringHash elements_tapleaf_ascii.
Definition elements_tapleaf_midstate :=
  compress Digest.sha256_iv elements_tapleaf_tag_digest elements_tapleaf_tag_digest.
Definition elements_tapleaf_prefix : Ty.tySem Word256 :=
  haskell_to_word 8 (haskell_integer_hash256 (hash256_to_bytelist elements_tapleaf_midstate)).
Definition elements_tapleaf_size : Ty.tySem Word8 := haskell_to_word 3 32.

Lemma elements_tapleaf_ascii_string :
  elements_tapleaf_ascii = sha.SHA256.str_to_bytes "TapLeaf/elements"%string.
Proof. reflexivity. Qed.

Lemma elements_tapleaf_prefix_matches :
  elements_tapleaf_prefix = from_hash256 elements_tapleaf_midstate.
Proof. unfold elements_tapleaf_prefix. apply haskell_hash_word256. Qed.

Lemma elements_tapleaf_size_matches : elements_tapleaf_size = byte32.
Proof. unfold elements_tapleaf_size, byte32. apply haskell_to_word_matches. Qed.

Definition elements_tapleaf_hash_spec {alg : EFP.Algebra} : EFP.domain alg Ty.Unit Word256 :=
  let term := EFP.CanonicalStructures.toAssertion alg in
  let core := Alg.Assertion.toCore term in
  @AC.comp _ _ _ core
    (@AC.pair _ _ _ core
       (@AC.comp _ _ _ core
          (@AC.pair _ _ _ core (@ctx8_init_tag_spec elements_tapleaf_prefix core)
             (@AC.pair _ _ _ core
                (@EFP.Combinators.prim _ _ alg Elements.TapleafVersion)
                (@Alg.scribe Ty.Unit Word8 elements_tapleaf_size core)))
          (@ctx8_addn_spec 1 term))
       (@EFP.Combinators.prim _ _ alg Elements.ScriptCMR))
    (@AC.comp _ _ _ core (@ctx8_addn_spec 5 term) (@ctx8_finalize_spec term)).

Lemma elements_tapleaf_hash_spec_parametric : EFP.Parametric (@elements_tapleaf_hash_spec).
Proof.
  intros alg1 alg2 R. destruct R as [R [HA [HP]]].
  set (RA := Alg.Assertion.Parametric.Pack HA).
  pose proof (ctx8_addn_spec_parametric 1 _ _ RA) as H1.
  pose proof (ctx8_addn_spec_parametric 5 _ _ RA) as H5.
  pose proof (ctx8_finalize_spec_parametric _ _ RA) as HF.
  destruct HA as [HC HAm]. set (RC := Alg.Core.Parametric.Pack HC).
  unfold elements_tapleaf_hash_spec. cbv zeta.
  apply (Alg.comp_Parametric RC).
  - apply (Alg.pair_Parametric RC); [|apply HP].
    apply (Alg.comp_Parametric RC); [|exact H1].
    apply (Alg.pair_Parametric RC).
    + apply (ctx8_init_tag_spec_parametric elements_tapleaf_prefix _ _ RC).
    + apply (Alg.pair_Parametric RC); [apply HP|apply (Alg.scribe_Parametric RC)].
  - apply (Alg.comp_Parametric RC); [exact H5|exact HF].
Qed.

Definition elements_tapleaf_bytes (e : Elements.env) : list (Ty.tySem Word8) :=
  [@fromZ (WordToZ 3) (Byte.unsigned (tapleafVersion (Elements.envTap e))); elements_tapleaf_size] ++
  vector_values Word8 5 (from_hash256 (tapScriptCMR (Elements.envTap e))).

Definition elements_tapleaf_hash_of (e : Elements.env) : hash256 :=
  mk_hash256 (sha_stream [] (state_regs elements_tapleaf_prefix) 1 (elements_tapleaf_bytes e)).

Theorem elements_tapleaf_hash_spec_sem (e : Elements.env) :
  @elements_tapleaf_hash_spec elements_hash_alg tt e = Some (from_hash256 (elements_tapleaf_hash_of e)).
Proof.
  unfold elements_tapleaf_hash_spec. cbv zeta.
  rewrite (hr_comp Elements.env), (hr_pair Elements.env), (hr_comp Elements.env),
    (hr_pair Elements.env), (hr_pair Elements.env).
  rewrite (hr_core Elements.env (fun alg => @ctx8_init_tag_spec elements_tapleaf_prefix alg)
    (ctx8_init_tag_spec_parametric elements_tapleaf_prefix)), ctx8_init_tag_spec_value.
  rewrite !elements_hash_prim.
  change (Elements.sem Elements.TapleafVersion tt e) with
    (Some (@fromZ (WordToZ 3) (Byte.unsigned (tapleafVersion (Elements.envTap e))))).
  change (Elements.sem Elements.ScriptCMR tt e) with
    (Some (from_hash256 (tapScriptCMR (Elements.envTap e)))).
  rewrite (hr_core Elements.env (fun alg => @Alg.scribe Ty.Unit Word8 elements_tapleaf_size alg)
    (fun a1 a2 R => @Alg.scribe_Parametric a1 a2 R Ty.Unit Word8 elements_tapleaf_size)), Alg.scribe_correct.
  cbv beta iota.
  rewrite (hr_assert Elements.env (fun alg => @ctx8_addn_spec 1 alg) (ctx8_addn_spec_parametric 1)),
    (ctx8_addn_option 1).
  assert (HB : elements_tapleaf_bytes e <> []) by discriminate.
  assert (HT : 1 + Z.of_nat (List.length (elements_tapleaf_bytes e)) / 64 < ctx8_limit).
  { unfold elements_tapleaf_bytes. rewrite app_length, vector_values_length. reflexivity. }
  unfold elements_tapleaf_hash_of.
  rewrite <- (tagged_hash_closed elements_tapleaf_prefix (elements_tapleaf_bytes e) HB HT).
  unfold elements_tapleaf_bytes. rewrite ctx8_add_list_app.
  match goal with |- match match ?X with _ => _ end with _ => _ end = _ =>
    destruct X as [c1|] eqn:H1 end;
  match goal with |- _ = match match ?Y with _ => _ end with _ => _ end =>
    match type of H1 with _ = ?r => assert (H2 : Y = r) by exact H1; rewrite H2 end end;
  [|reflexivity].
  rewrite (hr_comp Elements.env).
  rewrite (hr_assert Elements.env (fun alg => @ctx8_addn_spec 5 alg) (ctx8_addn_spec_parametric 5)),
    (ctx8_addn_option 5).
  match goal with |- match ?X with _ => _ end = _ => destruct X as [c2|] eqn:H3 end;
  try (match goal with |- _ = match ?Y with _ => _ end =>
    match type of H3 with _ = ?r => assert (H4 : Y = r) by exact H3; rewrite H4 end end);
  [|reflexivity].
  apply (hr_assert Elements.env (fun alg => @ctx8_finalize_spec alg) ctx8_finalize_spec_parametric).
Qed.

Theorem elements_tapleaf_hash_program_local_spec :
  application_jet_local_spec_sep f_simplicity_tapleaf_hash elements_ge Elements.env Ty.Unit Word256
    (hash_getter_rep elements_tapleaf_hash_of 8 8 176)
    (fun a e => @elements_tapleaf_hash_spec elements_hash_alg a e).
Proof.
  eapply elements_hash_getter_writeHash_local with (ptrfield := _taproot) (sid := _elementsTapEnv)
    (hashfield := _tapLeafHash).
  - exact elements_tapleaf_hash_spec_sem.
  - elements_hash_getter_shape.
  - exact elements_txEnv_taproot.
  - vm_compute; reflexivity.
  - lia.
  - lia.
Qed.
