(** Full canonical Elements sigAllHash: two copies of GenesisBlockHash,
    txHash, tapEnvHash, CurrentIndex, then the original C cache getter. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest Simplicity.Alg.
Require Import C.jet_elements_prim C.jets_elements C.jet_elements_linkage.
Require Import C.jet_application_sep C.jet_elements_wrapper C.jet_elements_words_hash_program.
Require Import C.jet_elements_direct_hash_getter C.jet_elements_tx_hash_literal.
Require Import C.jet_elements_tap_env_hash_program C.jet_elements_tap_hash_literal.
Require Import C.jet_buffer_empty_spec C.jet_buffer_input C.jet_sha256_ctx8_init_spec.
Require Import C.jet_sha_ctx8_spec C.jet_sha_finalize_spec C.jet_bitcoin_composite_hash C.jet_sha_hash_words_reader.
Require Import C.jet_sha_ctx8_literal C.jet_sha_finalize_literal C.jet_sha_hash_words_literal.
Module AC := Alg.Core.Combinators.
Module EFP := PrimitiveElements.Primitive.
Import ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition elements_sig_all_hash_spec {alg : EFP.Algebra} : EFP.domain alg Ty.Unit Word256 :=
  let term := EFP.CanonicalStructures.toAssertion alg in
  let core := Alg.Assertion.toCore term in
  @AC.comp _ _ _ core
    (@AC.pair _ _ _ core
      (@AC.comp _ _ _ core
        (@AC.pair _ _ _ core (@sha256_ctx8_init_spec core)
          (@AC.pair _ _ _ core
            (@AC.comp _ _ _ core (@EFP.Combinators.prim _ _ alg Elements.GenesisBlockHash)
              (AC.pair AC.iden AC.iden))
            (@AC.pair _ _ _ core (@elements_tx_hash_spec alg) (@elements_tap_env_hash_spec alg))))
        (@ctx8_addn_spec 7 term))
      (@EFP.Combinators.prim _ _ alg Elements.CurrentIndex))
    (@AC.comp _ _ _ core (@ctx8_addn_spec 2 term) (@ctx8_finalize_spec term)).

Lemma elements_sig_all_hash_spec_parametric : EFP.Parametric (@elements_sig_all_hash_spec).
Proof.
  intros alg1 alg2 R.
  pose proof (elements_tx_hash_spec_parametric alg1 alg2 R) as HTx.
  pose proof (elements_tap_env_hash_spec_parametric alg1 alg2 R) as HTap.
  destruct R as [R [HA [HP]]]. set (RA := Alg.Assertion.Parametric.Pack HA).
  pose proof (ctx8_addn_spec_parametric 2 _ _ RA) as H2.
  pose proof (ctx8_addn_spec_parametric 7 _ _ RA) as H7.
  pose proof (ctx8_finalize_spec_parametric _ _ RA) as HF.
  destruct HA as [HC HAm]. set (RC := Alg.Core.Parametric.Pack HC).
  unfold elements_sig_all_hash_spec. cbv zeta.
  apply (Alg.comp_Parametric RC); [|apply (Alg.comp_Parametric RC); [exact H2|exact HF]].
  apply (Alg.pair_Parametric RC); [|apply HP].
  apply (Alg.comp_Parametric RC); [|exact H7].
  apply (Alg.pair_Parametric RC); [apply (sha256_ctx8_init_spec_parametric _ _ RC)|].
  apply (Alg.pair_Parametric RC).
  - apply (Alg.comp_Parametric RC); [apply HP|].
    apply (Alg.pair_Parametric RC); apply Alg.iden_Parametric.
  - apply (Alg.pair_Parametric RC); assumption.
Qed.

Definition elements_genesis_word (e : Elements.env) : Ty.tySem Word256 :=
  from_hash256 (Elements.envGenesisBlock e).
Definition elements_current_index_word (e : Elements.env) : Ty.tySem Word32 :=
  @fromZ (WordToZ 5) (Z.of_nat (Elements.envIx e)).

Definition elements_sig_all_hash_of (e : Elements.env) : hash256 :=
  sha256_bytes_of
    (vector_values Word8 7
      ((elements_genesis_word e, elements_genesis_word e),
       (from_hash256 (elements_tx_hash_of e), from_hash256 (elements_tap_env_hash_of e))) ++
     vector_values Word8 2 (elements_current_index_word e)).

Theorem elements_sig_all_hash_spec_sem e :
  @elements_sig_all_hash_spec elements_hash_alg tt e = Some (from_hash256 (elements_sig_all_hash_of e)).
Proof.
  unfold elements_sig_all_hash_spec. cbv zeta.
  rewrite (hr_comp Elements.env), (hr_pair Elements.env), (hr_comp Elements.env),
    (hr_pair Elements.env), (hr_pair Elements.env), (hr_comp Elements.env), elements_hash_prim.
  change (Elements.sem Elements.GenesisBlockHash tt e) with (Some (elements_genesis_word e)).
  cbv beta iota.
  rewrite (hr_pair Elements.env), !(hr_iden Elements.env), (hr_pair Elements.env),
    elements_tx_hash_spec_sem, elements_tap_env_hash_spec_sem, elements_hash_prim.
  change (Elements.sem Elements.CurrentIndex tt e) with (Some (elements_current_index_word e)).
  rewrite (hr_core Elements.env (fun alg => @sha256_ctx8_init_spec alg) sha256_ctx8_init_spec_parametric).
  cbv beta iota. rewrite (hr_assert Elements.env (fun alg => @ctx8_addn_spec 7 alg) (ctx8_addn_spec_parametric 7)),
    (ctx8_addn_option 7).
  destruct (init_hash_sem
    (vector_values Word8 7
      ((elements_genesis_word e, elements_genesis_word e),
       (from_hash256 (elements_tx_hash_of e), from_hash256 (elements_tap_env_hash_of e))) ++
     vector_values Word8 2 (elements_current_index_word e))) as (cf & H1 & H2).
  { rewrite app_length, !vector_values_length. reflexivity. }
  destruct (add_app_some _ _ _ _ H1) as (c1 & E1 & E2).
  use_add E1. cbv beta iota. rewrite (hr_comp Elements.env).
  rewrite (hr_assert Elements.env (fun alg => @ctx8_addn_spec 2 alg) (ctx8_addn_spec_parametric 2)),
    (ctx8_addn_option 2).
  use_add E2.
  rewrite (hr_assert Elements.env (fun alg => @ctx8_finalize_spec alg) ctx8_finalize_spec_parametric).
  exact H2.
Qed.

Definition literal_elements_sig_all_hash {alg : EFP.Algebra} : EFP.domain alg Ty.Unit Word256 :=
  let term := EFP.CanonicalStructures.toAssertion alg in
  let core := Alg.Assertion.toCore term in
  @AC.comp _ _ _ core
    (@AC.pair _ _ _ core
      (@AC.comp _ _ _ core
        (@AC.pair _ _ _ core (@literal_sha_hash_ctx_init core)
          (@AC.pair _ _ _ core
            (@AC.comp _ _ _ core (@EFP.Combinators.prim _ _ alg Elements.GenesisBlockHash)
              (AC.pair AC.iden AC.iden))
            (@AC.pair _ _ _ core (@literal_elements_tx_hash alg) (@literal_elements_tap_env_hash alg))))
        (@literal_ctx8_addn 7 term))
      (@EFP.Combinators.prim _ _ alg Elements.CurrentIndex))
    (@AC.comp _ _ _ core (@literal_ctx8_addn 2 term) (@literal_ctx8_finalize term)).

Lemma literal_elements_sig_all_hash_matches alg :
  @literal_elements_sig_all_hash alg = @elements_sig_all_hash_spec alg.
Proof.
  unfold literal_elements_sig_all_hash, elements_sig_all_hash_spec.
  rewrite (literal_elements_tx_hash_matches alg), (literal_elements_tap_env_hash_matches alg),
    literal_sha_hash_ctx_init_matches, !literal_ctx8_addn_algebra_matches,
    literal_ctx8_finalize_algebra_matches. reflexivity.
Qed.

Lemma literal_elements_sig_all_hash_parametric : EFP.Parametric (@literal_elements_sig_all_hash).
Proof.
  intros alg1 alg2 R.
  rewrite (literal_elements_sig_all_hash_matches alg1), (literal_elements_sig_all_hash_matches alg2).
  exact (elements_sig_all_hash_spec_parametric alg1 alg2 R).
Qed.

Theorem elements_sig_all_hash_literal_local_spec :
  application_jet_local_spec_sep f_simplicity_sig_all_hash elements_ge Elements.env Ty.Unit Word256
    (elements_direct_hash_rep elements_sig_all_hash_of 48)
    (fun a environment => @literal_elements_sig_all_hash elements_hash_alg a environment).
Proof.
  eapply elements_direct_hash_getter_local with (field := _sigAllHash).
  - intro e. rewrite literal_elements_sig_all_hash_matches. apply elements_sig_all_hash_spec_sem.
  - elements_hash_getter_shape.
  - vm_compute; reflexivity.
  - lia.
Qed.
