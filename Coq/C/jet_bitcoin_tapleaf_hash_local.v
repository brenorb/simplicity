(** Actual Bitcoin tapleaf_hash jet against the literal tapleafHash program:
    [writeHash(dst, &env->taproot->tapLeafHash)].  The environment relation
    states that the cached field holds the tagged hash [tapleaf_hash_of]. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Maps Errors Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest Simplicity.Translate Simplicity.BitMachine.
Require Simplicity.Alg.
Require Import Simplicity.Util.Option Simplicity.Primitive.Bitcoin.
Require Import C.jet_application_sep C.jets_bitcoin C.jet_bitcoin_linkage.
Require Import C.jet_bitcoin_field_eval C.jet_bitcoin_wrapper C.jet_bitcoin_hash_getters.
Require Import C.jet_bitcoin_script_cmr_local C.jet_bitcoin_hash_getter_local C.jet_bitcoin_hash_getter_writehash.
Require Import C.jet_buffer_empty_spec C.jet_sha_ctx8_spec C.jet_sha_finalize_spec C.jet_sha_tapdata_spec.
Require Import C.jet_bitcoin_ext_prim C.jet_bitcoin_full_prim C.jet_bitcoin_tapleaf_hash_spec.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 60.

Lemma tapleaf_hash_spec_parametric : PF.Parametric (@tapleaf_hash_spec).
Proof.
  intros alg1 alg2 R. destruct R as [R [HA [HP]]].
  set (RA := Alg.Assertion.Parametric.Pack HA).
  pose proof (ctx8_addn_spec_parametric 1 _ _ RA) as H1.
  pose proof (ctx8_addn_spec_parametric 5 _ _ RA) as H5.
  pose proof (ctx8_finalize_spec_parametric _ _ RA) as HF.
  destruct HA as [HC HAm]. set (RC := Alg.Core.Parametric.Pack HC).
  unfold tapleaf_hash_spec. cbv zeta.
  apply (Alg.comp_Parametric RC); [|apply (Alg.comp_Parametric RC); [exact H5|exact HF]].
  apply (Alg.pair_Parametric RC); [|apply HP].
  apply (Alg.comp_Parametric RC); [|exact H1].
  apply (Alg.pair_Parametric RC); [apply (ctx8_init_tag_spec_parametric tapleaf_prefix _ _ RC)|].
  apply (Alg.pair_Parametric RC); [apply HP|apply (Alg.scribe_Parametric RC)].
Qed.

Lemma bitcoin_tapleaf_hash_getter_body :
  bitcoin_wrapper_shape f_simplicity_bitcoin_tapleaf_hash (bitcoin_simple_rest
    (bitcoin_hash_mid_writeHash _taproot _bitcoinTapEnv _tapLeafHash)).
Proof.
  repeat split; try reflexivity.
  intros x y HX HY Hxy. cbn in HX, HY.
  repeat match goal with H : _ \/ _ |- _ => destruct H end; subst;
    first [contradiction | vm_compute in Hxy; discriminate | congruence].
Qed.

Lemma bitcoin_tapLeafHash_at : bitcoin_field_at _bitcoinTapEnv _tapLeafHash 8.
Proof. vm_compute; reflexivity. Qed.

Theorem bitcoin_tapleaf_hash_local_spec :
  application_jet_local_spec_sep f_simplicity_bitcoin_tapleaf_hash bitcoin_ge ext_environment Ty.Unit Word256
    (hash_getter_rep tapleaf_hash_of 8 8 176)
    (fun a environment => @tapleaf_hash_spec fullalg a environment).
Proof.
  eapply bitcoin_hash_getter_writeHash_local with (ptrfield := _taproot) (sid := _bitcoinTapEnv)
    (hashfield := _tapLeafHash).
  - intros e. apply tapleaf_hash_spec_sem.
  - exact bitcoin_tapleaf_hash_getter_body.
  - exact bitcoin_txEnv_taproot.
  - exact bitcoin_tapLeafHash_at.
  - lia.
  - lia.
Qed.
