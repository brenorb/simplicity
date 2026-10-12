(** The words [simplicity_bitcoin_mallocTapEnv] stores are the canonical
    values the accepted environment relations require.  First link: the
    cached [tapLeafHash] is [tapleaf_hash_of e] whenever the leaf version and
    script CMR of the logical environment [e] are the ones the C code read. *)
From Coq Require Import ZArith List Lia PeanoNat.
From compcert Require Import Integers.
Require sha.SHA256.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest.
Require Import Simplicity.Primitive.Bitcoin.
Require Import C.jet_read8s_layout C.jet_word32_chunks C.jet_buffer_input.
Require Import C.jet_sha_ctx8_model C.jet_sha_ctx8_bridge C.jet_sha_uchars_prep C.jet_sha_finalize_exec.
Require Import C.jet_sha_be32_write C.jet_sha_ctx_abs C.jet_sha_ctxi C.jet_sha_hash_closed C.jet_sha_tapdata_prep.
Require Import C.jet_bitcoin_ext_prim C.jet_bitcoin_tapleaf_hash_spec C.jet_bitcoin_build_tapleaf_spec.
Require Import C.jet_bitcoin_make_tapleaf_exec C.jet_bitcoin_build_tapleaf_jet.
Require Import C.jet_bitcoin_env_stream.
Import ListNotations.
Local Open Scope Z_scope.

Lemma byte32_value : word8_array_value byte32 = Int.repr 32.
Proof. apply Int.same_if_eq. vm_compute. reflexivity. Qed.

Theorem tapleaf_hash_link (e : ext_environment) (v : int) (cmrw : list int) :
  word8_array_value (@fromZ (WordToZ 3) (extTapleafVersion e)) = v ->
  state_regs (from_hash256 (Bitcoin.envScriptCMR (extBase e))) = cmrw ->
  hash256_reg (tapleaf_hash_of e) = make_tapleaf_regs v cmrw.
Proof.
  intros Hv Hc.
  assert (HcL : length cmrw = 8%nat) by (rewrite <- Hc; apply state_regs_length).
  assert (HB : map word8_array_value (tapleaf_bytes e) = [v; Int.repr 32] ++ be_bytes cmrw).
  { unfold tapleaf_bytes. rewrite map_app. cbn [map]. rewrite Hv, byte32_value.
    rewrite <- be_bytes_state_regs, Hc. reflexivity. }
  assert (HBL : length (tapleaf_bytes e) = 34%nat).
  { rewrite <- (map_length word8_array_value), HB, app_length, be_bytes_length, HcL. reflexivity. }
  unfold tapleaf_hash_of.
  rewrite sha_stream_absorb_i by (cbn; lia). cbn [map length].
  rewrite HB, HBL.
  rewrite (absorb_i_small ([v; Int.repr 32] ++ be_bytes cmrw) [] (state_regs tapleaf_prefix))
    by (rewrite app_length, be_bytes_length, HcL; cbn; lia).
  cbn [fst snd app].
  rewrite mk_hash256_reg.
  - unfold make_tapleaf_regs. rewrite btl_prefix_regs. reflexivity.
  - refine (proj2 (proj2 (absorb_i_len (sha_pad (Int64.repr (64 * 1 + Z.of_nat 0 + Z.of_nat 34)))
      ([v; Int.repr 32] ++ be_bytes cmrw) (state_regs tapleaf_prefix) _ _))).
    + rewrite app_length, be_bytes_length, HcL. cbn. lia.
    + apply state_regs_length.
Qed.
