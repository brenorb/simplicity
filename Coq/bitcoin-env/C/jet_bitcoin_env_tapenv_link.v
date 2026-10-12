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
Require Import C.jet_sha256_iv_init C.jet_forWhile_seq C.jet_sha_hash_loop C.jet_sha_hash_words.
Require Import C.jet_bitcoin_full_prim C.jet_bitcoin_words_hash C.jet_bitcoin_tapleaf_hash_local C.jet_bitcoin_composite_hash.
Require Import C.jet_bitcoin_env_tomidstate C.jet_bitcoin_env_tapenv_loop C.jet_bitcoin_env_tapenv_path C.jet_bitcoin_env_tapenv_tail.
Require Import C.jet_sha_block_local C.jet_sha_uchars_exec.
Require Import C.jet_uint32_array_init C.jet_sha_add_n_calls C.jet_bitcoin_env_tapenv.
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

(** ** The tap-path hash *)

Lemma reg_bytes (h : hash256) :
  be_bytes (hash256_reg h) = map word8_array_value (vector_values (Word 3) 5 (from_hash256 h)).
Proof.
  rewrite <- be_bytes_state_regs. f_equal. unfold state_regs.
  rewrite <- hash256_reg_chunks, to_from_hash256. reflexivity.
Qed.

Lemma firstn_snoc {A} (l : list A) : forall k x, nth_error l k = Some x ->
  firstn (S k) l = firstn k l ++ [x].
Proof.
  induction l as [|a l IH]; intros k x H; destruct k; cbn in H; try discriminate.
  - injection H as ->. reflexivity.
  - cbn [firstn app]. f_equal. apply IH. exact H.
Qed.

Lemma te_st_bytes (pb : nat -> list int) (hs : list hash256) :
  (forall j h, nth_error hs j = Some h -> tm_words (pb j) = hash256_reg h) ->
  forall k, (k <= length hs)%nat ->
  te_st pb k = absorb_i [] sha256_iv_words
    (map word8_array_value (loop_bytes 5 (map (fun x => from_hash256 x) (firstn k hs)))).
Proof.
  intros HP. induction k as [|k IH]; intros Hk.
  - reflexivity.
  - destruct (nth_error hs k) as [h|] eqn:Hn; [|apply nth_error_None in Hn; lia].
    cbn [te_st]. rewrite IH by lia. rewrite (HP k h Hn), reg_bytes.
    rewrite <- absorb_i_app. f_equal.
    rewrite (firstn_snoc hs k h Hn). unfold loop_bytes.
    rewrite !map_app, concat_app, map_app. cbn [map concat]. rewrite app_nil_r. reflexivity.
Qed.

Theorem tappath_hash_link (e : ext_environment) (pb : nat -> list int) :
  (forall j h, nth_error (extTappath e) j = Some h -> tm_words (pb j) = hash256_reg h) ->
  hash256_reg (words_hash_of 5 3 (tappath_of e)) = te_tappath_regs pb (length (extTappath e)).
Proof.
  intros HP. pose proof (extTappath_len e) as HL.
  unfold words_hash_of, tappath_of. change (Z.to_nat (wsize 3)) with 256%nat.
  rewrite firstn_all2 by (rewrite map_length; lia).
  unfold hash_words_of. rewrite sha_stream_absorb_i by (cbn; lia). cbn [map length].
  unfold te_tappath_regs. rewrite (te_st_bytes pb (extTappath e) HP _ (le_n _)), firstn_all.
  rewrite loop_bytes_length, map_length.
  replace (64 * 0 + Z.of_nat 0 + Z.of_nat (Nat.pow 2 5 * length (extTappath e)))
    with (32 * Z.of_nat (length (extTappath e))) by (change (Nat.pow 2 5) with 32%nat; lia).
  apply mk_hash256_reg.
  refine (proj2 (proj2 (absorb_i_len _ _ _ _ _))).
  - refine (proj1 (proj2 (absorb_i_len _ [] sha256_iv_words _ eq_refl))). cbn. lia.
  - refine (proj2 (proj2 (absorb_i_len _ [] sha256_iv_words _ eq_refl))). cbn. lia.
Qed.

(** ** The tap environment hash *)

Lemma norm8_id (R : list int) : length R = 8%nat -> norm8 R = R.
Proof.
  intros H. do 9 (destruct R as [|? R]; try discriminate). reflexivity.
Qed.

Lemma counter96 :
  Int64.add (Int64.add (Int64.add Int64.zero (Int64.repr 32)) (Int64.repr 32)) (Int64.repr 32) = Int64.repr 96.
Proof. apply Int64.same_if_eq. vm_compute. reflexivity. Qed.

Theorem tap_env_hash_link (e : ext_environment) :
  hash256_reg (tap_env_hash_of e) =
    te_tapenv_regs (hash256_reg (tapleaf_hash_of e)) (hash256_reg (words_hash_of 5 3 (tappath_of e)))
      (hash256_reg (extInternalKey e)).
Proof.
  unfold tap_env_hash_of, sha256_bytes_of.
  rewrite sha_stream_absorb_i by (cbn; lia). cbn [map length].
  unfold te_tapenv_regs. cbv zeta.
  rewrite !norm8_id by apply hash256_len. rewrite !reg_bytes, counter96.
  rewrite <- !absorb_i_app.
  assert (HB : map word8_array_value
      (vector_values (Word 3) 5 (from_hash256 (tapleaf_hash_of e)) ++
       vector_values (Word 3) 6
         (from_hash256 (words_hash_of 5 3 (tappath_of e)), from_hash256 (extInternalKey e))) =
    (map word8_array_value (vector_values (Word 3) 5 (from_hash256 (tapleaf_hash_of e))) ++
     map word8_array_value (vector_values (Word 3) 5 (from_hash256 (words_hash_of 5 3 (tappath_of e))))) ++
    map word8_array_value (vector_values (Word 3) 5 (from_hash256 (extInternalKey e)))).
  { rewrite <- app_assoc, <- !map_app. reflexivity. }
  rewrite HB.
  assert (HLen : Z.of_nat (length
      (vector_values (Word 3) 5 (from_hash256 (tapleaf_hash_of e)) ++
       vector_values (Word 3) 6
         (from_hash256 (words_hash_of 5 3 (tappath_of e)), from_hash256 (extInternalKey e)))) = 96).
  { rewrite app_length, !vector_values_length. reflexivity. }
  rewrite HLen. change (64 * 0 + Z.of_nat 0 + 96) with 96.
  apply mk_hash256_reg.
  refine (proj2 (proj2 (absorb_i_len _ [] sha256_iv_words _ eq_refl))). cbn. lia.
Qed.

(** ** The cached hashes of the allocated taproot environment

    A logical environment [e] *describes* the raw data the builder read when
    its leaf version, script CMR, path and internal key are the stored ones.
    For such an [e] the three cached fields hold exactly the values the
    accepted hash-getter relations ([hash_getter_rep ... 8 8 176],
    [... 8 40 176], [... 8 72 176]) require of the taproot structure: the
    relation premise is established by the C code, not assumed. *)
Definition tapenv_describes (e : ext_environment) (nb cb0 : int) (kb cmrb : list int)
    (pb : nat -> list int) : Prop :=
  word8_array_value (@fromZ (WordToZ 3) (extTapleafVersion e)) = Int.and cb0 (Int.repr 254) /\
  state_regs (from_hash256 (Bitcoin.envScriptCMR (extBase e))) = tm_words cmrb /\
  length (extTappath e) = Z.to_nat (Int.unsigned nb) /\
  (forall j h, nth_error (extTappath e) j = Some h -> tm_words (pb j) = hash256_reg h) /\
  hash256_reg (extInternalKey e) = tm_words kb.

Theorem tapenv_cached_hashes (e : ext_environment) m bA nb cb0 kb cmrb pb :
  tapenv_built m bA nb cb0 kb cmrb pb ->
  tapenv_describes e nb cb0 kb cmrb pb ->
  uint32_array_at m bA 8 (hash256_reg (tapleaf_hash_of e)) /\
  uint32_array_at m bA 40 (hash256_reg (words_hash_of 5 3 (tappath_of e))) /\
  uint32_array_at m bA 72 (hash256_reg (tap_env_hash_of e)).
Proof.
  intros (_ & HLeaf & HPath & HEnv & _) (Hv & Hc & HLn & HP & HK).
  cbv zeta in HLeaf, HPath, HEnv.
  pose proof (tapleaf_hash_link e _ _ Hv Hc) as E1.
  pose proof (tappath_hash_link e pb HP) as E2. rewrite HLn in E2.
  pose proof (tap_env_hash_link e) as E3. rewrite E1, E2, HK in E3.
  split; [|split]; apply u32_of_nth; intros i Hi; rewrite hash256_len in Hi.
  - rewrite E1. apply HLeaf, Hi.
  - rewrite E2. apply HPath, Hi.
  - rewrite E3. apply HEnv, Hi.
Qed.

(** The headline statement: the actual builder establishes the cached-hash
    premises of the accepted relations. *)
Theorem mallocTapEnv_cached_hashes (Hmodel : jet_memcpy_model.memcpy_model) (e : ext_environment)
    m braw oraw bcb ocb bcm ocm (nb cb0 : int) (kb cmrb : list int) (pb : nat -> list int) :
  0 <= oraw /\ oraw + 24 <= Ptrofs.max_unsigned ->
  0 <= Int.unsigned nb <= 128 ->
  Memory.Mem.load AST.Mptr m braw oraw = Some (Values.Vptr bcb ocb) ->
  Memory.Mem.load AST.Mptr m braw (oraw + 8) = Some (Values.Vptr bcm ocm) ->
  Memory.Mem.load AST.Mint8unsigned m braw (oraw + 16) = Some (Values.Vint nb) ->
  Ptrofs.unsigned ocb + 33 + 32 * Int.unsigned nb <= Ptrofs.max_unsigned ->
  Memory.Mem.load AST.Mint8unsigned m bcb (Ptrofs.unsigned ocb) = Some (Values.Vint cb0) ->
  (forall i, (i < 32)%nat ->
     Memory.Mem.load AST.Mint8unsigned m bcb (Ptrofs.unsigned ocb + 1 + Z.of_nat i) =
       Some (Values.Vint (nth i kb Int.zero))) ->
  (forall j i, (j < Z.to_nat (Int.unsigned nb))%nat -> (i < 32)%nat ->
     Memory.Mem.load AST.Mint8unsigned m bcb (Ptrofs.unsigned ocb + 33 + 32 * Z.of_nat j + Z.of_nat i) =
       Some (Values.Vint (nth i (pb j) Int.zero))) ->
  Ptrofs.unsigned ocm + 32 <= Ptrofs.max_unsigned ->
  (forall i, (i < 32)%nat ->
     Memory.Mem.load AST.Mint8unsigned m bcm (Ptrofs.unsigned ocm + Z.of_nat i) =
       Some (Values.Vint (nth i cmrb Int.zero))) ->
  sha_dispatch_ok m ->
  Memory.Mem.load AST.Mint64 m (jet_sha_linkage.sha_symbol_block jets_sha._sha256_max_counter) 0 =
    Some (Values.Vlong sha_max_counter) ->
  sha_tapleaf_tag_ok m ->
  tapenv_describes e nb cb0 kb cmrb pb ->
  exists m' bA,
    ClightBigstep.Clight2.eval_funcall jet_sha_linkage.sha_ge m
      (Ctypes.Internal jets_sha.f_simplicity_bitcoin_mallocTapEnv)
      [Values.Vptr braw (Ptrofs.repr oraw)] Events.E0 m' (Values.Vptr bA Ptrofs.zero) /\
    ~ Memory.Mem.valid_block m bA /\
    uint32_array_at m' bA 8 (hash256_reg (tapleaf_hash_of e)) /\
    uint32_array_at m' bA 40 (hash256_reg (words_hash_of 5 3 (tappath_of e))) /\
    uint32_array_at m' bA 72 (hash256_reg (tap_env_hash_of e)) /\
    (forall ch b ofs, Memory.Mem.valid_block m b -> Memory.Mem.load ch m' b ofs = Memory.Mem.load ch m b ofs).
Proof.
  intros H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 HD.
  destruct (eval_mallocTapEnv Hmodel m braw oraw bcb ocb bcm ocm nb cb0 kb cmrb pb
    H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14) as (m' & bA & HCall & HFresh & HBuilt & HL & _).
  destruct (tapenv_cached_hashes e m' bA nb cb0 kb cmrb pb HBuilt HD) as (A & B & C).
  exists m', bA. repeat (split; [assumption|]). exact HL.
Qed.
