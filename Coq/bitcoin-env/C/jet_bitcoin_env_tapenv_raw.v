(** The taproot environment built by [simplicity_bitcoin_mallocTapEnv]
    against the raw-data meaning of the Bitcoin environment
    ([C.jet_bitcoin_raw_env]): when the control block and script CMR the
    builder reads are those of a raw environment [R], the logical environment
    [project_raw_environment R] is described by them, so the three cached
    hash fields are the canonical hashes of [R]. *)
From Coq Require Import ZArith List Lia PeanoNat.
From compcert Require Import Integers.
Require sha.SHA256.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest.
Require Import Simplicity.Primitive.Bitcoin.
Require Import C.jet_word_repr C.jet_read8s_layout C.jet_word32_chunks.
Require Import C.jet_bitcoin_ext_prim C.jet_bitcoin_raw_env.
Require Import C.jet_sha_ctx8_model C.jet_sha_hash_closed C.jet_uint32_array_init.
Require Import C.jet_bitcoin_words_hash C.jet_bitcoin_tapleaf_hash_spec C.jet_bitcoin_tapleaf_hash_local C.jet_bitcoin_composite_hash.
Require Import C.jet_bitcoin_env_tomidstate C.jet_bitcoin_env_tapenv C.jet_bitcoin_env_tapenv_link.
Require Import C.jet_bitcoin_env_tapenv_describe C.jet_bitcoin_env_bytestring.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 120.

(** The bytes the builder reads are those of the raw environment [R]. *)
Definition raw_tapenv_holds (R : raw_bitcoin_environment) (nb cb0 : int) (kb cmrb : list int)
    (pb : nat -> list int) : Prop :=
  byte_int (raw_leaf_version R) = Int.and cb0 (Int.repr 254) /\
  hash256_reg (Bitcoin.envScriptCMR (raw_base R)) = tm_words cmrb /\
  length (raw_tap_path R) = Z.to_nat (Int.unsigned nb) /\
  (forall j h, nth_error (raw_tap_path R) j = Some h -> tm_words (pb j) = hash256_reg h) /\
  hash256_reg (raw_internal_key R) = tm_words kb.

Lemma byte_word_value (b : byte) :
  word8_array_value (@fromZ (WordToZ 3) (Byte.unsigned b)) = byte_int b.
Proof.
  pose proof (Byte.unsigned_range b) as HR. change Byte.modulus with 256 in HR.
  unfold word8_array_value, byte_int.
  rewrite to_fromZ, two_power_nat_equiv, word_bitSize.
  change (2 ^ Z.of_nat (Nat.pow 2 3)) with 256. rewrite Z.mod_small by exact HR. reflexivity.
Qed.

Lemma state_regs_hash (h : hash256) : state_regs (from_hash256 h) = hash256_reg h.
Proof. unfold state_regs. rewrite <- hash256_reg_chunks, to_from_hash256. reflexivity. Qed.

Theorem raw_tapenv_describes (R : raw_bitcoin_environment) (Hpath : (length (raw_tap_path R) <= 128)%nat)
    nb cb0 kb cmrb pb :
  raw_tapenv_holds R nb cb0 kb cmrb pb ->
  tapenv_describes (project_raw_environment R Hpath) nb cb0 kb cmrb pb.
Proof.
  intros (Hv & Hc & HL & HP & HK). unfold tapenv_describes.
  cbn [project_raw_environment extBase extTapleafVersion extTappath extInternalKey].
  split; [rewrite byte_word_value; exact Hv|].
  split; [rewrite state_regs_hash; exact Hc|].
  split; [exact HL|]. split; [exact HP|exact HK].
Qed.

(** The headline statement against raw data. *)
Theorem mallocTapEnv_raw_cached_hashes (Hmodel : jet_memcpy_model.memcpy_model)
    (R : raw_bitcoin_environment) (Hpath : (length (raw_tap_path R) <= 128)%nat)
    m braw oraw bcb ocb bcm ocm (nb cb0 : int) (kb cmrb : list int) (pb : nat -> list int) :
  let e := project_raw_environment R Hpath in
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
  jet_sha_block_local.sha_dispatch_ok m ->
  Memory.Mem.load AST.Mint64 m (jet_sha_linkage.sha_symbol_block jets_sha._sha256_max_counter) 0 =
    Some (Values.Vlong jet_sha_uchars_exec.sha_max_counter) ->
  jet_bitcoin_make_tapleaf_exec.sha_tapleaf_tag_ok m ->
  raw_tapenv_holds R nb cb0 kb cmrb pb ->
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
  intros e H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 HR.
  exact (mallocTapEnv_cached_hashes Hmodel e m braw oraw bcb ocb bcm ocm nb cb0 kb cmrb pb
    H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 (raw_tapenv_describes R Hpath nb cb0 kb cmrb pb HR)).
Qed.
