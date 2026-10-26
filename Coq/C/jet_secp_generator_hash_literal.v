(** The two SHA expressions inside canonical LibSecp256k1.hash_to_curve_core
    (Haskell/Core/Simplicity/Programs/LibSecp256k1.hs:729--738).
    Connect their exact block layout to the original generator's computed
    registers; this is an internal bridge, not whole-jet coverage. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Simplicity.SHA256.
Require Import C.jet_buffer_input C.jet_read8s_layout C.jet_sha_ctx8_model
  C.jet_sha256_iv_init C.jet_sha_finalize_exec C.jet_secp_generator_sha_absorb
  C.jet_secp_generator_sha_complete C.jet_secp_input_bytes C.jet_secp_swu_raw_input
  C.jet_secp_sha_owned C.jet_secp_fe_math C.jet_word_repr C.jet_bitcoin_build_tapleaf_spec
  C.jet_vector_shift_word C.jet_full_shift_spec.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope term_scope.
Set Default Timeout 10.

Definition generator_hash_prefix (second:bool) : Ty.tySem (Word 7) :=
  @fromZ (WordToZ 7) (if second then 0x326e642067656e65726174696f6e3a20
    else 0x3173742067656e65726174696f6e3a20).
Definition generator_hash_postfix : Ty.tySem (Word 7) :=
  @fromZ (WordToZ 7) (2^127+128+256).
Definition generator_hash_block second (key:Ty.tySem (Word 8)) : Ty.tySem (Word 9) :=
  ((generator_hash_prefix second,fst key),(snd key,generator_hash_postfix)).
Definition literal_generator_hash second {term:Alg.Core.Algebra} : term (Word 8) (Word 8) :=
  (unit >>> @sha256_iv_spec term) &&&
    ((Alg.scribe (generator_hash_prefix second) &&& O H) &&&
      (I H &&& Alg.scribe generator_hash_postfix)) >>> @Simplicity.SHA256.hashBlock term.

Lemma literal_generator_hash_parametric second : Alg.Core.Parametric (@literal_generator_hash second).
Proof.
  intros t1 t2 R;unfold literal_generator_hash.
  repeat first [apply Simplicity.SHA256.hashBlock_Parametric|apply sha256_iv_spec_parametric|
    apply Alg.scribe_Parametric|apply Alg.comp_Parametric|apply Alg.pair_Parametric|
    apply Alg.take_Parametric|apply Alg.drop_Parametric|apply Alg.iden_Parametric|apply Alg.unit_Parametric].
Qed.
Lemma literal_generator_hash_step second key :
  @literal_generator_hash second Alg.CoreFunSem key=
  @Simplicity.SHA256.hashBlock Alg.CoreFunSem
    (@sha256_iv_spec Alg.CoreFunSem tt,generator_hash_block second key).
Proof.
  unfold literal_generator_hash,generator_hash_block.
  change (@Simplicity.SHA256.hashBlock Alg.CoreFunSem
    (@sha256_iv_spec Alg.CoreFunSem tt,
      ((@Alg.scribe _ _ (generator_hash_prefix second) Alg.CoreFunSem key,fst key),
       (snd key,@Alg.scribe _ _ generator_hash_postfix Alg.CoreFunSem key)))=
    @Simplicity.SHA256.hashBlock Alg.CoreFunSem
      (@sha256_iv_spec Alg.CoreFunSem tt,
       ((generator_hash_prefix second,fst key),(snd key,generator_hash_postfix)))).
  rewrite !Alg.scribe_correct;reflexivity.
Qed.
Lemma generator_hash_prefix_bytes second :
  map word8_array_value (vector_values (Word 3) 4 (generator_hash_prefix second))=
    generator_sha_prefix_bytes second.
Proof. destruct second;vm_compute;reflexivity. Qed.
Lemma generator_hash_postfix_bytes :
  map word8_array_value (vector_values (Word 3) 4 generator_hash_postfix)=sha_pad (Int64.repr 48).
Proof. vm_compute;reflexivity. Qed.
Lemma generator_hash_iv_regs : state_regs (@sha256_iv_spec Alg.CoreFunSem tt)=sha256_iv_words.
Proof. vm_compute;reflexivity. Qed.

Lemma generator_hash_block_bytes second key :
  map word8_array_value (vector_values (Word 3) 6 (generator_hash_block second key))=
    generator_sha_prefix_bytes second++
      map word8_array_value (vector_values (Word 3) 5 key)++sha_pad (Int64.repr 48).
Proof.
  unfold generator_hash_block.
  change (map word8_array_value
    ((vector_values (Word 3) 4 (generator_hash_prefix second)++vector_values (Word 3) 4 (fst key))++
     (vector_values (Word 3) 4 (snd key)++vector_values (Word 3) 4 generator_hash_postfix))=
    generator_sha_prefix_bytes second++
      map word8_array_value (vector_values (Word 3) 4 (fst key)++vector_values (Word 3) 4 (snd key))++
      sha_pad (Int64.repr 48)).
  rewrite !map_app,generator_hash_prefix_bytes,generator_hash_postfix_bytes,!app_assoc;reflexivity.
Qed.
Theorem generator_sha_regs_literal second (key:Ty.tySem (Word 8)) :
  generator_sha_regs second (map word8_array_value (vector_values (Word 3) 5 key))=
    state_regs (@literal_generator_hash second Alg.CoreFunSem key).
Proof.
  rewrite literal_generator_hash_step,hashBlock_regs,generator_hash_iv_regs,generator_hash_block_bytes.
  reflexivity.
Qed.

Lemma generator_bytes_value_app left right :
  be_val (left++right)=be_val left*256^Z.of_nat (length right)+be_val right.
Proof. unfold be_val at 1;rewrite fold_left_app;apply fold_be_linear. Qed.

Lemma generator_word_bytes_value n (w:Ty.tySem (Vector (Word 3) n)) :
  be_val (map Int.unsigned (map word8_array_value (vector_values (Word 3) n w)))=
    vector_value (WordToZ 3) n w.
Proof.
  revert w;induction n as [|n IH];intro w.
  - change (Int.unsigned (Int.repr (@toZ (WordToZ 3) w))=@toZ (WordToZ 3) w).
    apply Int.unsigned_repr;pose proof (word_toZ_range 3 w) as Bound.
    change (0<=@toZ (WordToZ 3) w<256) in Bound.
    change Int.max_unsigned with 4294967295;lia.
  - destruct w as [hi lo].
    change (be_val (map Int.unsigned (map word8_array_value
      (vector_values (Word 3) n hi++vector_values (Word 3) n lo)))=
      vector_value (WordToZ 3) n hi*two_power_nat (vector_bits (WordToZ 3) n)+
      vector_value (WordToZ 3) n lo).
    rewrite !map_app,generator_bytes_value_app,!map_length,vector_values_length,!IH.
    rewrite vector_word_bits,two_power_nat_equiv,word_bitSize.
    replace (Nat.pow 2 (n+3)) with (8*Nat.pow 2 n)%nat by
      (rewrite Nat.pow_add_r;cbn;lia).
    rewrite Nat2Z.inj_mul,Z.pow_mul_r by lia;reflexivity.
Qed.

Lemma generator_word256_bytes_value (w:Ty.tySem (Word 8)) :
  be_val (map Int.unsigned (map word8_array_value (vector_values (Word 3) 5 w)))=
    @toZ (WordToZ 8) w.
Proof.
  rewrite generator_word_bytes_value.
  pose proof (vector_word_value 3 5 w) as Value.
  change (@toZ (WordToZ 8) w=vector_value (WordToZ 3) 5 w) in Value.
  symmetry;exact Value.
Qed.

Lemma generator_digest_state_word (h:Ty.tySem (Word 8)) :
  swu_digest_word (secp_sha_digest_bytes (state_regs h))=h.
Proof.
  unfold swu_digest_word,secp_sha_digest_bytes;rewrite be_bytes_state_regs.
  rewrite generator_word256_bytes_value;apply from_toZ.
Qed.

Theorem generator_digest_word_literal second (key:Ty.tySem (Word 8)) :
  swu_digest_word (secp_sha_digest_bytes
    (generator_sha_regs second (map word8_array_value (vector_values (Word 3) 5 key))))=
    @literal_generator_hash second Alg.CoreFunSem key.
Proof. rewrite generator_sha_regs_literal;apply generator_digest_state_word. Qed.

Theorem generator_digest_value_literal second (key:Ty.tySem (Word 8)) :
  be_val (secp_sha_digest_bytes
    (generator_sha_regs second (map word8_array_value (vector_values (Word 3) 5 key))))=
    @toZ (WordToZ 8) (@literal_generator_hash second Alg.CoreFunSem key).
Proof.
  rewrite generator_sha_regs_literal;unfold secp_sha_digest_bytes;rewrite be_bytes_state_regs.
  apply generator_word256_bytes_value.
Qed.
