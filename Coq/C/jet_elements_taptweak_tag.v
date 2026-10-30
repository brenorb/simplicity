(** Elements' frozen TapTweak tag and its canonical runtime SHA digest/IV. *)
From Coq Require Import ZArith List Lia Strings.String.
From compcert Require Import Integers AST Ctypes Clight Memory Globalenvs Values.
Require sha.SHA256 sha.functional_prog sha.general_lemmas.
Require Import Simplicity.Digest Simplicity.Word
 C.jets_elements C.jet_elements_linkage C.jet_sx_mem C.jet_read8s_layout
 C.jet_secp_taptweak_tag_runtime C.jet_secp_sha_owned C.jet_secp_sha_hash32
 C.jet_sha256_iv_init C.jet_sha_ctx8_model C.jet_sha_finalize_exec C.jet_sha_be32_write
 C.jet_secp_schnorr_challenge_hash C.jet_entropy_streaming_byte_blocks C.jet_sha_hash_exec.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.
Set Default Timeout 10.
Definition elements_taptweak_tag_bytes:list int:=map Int.repr
 [84;97;112;84;119;101;97;107;47;101;108;101;109;101;110;116;115].
Definition elements_taptweak_tag_digest:=Digest.stringHash "TapTweak/elements".
Definition elements_taptweak_tag_iv:=Digest.compress Digest.sha256_iv elements_taptweak_tag_digest elements_taptweak_tag_digest.
Definition elements_taptweak_iv_word:=Word.from_hash256 elements_taptweak_tag_iv.
Lemma elements_taptweak_tag_length:List.length elements_taptweak_tag_bytes=17%nat.
Proof. reflexivity. Qed.
Lemma elements_taptweak_tag_padded_words:
 be_words (elements_taptweak_tag_bytes++sha_pad (Int64.repr 17))=
 SHA256.generate_and_pad (SHA256.str_to_bytes "TapTweak/elements").
Proof. vm_compute;reflexivity. Qed.
Lemma elements_taptweak_tag_regs:
 short_tag_regs elements_taptweak_tag_bytes=Digest.hash256_reg elements_taptweak_tag_digest.
Proof.
 unfold short_tag_regs;rewrite elements_taptweak_tag_length.
 change (SHA256.hash_block sha256_iv_words (be_words (elements_taptweak_tag_bytes++sha_pad (Int64.repr 17)))=
 Digest.hash256_reg elements_taptweak_tag_digest).
 unfold elements_taptweak_tag_digest,Digest.stringHash,Digest.byteStringHash;cbn [Digest.hash256_reg].
 rewrite <-sha.functional_prog.generate_and_pad'_eq.
 rewrite sha.functional_prog.process_msg_hash_blocks.
 - rewrite <-elements_taptweak_tag_padded_words,<-sha256_iv_words_registers.
   pose proof (hash_blocks_app sha256_iv_words
    (be_words (elements_taptweak_tag_bytes++sha_pad (Int64.repr 17))) [] eq_refl) as Single.
   rewrite app_nil_r in Single;rewrite Single,SHA256.hash_blocks_equation;reflexivity.
 - rewrite sha.functional_prog.length_generate_and_pad;apply sha.functional_prog.roundup_divide;lia.
 - reflexivity.
Qed.
Lemma elements_taptweak_iv_regs:
 SHA256.hash_block sha256_iv_words (be_words
  (secp_hash_bytes (Digest.hash256_reg elements_taptweak_tag_digest)++secp_hash_bytes (Digest.hash256_reg elements_taptweak_tag_digest)))=
 Digest.hash256_reg elements_taptweak_tag_iv.
Proof.
 rewrite !secp_hash_bytes_value.
 unfold C.jet_sha_be32_write.be_bytes;rewrite <-flat_map_app,be_words_be_bytes.
 unfold elements_taptweak_tag_iv,Digest.compress;cbn [Digest.hash256_reg].
 rewrite sha.functional_prog.process_block_hash_block;
 [rewrite sha256_iv_words_registers;reflexivity|reflexivity|rewrite app_length,!Digest.hash256_len;reflexivity].
Qed.
Lemma elements_taptweak_iv_word_regs:state_regs elements_taptweak_iv_word=Digest.hash256_reg elements_taptweak_tag_iv.
Proof.
 unfold state_regs;rewrite <-hash256_reg_chunks;unfold elements_taptweak_iv_word;rewrite Word.to_from_hash256;reflexivity.
Qed.
Definition elements_taptweak_tag_block:=elements_symbol_block jets_elements._taptweak.
Lemma elements_taptweak_tag_info:Genv.find_var_info (Genv.globalenv jets_elements.prog)
 elements_taptweak_tag_block=Some jets_elements.v_taptweak.
Proof. vm_compute;reflexivity. Qed.
Lemma elements_taptweak_tag_symbol:Genv.find_symbol elements_ge jets_elements._taptweak=Some elements_taptweak_tag_block.
Proof. vm_compute;reflexivity. Qed.

Definition elements_taptweak_tag_state m:=
 uint8_array_at m elements_taptweak_tag_block 0 elements_taptweak_tag_bytes /\
 Mem.load Mint8unsigned m elements_taptweak_tag_block 17=Some (Vint Int.zero) /\
 Mem.range_perm m elements_taptweak_tag_block 0 18 Cur Readable /\
 (forall pos kind p,Mem.perm m elements_taptweak_tag_block pos kind p ->0<=pos<18 /\perm_order Writable p).
Local Opaque elements_ge elements_taptweak_tag_block.
Theorem elements_taptweak_tag_initial m:Genv.init_mem jets_elements.prog=Some m ->elements_taptweak_tag_state m.
Proof.
 intro Init;destruct (Genv.init_mem_characterization jets_elements.prog elements_taptweak_tag_block elements_taptweak_tag_info Init)
 as (Perm & Bounds & Loads & _).
 change (Mem.range_perm m elements_taptweak_tag_block 0 18 Cur Writable) in Perm.
 specialize (Loads eq_refl).
 change (Mem.load Mint8unsigned m elements_taptweak_tag_block 0=Some (Vint (Int.repr 84)) /\
 Mem.load Mint8unsigned m elements_taptweak_tag_block 1=Some (Vint (Int.repr 97)) /\
 Mem.load Mint8unsigned m elements_taptweak_tag_block 2=Some (Vint (Int.repr 112)) /\
 Mem.load Mint8unsigned m elements_taptweak_tag_block 3=Some (Vint (Int.repr 84)) /\
 Mem.load Mint8unsigned m elements_taptweak_tag_block 4=Some (Vint (Int.repr 119)) /\
 Mem.load Mint8unsigned m elements_taptweak_tag_block 5=Some (Vint (Int.repr 101)) /\
 Mem.load Mint8unsigned m elements_taptweak_tag_block 6=Some (Vint (Int.repr 97)) /\
 Mem.load Mint8unsigned m elements_taptweak_tag_block 7=Some (Vint (Int.repr 107)) /\
 Mem.load Mint8unsigned m elements_taptweak_tag_block 8=Some (Vint (Int.repr 47)) /\
 Mem.load Mint8unsigned m elements_taptweak_tag_block 9=Some (Vint (Int.repr 101)) /\
 Mem.load Mint8unsigned m elements_taptweak_tag_block 10=Some (Vint (Int.repr 108)) /\
 Mem.load Mint8unsigned m elements_taptweak_tag_block 11=Some (Vint (Int.repr 101)) /\
 Mem.load Mint8unsigned m elements_taptweak_tag_block 12=Some (Vint (Int.repr 109)) /\
 Mem.load Mint8unsigned m elements_taptweak_tag_block 13=Some (Vint (Int.repr 101)) /\
 Mem.load Mint8unsigned m elements_taptweak_tag_block 14=Some (Vint (Int.repr 110)) /\
 Mem.load Mint8unsigned m elements_taptweak_tag_block 15=Some (Vint (Int.repr 116)) /\
 Mem.load Mint8unsigned m elements_taptweak_tag_block 16=Some (Vint (Int.repr 115)) /\
 Mem.load Mint8unsigned m elements_taptweak_tag_block 17=Some (Vint Int.zero) /\True) in Loads.
 split.
 - intros i v Nth;destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]];
   cbn [elements_taptweak_tag_bytes map nth_error] in Nth;
   try (destruct i;discriminate Nth);injection Nth as Same;subst v;cbn [Z.of_nat Z.add];tauto.
 - split;[tauto|];split.
   + intros pos Range;eapply Mem.perm_implies;[apply Perm;exact Range|constructor].
   + intros pos kind p Permission;exact (Bounds pos kind p Permission).
Qed.
Theorem elements_taptweak_tag_owned_separate m b size:elements_taptweak_tag_state m ->0<size ->
 Mem.range_perm m b 0 size Cur Freeable ->b<>elements_taptweak_tag_block.
Proof.
 intros [_ [_ [_ Bounds]]] Positive Free Same;subst b.
 pose proof (proj2 (Bounds 0 Cur Freeable (Free 0 ltac:(clear -Positive;lia)))) as Order;inversion Order.
Qed.
