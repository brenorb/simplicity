(** The actual writable Bitcoin TapTweak tag and its canonical SHA values. *)
From Coq Require Import ZArith List Lia Strings.String.
From compcert Require Import Integers AST Ctypes Clight Memory Globalenvs Values.
Require sha.SHA256 sha.functional_prog sha.general_lemmas.
Require Import Simplicity.Digest Simplicity.Word
 C.jets_secp C.jet_secp_linkage C.jet_sx_mem C.jet_clight_forward C.jet_read8s_layout
 C.jet_secp_sha_owned C.jet_secp_sha_hash32 C.jet_sha256_iv_init C.jet_sha_ctx8_model
 C.jet_sha_finalize_exec C.jet_sha_be32_write C.jet_secp_schnorr_startup
 C.jet_entropy_streaming_byte_blocks C.jet_sha_hash_exec.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.
Set Default Timeout 10.
Definition taptweak_tag_bytes:list int:=map Int.repr [84;97;112;84;119;101;97;107].
Definition taptweak_tag_digest:=Digest.stringHash "TapTweak".
Definition taptweak_tag_iv:=Digest.compress Digest.sha256_iv taptweak_tag_digest taptweak_tag_digest.
Definition taptweak_iv_word:=Word.from_hash256 taptweak_tag_iv.
Lemma taptweak_tag_length:List.length taptweak_tag_bytes=8%nat.
Proof. reflexivity. Qed.
Lemma taptweak_tag_padded_words:
 be_words (taptweak_tag_bytes++sha_pad (Int64.repr 8))=
 SHA256.generate_and_pad (SHA256.str_to_bytes "TapTweak").
Proof. vm_compute;reflexivity. Qed.
Lemma taptweak_tag_regs:
 SHA256.hash_block sha256_iv_words (be_words (taptweak_tag_bytes++sha_pad (Int64.repr 8)))=
 Digest.hash256_reg taptweak_tag_digest.
Proof.
 unfold taptweak_tag_digest,Digest.stringHash,Digest.byteStringHash;cbn [Digest.hash256_reg].
 rewrite <-sha.functional_prog.generate_and_pad'_eq.
 rewrite sha.functional_prog.process_msg_hash_blocks.
 - rewrite <-taptweak_tag_padded_words,<-sha256_iv_words_registers.
   pose proof (hash_blocks_app sha256_iv_words
     (be_words (taptweak_tag_bytes++sha_pad (Int64.repr 8))) [] eq_refl) as Single.
   rewrite app_nil_r in Single;rewrite Single,SHA256.hash_blocks_equation;reflexivity.
 - rewrite sha.functional_prog.length_generate_and_pad;apply sha.functional_prog.roundup_divide;lia.
 - reflexivity.
Qed.
Lemma taptweak_iv_regs:
 SHA256.hash_block sha256_iv_words (be_words
  (secp_hash_bytes (Digest.hash256_reg taptweak_tag_digest)++secp_hash_bytes (Digest.hash256_reg taptweak_tag_digest)))=
 Digest.hash256_reg taptweak_tag_iv.
Proof.
 rewrite !secp_hash_bytes_value.
 unfold C.jet_sha_be32_write.be_bytes;rewrite <-flat_map_app,be_words_be_bytes.
 unfold taptweak_tag_iv,Digest.compress;cbn [Digest.hash256_reg].
 rewrite sha.functional_prog.process_block_hash_block;
 [rewrite sha256_iv_words_registers;reflexivity|reflexivity|rewrite app_length,!Digest.hash256_len;reflexivity].
Qed.
Lemma taptweak_iv_word_regs:state_regs taptweak_iv_word=Digest.hash256_reg taptweak_tag_iv.
Proof.
 unfold state_regs;rewrite <-hash256_reg_chunks;unfold taptweak_iv_word;rewrite Word.to_from_hash256;reflexivity.
Qed.
Definition taptweak_tag_block:=secp_symbol_block _taptweak.
Definition taptweak_tag_ok m:=uint8_array_at m taptweak_tag_block 0 taptweak_tag_bytes /\
 Mem.range_perm m taptweak_tag_block 0 9 Cur Readable /\
 (forall pos kind p,Mem.perm m taptweak_tag_block pos kind p ->0<=pos<9 /\perm_order Writable p).
Lemma taptweak_tag_info:Genv.find_var_info (Genv.globalenv jets_secp.prog) taptweak_tag_block=Some v_taptweak.
Proof. vm_compute;reflexivity. Qed.
Lemma taptweak_tag_symbol:Genv.find_symbol secp_ge _taptweak=Some taptweak_tag_block.
Proof. vm_compute;reflexivity. Qed.
Local Opaque secp_ge taptweak_tag_block.
Theorem taptweak_tag_initial m:Genv.init_mem jets_secp.prog=Some m ->taptweak_tag_ok m.
Proof.
 intro Init;destruct (Genv.init_mem_characterization jets_secp.prog taptweak_tag_block taptweak_tag_info Init)
 as (Perm & Bounds & Loads & _).
 change (Mem.range_perm m taptweak_tag_block 0 9 Cur Writable) in Perm.
 specialize (Loads eq_refl).
 change (Mem.load Mint8unsigned m taptweak_tag_block 0=Some (Vint (Int.repr 84)) /\
 Mem.load Mint8unsigned m taptweak_tag_block 1=Some (Vint (Int.repr 97)) /\
 Mem.load Mint8unsigned m taptweak_tag_block 2=Some (Vint (Int.repr 112)) /\
 Mem.load Mint8unsigned m taptweak_tag_block 3=Some (Vint (Int.repr 84)) /\
 Mem.load Mint8unsigned m taptweak_tag_block 4=Some (Vint (Int.repr 119)) /\
 Mem.load Mint8unsigned m taptweak_tag_block 5=Some (Vint (Int.repr 101)) /\
 Mem.load Mint8unsigned m taptweak_tag_block 6=Some (Vint (Int.repr 97)) /\
 Mem.load Mint8unsigned m taptweak_tag_block 7=Some (Vint (Int.repr 107)) /\
 Mem.load Mint8unsigned m taptweak_tag_block 8=Some (Vint Int.zero) /\True) in Loads.
 split.
 - intros i v Nth;destruct i as [|[|[|[|[|[|[|[|i]]]]]]]];
   cbn [taptweak_tag_bytes map nth_error] in Nth;
   try (destruct i;discriminate Nth);injection Nth as Same;subst v;cbn [Z.of_nat Z.add];tauto.
 - split.
   + intros pos Range;eapply Mem.perm_implies;[apply Perm;exact Range|constructor].
   + intros pos kind p Permission;exact (Bounds pos kind p Permission).
Qed.
Theorem taptweak_tag_owned_separate m b size:taptweak_tag_ok m ->0<size ->Mem.range_perm m b 0 size Cur Freeable ->b<>taptweak_tag_block.
Proof.
 intros [_ [_ Bounds]] Positive Free Same;subst b.
 pose proof (proj2 (Bounds 0 Cur Freeable (Free 0 ltac:(clear -Positive;lia)))) as Order;inversion Order.
Qed.
Theorem taptweak_tag_framed m mf P:taptweak_tag_ok m ->mem_forward m mf ->lframe P m mf ->
 (forall pos,P taptweak_tag_block pos) ->taptweak_tag_ok mf.
Proof.
 intros (Bytes & Perm & Bounds) Forward Frame Outside.
 assert (Valid:Mem.valid_block m taptweak_tag_block) by (eapply Mem.perm_valid_block;apply (Perm 0);clear;lia).
 split.
 - intros i v Nth;rewrite (proj1 Frame Mint8unsigned taptweak_tag_block (0+Z.of_nat i) Valid);
   [apply Bytes;exact Nth|intros;apply Outside].
 - split.
   + intros pos Range;apply (proj1 (proj2 Frame));[exact Valid|apply Outside|apply Perm;exact Range].
   + intros pos kind p Permission;apply (Bounds pos Max p).
     apply (proj2 (Forward _ Valid) pos p);destruct kind;first [exact Permission|eapply Mem.perm_cur_max;exact Permission].
Qed.
Definition taptweak_startup m:=schnorr_startup m /\taptweak_tag_ok m.
Theorem taptweak_startup_initial m:Genv.init_mem jets_secp.prog=Some m ->taptweak_startup m.
Proof. intro Init;split;[apply schnorr_startup_initial|apply taptweak_tag_initial];exact Init. Qed.
Theorem taptweak_startup_exists:exists m,Genv.init_mem jets_secp.prog=Some m /\taptweak_startup m.
Proof.
 destruct schnorr_startup_exists as (m & Init & _);exists m;split;[exact Init|apply taptweak_startup_initial;exact Init].
Qed.
Theorem taptweak_startup_framed m mf:taptweak_startup m ->mem_forward m mf ->lframe (fun _ _=>True) m mf ->taptweak_startup mf.
Proof.
 intros [Schnorr Tag] Forward Frame;split.
 - eapply schnorr_startup_framed;[exact Schnorr|exact Forward|exact Frame].
 - eapply taptweak_tag_framed;[exact Tag|exact Forward|exact Frame|intros;exact I].
Qed.

Theorem taptweak_startup_owned_forward m mf (slots:list (block*Z)):
 taptweak_startup m ->mem_forward m mf ->
 (forall b hi,In (b,hi) slots ->0<hi /\Mem.range_perm m b 0 hi Cur Freeable) ->
 lframe (fun b _=>~In b (map fst slots)) m mf ->taptweak_startup mf.
Proof.
 intros [Schnorr Tag] Forward Owned Frame;split.
 - eapply schnorr_startup_owned_forward;[exact Schnorr|exact Forward|exact Owned|exact Frame].
 - eapply taptweak_tag_framed;[exact Tag|exact Forward|exact Frame|].
   intros pos Member;apply in_map_iff in Member as ([b hi] & Same & Slot);cbn in Same;subst b.
   destruct (Owned _ hi Slot) as [Positive Free].
   exact (taptweak_tag_owned_separate m taptweak_tag_block hi Tag Positive Free eq_refl).
Qed.
