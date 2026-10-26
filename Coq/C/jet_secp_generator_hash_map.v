(** The actual three-statement SHA/conversion/SWU spans of the original
    generator. All digests execute the mapper, including rejected ones.
    Preserve the input key and both families' startup state for the next
    generator stage. The deferred ctz call premise remains explicit. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg.
Require Import C.extraMath C.jet_memcpy_model C.jet_sx_mem C.jet_sx_zval
  C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_fe_math
  C.jet_secp_field_cmov C.jet_secp_square_columns C.jet_secp_multiply_normalize_bridge
  C.jet_secp_rescale_literal C.jet_secp_swu_raw_input C.jet_secp_swu_word_parity
  C.jet_secp_swu_literal C.jet_secp_swu_startup C.jet_secp_curve_statements
  C.jet_secp_curve_frame C.jet_secp_statement_prefix C.jet_clight_internal_preserve
  C.jet_buffer_input C.jet_read8s_layout C.jet_sha_ctx8_model C.jet_secp_sha_owned
  C.jet_secp_sha_startup C.jet_secp_generator_sha_start C.jet_secp_generator_sha_absorb
  C.jet_secp_generator_sha_complete C.jet_secp_generator_hash_literal
  C.jet_secp_generator_digest_mapping.
Import ListNotations Ctypes Values Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge literal_swu rescale_field_output swu_words_literal_output literal_generator_hash.

Definition generator_hash_map_statements second := firstn 3
  (skipn (Nat.pred (generator_digest_index second))
    (fst (split_statement_last (fn_body f_secp256k1_generator_generate_internal)))).
Definition generator_hash_map_stage second := statement_sequence (generator_hash_map_statements second) Sskip.
Lemma generator_hash_map_stage_source second : generator_hash_map_stage second=
  Ssequence (generator_sha_block second) (generator_digest_stage second).
Proof. destruct second;reflexivity. Qed.
Lemma generator_hash_map_suffix_source second : statement_sequence
  (skipn (Nat.pred (generator_digest_index second))
    (fst (split_statement_last (fn_body f_secp256k1_generator_generate_internal))))
  (snd (split_statement_last (fn_body f_secp256k1_generator_generate_internal)))=
  statement_sequence (generator_hash_map_statements second) (generator_after_mapping second).
Proof. destruct second;reflexivity. Qed.

Definition generator_hash_digest second key :=
  secp_sha_digest_bytes (state_regs (@literal_generator_hash second Alg.CoreFunSem key)).
Definition generator_hash_accepted second key :=
  Z.ltb (@toZ (WordToZ 8) (@literal_generator_hash second Alg.CoreFunSem key)) feP.
Definition generator_hash_map_temps second prior key le :=
  PTree.set _ret (Vint (cmov_int (prior && generator_hash_accepted second key)))
    (PTree.set (generator_digest_slot second) (Vint (cmov_int (generator_hash_accepted second key))) le).
Lemma generator_hash_digest_word second key :
  swu_digest_word (generator_hash_digest second key)=@literal_generator_hash second Alg.CoreFunSem key.
Proof. apply generator_digest_state_word. Qed.
Lemma generator_hash_digest_accept second key :
  generator_digest_accept (generator_hash_digest second key)=generator_hash_accepted second key.
Proof.
  unfold generator_digest_accept,generator_hash_digest,generator_hash_accepted,secp_sha_digest_bytes.
  rewrite jet_bitcoin_build_tapleaf_spec.be_bytes_state_regs,generator_word256_bytes_value;reflexivity.
Qed.
Lemma generator_hash_map_temps_digest second prior key le : generator_hash_map_temps second prior key le=
  generator_digest_temps second prior (generator_hash_digest second key) le.
Proof. unfold generator_hash_map_temps,generator_digest_temps;rewrite generator_hash_digest_accept;reflexivity. Qed.
Lemma generator_hash_map_ret second prior key le :
  (generator_hash_map_temps second prior key le)!_ret=
    Some (Vint (cmov_int (prior && generator_hash_accepted second key))).
Proof. apply PTree.gss. Qed.
Lemma generator_hash_map_key second prior key le :
  (generator_hash_map_temps second prior key le)!_key32=le!_key32.
Proof.
  rewrite generator_hash_map_temps_digest;apply generator_digest_temps_other;
    [discriminate|destruct second;discriminate].
Qed.

Local Ltac split_separation H :=
  repeat rewrite NoDup_cons_iff in H;cbn [In] in H;
  repeat match goal with H : _ /\ _ |- _=>destruct H end;
  repeat match goal with H : ~(?P \/ ?Q) |- _=>
    let H1:=fresh "Sep" in let H2:=fresh "Sep" in
    assert (H1:~P) by (exact (fun HP=>H (or_introl HP)));
    assert (H2:~Q) by (exact (fun HQ=>H (or_intror HQ)));clear H end.
Local Ltac keep_owned H F :=
  eapply curve_keep_free;[lia|exact H|exact F|];intro pos;repeat split;congruence.

Theorem exec_generator_hash_map (Hmodel:memcpy_model) second prior (key:Ty.tySem (Word 8))
    e le m br bc bs bb bt bp ba oa :
  (forall mc x,Int64.unsigned x<>0 ->
    Clight2.eval_funcall secp_ge mc (Internal f_secp256k1_ctz64_var) [Vlong x]
      E0 mc (Vint (Int.repr (Z_ctz (Int64.unsigned x))))) ->
  e!_sha256_init=None ->e!_sha256_uchars=None ->e!_sha256_finalize=None ->e!_sha256_fromMidstate=None ->
  e!_secp256k1_fe_set_b32=None ->e!_shallue_van_de_woestijne=None ->
  e!(generator_sha_result_id second)=Some (br,generator_sha_ctx_type) ->
  e!(generator_sha_context_id second)=Some (bc,generator_sha_ctx_type) ->
  e!_sha256_buf=Some (bs,generator_sha_state_type) ->e!_b32=Some (bb,tarray tuchar 32) ->
  e!_t=Some (bt,curve_fe_type) ->e!_add=Some (bp,curve_ge_type) ->
  e!(generator_sha_prefix_id second)=None ->le!_key32=Some (Vptr ba oa) ->
  le!_ret=Some (Vint (cmov_int prior)) ->
  NoDup [ba;br;bc;bs;bb;bt;bp] ->
  Ptrofs.unsigned oa+32<=Ptrofs.max_unsigned ->
  secp_sha_startup m ->swu_startup m ->(forall prefix,generator_sha_prefix_state prefix m) ->
  Mem.range_perm m br 0 88 Cur Freeable ->Mem.range_perm m bc 0 88 Cur Freeable ->
  Mem.range_perm m bs 0 32 Cur Freeable ->Mem.range_perm m bb 0 32 Cur Freeable ->
  Mem.range_perm m bt 0 40 Cur Freeable ->Mem.range_perm m bp 0 88 Cur Freeable ->
  (forall i,(i<32)%nat ->Mem.load Mint8unsigned m ba (Ptrofs.unsigned oa+Z.of_nat i)=
    Some (Vint (nth i (map word8_array_value (vector_values (Word 3) 5 key)) Int.zero))) ->
  let hash:=@literal_generator_hash second Alg.CoreFunSem key in
  exists mf x y,
  Clight2.exec_stmt secp_ge e le m (generator_hash_map_stage second) E0
    (generator_hash_map_temps second prior key le) mf Out_normal /\
  fe_at mf bp 0 (words5 x) /\fe_at mf bp 40 (words5 y) /\Mem.load Mint32 mf bp 80=Some (Vint Int.zero) /\
  square_input_bounds x /\square_input_bounds y /\
  (rescale_field_output x,rescale_field_output y)=swu_words_literal_output (swu_raw_words hash) hash /\
  (generator_hash_accepted second key=true ->
    (rescale_field_output x,rescale_field_output y)=@literal_swu Alg.CoreFunSem hash) /\
  Mem.range_perm mf br 0 88 Cur Freeable /\Mem.range_perm mf bc 0 88 Cur Freeable /\
  Mem.range_perm mf bs 0 32 Cur Freeable /\Mem.range_perm mf bb 0 32 Cur Freeable /\
  Mem.range_perm mf bt 0 40 Cur Freeable /\Mem.range_perm mf bp 0 88 Cur Freeable /\
  (forall i,(i<32)%nat ->Mem.load Mint8unsigned mf ba (Ptrofs.unsigned oa+Z.of_nat i)=
    Some (Vint (nth i (map word8_array_value (vector_values (Word 3) 5 key)) Int.zero))) /\
  lframe (fun b _=>b<>br /\b<>bc /\b<>bs /\b<>bb /\b<>bt /\b<>bp) m mf /\
  readonly_preserved m mf /\secp_sha_startup mf /\swu_startup mf /\
  (forall prefix,generator_sha_prefix_state prefix mf).
Proof.
  intros Count FI FU FF FD SetFun MapFun Result Context State Bytes T Add Prefix Key Ret Sep.
  split_separation Sep.
  intros Hi SHA SWU Prefixes FR FC FS FB FT FP Input;cbv zeta.
  assert (Len:length (map word8_array_value (vector_values (Word 3) 5 key))=32%nat).
  { rewrite map_length,vector_values_length;reflexivity. }
  destruct (exec_generator_sha_block_owned Hmodel second
    (map word8_array_value (vector_values (Word 3) 5 key)) e le m br bc bs bb ba oa
    FI FU FF FD Result Context State Bytes Prefix Key
    ltac:(congruence) ltac:(congruence) ltac:(congruence) ltac:(congruence) ltac:(congruence)
    ltac:(congruence) ltac:(congruence) ltac:(congruence) ltac:(congruence)
    Len Hi SHA (Prefixes second) FR FC FS FB Input)
    as (mi & Hash & Digest & Regs & FRI & FCI & FSI & FBI & FrameH & ReadH & SHAI & PrefixI).
  rewrite generator_sha_regs_literal in Digest,Regs.
  change (forall i,(i<32)%nat ->Mem.load Mint8unsigned mi bb (Z.of_nat i)=
    Some (Vint (Int.repr (nth i (generator_hash_digest second key) 0)))) in Digest.
  assert (FTI:Mem.range_perm mi bt 0 40 Cur Freeable) by (keep_owned FT FrameH).
  assert (FPI:Mem.range_perm mi bp 0 88 Cur Freeable) by (keep_owned FP FrameH).
  assert (SWUI:swu_startup mi) by (eapply swu_startup_preserved;[exact SWU|exact ReadH]).
  assert (DigestLen:length (generator_hash_digest second key)=32%nat).
  { apply secp_sha_digest_length;unfold state_regs;rewrite map_length.
    apply jet_word32_chunks.word32_chunks_length. }
  destruct (exec_generator_digest_mapping second prior (generator_hash_digest second key) e le mi bt bb bp
    Count SetFun MapFun T Add Bytes Ret DigestLen (secp_sha_digest_bounds _)
    ltac:(congruence) ltac:(congruence) ltac:(congruence) SWUI FTI FBI FPI Digest)
    as (mf & x & y & Map & X & Y & Flag & BX & BY & Value & Accepted & FTF & FBF & FPF & DigestF & SWUF & FrameM & ReadM).
  rewrite <-generator_hash_map_temps_digest in Map.
  rewrite generator_hash_digest_word in Value,Accepted.
  rewrite generator_hash_digest_accept in Accepted.
  assert (FRF:Mem.range_perm mf br 0 88 Cur Freeable) by (keep_owned FRI FrameM).
  assert (FCF:Mem.range_perm mf bc 0 88 Cur Freeable) by (keep_owned FCI FrameM).
  assert (FSF:Mem.range_perm mf bs 0 32 Cur Freeable) by (keep_owned FSI FrameM).
  assert (Frame:lframe (fun b _=>b<>br /\b<>bc /\b<>bs /\b<>bb /\b<>bt /\b<>bp) m mf).
  { eapply lframe_trans.
    - eapply lframe_implies;[exact FrameH|];intros b pos [NR [NC [NS [NB [NT NP]]]]] Valid;repeat split;assumption.
    - eapply lframe_implies;[exact FrameM|];intros b pos [NR [NC [NS [NB [NT NP]]]]] Valid;repeat split;assumption. }
  assert (Read:readonly_preserved m mf) by (eapply preserved_trans;[exact ReadH|exact ReadM]).
  assert (SHAF:secp_sha_startup mf).
  { eapply secp_sha_startup_preserved;[exact SHAI|exact ReadM|exact FrameM|].
    pose proof (proj1 (secp_sha_startup_separate mi bt 40 SHAI ltac:(lia) FTI)) as DT.
    pose proof (proj1 (secp_sha_startup_separate mi bb 32 SHAI ltac:(lia) FBI)) as DB.
    pose proof (proj1 (secp_sha_startup_separate mi bp 88 SHAI ltac:(lia) FPI)) as DP.
    intros pos;repeat split;congruence. }
  exists mf,x,y;split.
  - rewrite generator_hash_map_stage_source;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact Hash|exact Map].
  - split;[exact X|];split;[exact Y|];split;[exact Flag|];split;[exact BX|];split;[exact BY|];
      split;[exact Value|];split;[exact Accepted|];split;[exact FRF|];split;[exact FCF|];
      split;[exact FSF|];split;[exact FBF|];split;[exact FTF|];split;[exact FPF|];split.
    + intros i Index;rewrite (proj1 Frame);[apply Input;exact Index| |intros;repeat split;congruence].
      pose proof (Input 0%nat ltac:(lia)) as Load;apply Mem.load_valid_access in Load.
      eapply Mem.valid_access_valid_block;eapply Mem.valid_access_implies;[exact Load|constructor].
    + split;[exact Frame|];split;[exact Read|];split;[exact SHAF|];split;[exact SWUF|].
      intro prefix;eapply generator_sha_prefix_preserved;[apply Prefixes|exact Read].
Qed.
