(** Both computed hash-to-point passes and the intervening unblinded
    accumulator initialization in the original generator. The public
    hash_to_curve wrapper calls this path with blind32 = NULL. Addition,
    final affine conversion, allocation and return are outside this span. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg.
Require Import C.extraMath C.jet_memcpy_model C.jet_sx_mem C.jet_sx_zval
  C.jet_secp_linkage C.jets_secp C.jet_secp_fns C.jet_secp_fe_nv C.jet_secp_fe_math
  C.jet_secp_field_cmov C.jet_secp_square_columns C.jet_secp_multiply_normalize_bridge
  C.jet_secp_rescale_literal C.jet_secp_swu_raw_input C.jet_secp_swu_word_parity
  C.jet_secp_swu_literal C.jet_secp_swu_startup C.jet_secp_curve_statements
  C.jet_secp_curve_frame C.jet_secp_statement_prefix C.jet_clight_internal_preserve
  C.jet_buffer_input C.jet_read8s_layout C.jet_sha_ctx8_model C.jet_secp_sha_owned
  C.jet_secp_sha_startup C.jet_secp_generator_sha_start C.jet_secp_generator_sha_absorb
  C.jet_secp_generator_sha_complete C.jet_secp_generator_hash_literal
  C.jet_secp_generator_digest_mapping C.jet_secp_generator_hash_map
  C.jet_secp_gej_set_ge_owned C.jet_secp_point_set_bit C.jet_secp_closed_helpers C.jet_clight_internal_frame.
Import ListNotations Ctypes Values Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge literal_swu rescale_field_output swu_words_literal_output literal_generator_hash.

Definition generator_first_accumulate := nth 10
  (fst (split_statement_last (fn_body f_secp256k1_generator_generate_internal))) Sskip.
Definition generator_blinded_accumulate := match generator_first_accumulate with
  Sifthenelse _ yes _=>yes | _=>Sskip end.
Lemma generator_first_accumulate_source : generator_first_accumulate=
  Sifthenelse (Etempvar _blind32 (tptr tuchar)) generator_blinded_accumulate
    (curve_call _secp256k1_gej_set_ge f_secp256k1_gej_set_ge None
      [Eaddrof (Evar _accum (Tstruct __6123 noattr)) (tptr (Tstruct __6123 noattr));
       Eaddrof (Evar _add curve_ge_type) (tptr curve_ge_type)]).
Proof. reflexivity. Qed.
Lemma generator_accumulate_closed :
  closed_stmtb secp_closed_helpers (fn_body f_secp256k1_gej_set_ge)=true.
Proof. vm_compute;reflexivity. Qed.

Theorem exec_generator_first_accumulate e le m bx bp x y :
  e!_accum=Some (bx,Tstruct __6123 noattr) ->e!_add=Some (bp,curve_ge_type) ->
  e!_secp256k1_gej_set_ge=None ->le!_blind32=Some (Vlong Int64.zero) ->bx<>bp ->
  Mem.range_perm m bx 0 128 Cur Freeable ->
  fe_at m bp 0 (words5 x) ->fe_at m bp 40 (words5 y) ->Mem.load Mint32 m bp 80=Some (Vint Int.zero) ->
  exists mf,Clight2.exec_stmt secp_ge e le m generator_first_accumulate E0 le mf Out_normal /\
  fe_at mf bx 0 (words5 x) /\fe_at mf bx 40 (words5 y) /\
  fe_at mf bx 80 (words5 (point_set_bit_words true)) /\Mem.load Mint32 mf bx 120=Some (Vint Int.zero) /\
  Mem.range_perm mf bx 0 128 Cur Freeable /\lframe (fun b _=>b<>bx) m mf /\readonly_preserved m mf.
Proof.
  intros Acc Add Fun Null Apart FX X Y Flag.
  destruct (eval_gej_set_ge_owned m bx bp x y Int.zero Apart FX X Y Flag)
    as (mf & Call & AX & AY & AZ & AF & FXF & Frame).
  change (fe_at mf bx 80 (words5 (point_set_bit_words true))) in AZ.
  exists mf;split.
  - rewrite generator_first_accumulate_source.
    eapply exec_Sifthenelse with (v1:=Vlong Int64.zero) (b:=false).
    + apply eval_Etempvar;exact Null.
    + reflexivity.
    + eapply exec_curve_call with (vargs:=[Vptr bx Ptrofs.zero;Vptr bp Ptrofs.zero]) (v:=Vundef).
      * unfold secp_pure;repeat (first [left;reflexivity|right]).
      * exact Fun.
      * eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;exact Acc|reflexivity|].
        eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;exact Add|reflexivity|constructor].
      * exact Call.
  - split;[exact AX|];split;[exact AY|];split;[exact AZ|];split;[exact AF|];split;[exact FXF|];split;[exact Frame|].
    eapply secp_closed_function_preserved;[exact generator_accumulate_closed|reflexivity|exact Call].
Qed.

Definition generator_two_maps := statement_sequence
  (firstn 7 (skipn 7 (fst (split_statement_last (fn_body f_secp256k1_generator_generate_internal))))) Sskip.
Definition generator_two_maps_temps prior key le :=
  generator_hash_map_temps true (prior && generator_hash_accepted false key) key
    (generator_hash_map_temps false prior key le).
Lemma generator_two_maps_source : generator_two_maps=
  statement_sequence (generator_hash_map_statements false)
    (Ssequence generator_first_accumulate (generator_hash_map_stage true)).
Proof. reflexivity. Qed.
Lemma generator_two_maps_ret prior key le : (generator_two_maps_temps prior key le)!_ret=
  Some (Vint (cmov_int ((prior && generator_hash_accepted false key) && generator_hash_accepted true key))).
Proof. apply generator_hash_map_ret. Qed.

Local Ltac split_separation H :=
  repeat rewrite NoDup_cons_iff in H;cbn [In] in H;
  repeat match goal with H : _ /\ _ |- _=>destruct H end;
  repeat match goal with H : ~(?P \/ ?Q) |- _=>
    let H1:=fresh "Sep" in let H2:=fresh "Sep" in
    assert (H1:~P) by (exact (fun HP=>H (or_introl HP)));
    assert (H2:~Q) by (exact (fun HQ=>H (or_intror HQ)));clear H end.
Local Ltac distinct_subset :=
  repeat rewrite NoDup_cons_iff;cbn [In];repeat split;try apply NoDup_nil;intuition congruence.
Local Ltac keep_owned H F :=
  eapply curve_keep_free;[lia|exact H|exact F|];intro pos;repeat split;congruence.

Theorem exec_generator_two_maps (Hmodel:memcpy_model) prior (key:Ty.tySem (Word 8))
    e le m br0 bc0 br1 bc1 bs bb bt bp bx ba oa :
  (forall mc x,Int64.unsigned x<>0 ->
    Clight2.eval_funcall secp_ge mc (Internal f_secp256k1_ctz64_var) [Vlong x]
      E0 mc (Vint (Int.repr (Z_ctz (Int64.unsigned x))))) ->
  e!_sha256_init=None ->e!_sha256_uchars=None ->e!_sha256_finalize=None ->e!_sha256_fromMidstate=None ->
  e!_secp256k1_fe_set_b32=None ->e!_shallue_van_de_woestijne=None ->e!_secp256k1_gej_set_ge=None ->
  e!(generator_sha_result_id false)=Some (br0,generator_sha_ctx_type) ->
  e!(generator_sha_context_id false)=Some (bc0,generator_sha_ctx_type) ->
  e!(generator_sha_result_id true)=Some (br1,generator_sha_ctx_type) ->
  e!(generator_sha_context_id true)=Some (bc1,generator_sha_ctx_type) ->
  e!_sha256_buf=Some (bs,generator_sha_state_type) ->e!_b32=Some (bb,tarray tuchar 32) ->
  e!_t=Some (bt,curve_fe_type) ->e!_add=Some (bp,curve_ge_type) ->e!_accum=Some (bx,Tstruct __6123 noattr) ->
  (forall second,e!(generator_sha_prefix_id second)=None) ->
  le!_key32=Some (Vptr ba oa) ->le!_blind32=Some (Vlong Int64.zero) ->le!_ret=Some (Vint (cmov_int prior)) ->
  NoDup [ba;br0;bc0;br1;bc1;bs;bb;bt;bp;bx] ->Ptrofs.unsigned oa+32<=Ptrofs.max_unsigned ->
  secp_sha_startup m ->swu_startup m ->(forall prefix,generator_sha_prefix_state prefix m) ->
  Mem.range_perm m br0 0 88 Cur Freeable ->Mem.range_perm m bc0 0 88 Cur Freeable ->
  Mem.range_perm m br1 0 88 Cur Freeable ->Mem.range_perm m bc1 0 88 Cur Freeable ->
  Mem.range_perm m bs 0 32 Cur Freeable ->Mem.range_perm m bb 0 32 Cur Freeable ->
  Mem.range_perm m bt 0 40 Cur Freeable ->Mem.range_perm m bp 0 88 Cur Freeable ->Mem.range_perm m bx 0 128 Cur Freeable ->
  (forall i,(i<32)%nat ->Mem.load Mint8unsigned m ba (Ptrofs.unsigned oa+Z.of_nat i)=
    Some (Vint (nth i (map word8_array_value (vector_values (Word 3) 5 key)) Int.zero))) ->
  exists mf x0 y0 x1 y1,
  Clight2.exec_stmt secp_ge e le m generator_two_maps E0 (generator_two_maps_temps prior key le) mf Out_normal /\
  fe_at mf bx 0 (words5 x0) /\fe_at mf bx 40 (words5 y0) /\
  fe_at mf bx 80 (words5 (point_set_bit_words true)) /\Mem.load Mint32 mf bx 120=Some (Vint Int.zero) /\
  fe_at mf bp 0 (words5 x1) /\fe_at mf bp 40 (words5 y1) /\Mem.load Mint32 mf bp 80=Some (Vint Int.zero) /\
  square_input_bounds x0 /\square_input_bounds y0 /\square_input_bounds x1 /\square_input_bounds y1 /\
  (rescale_field_output x0,rescale_field_output y0)=swu_words_literal_output
    (swu_raw_words (@literal_generator_hash false Alg.CoreFunSem key)) (@literal_generator_hash false Alg.CoreFunSem key) /\
  (rescale_field_output x1,rescale_field_output y1)=swu_words_literal_output
    (swu_raw_words (@literal_generator_hash true Alg.CoreFunSem key)) (@literal_generator_hash true Alg.CoreFunSem key) /\
  (generator_hash_accepted false key=true ->
    (rescale_field_output x0,rescale_field_output y0)=@literal_swu Alg.CoreFunSem (@literal_generator_hash false Alg.CoreFunSem key)) /\
  (generator_hash_accepted true key=true ->
    (rescale_field_output x1,rescale_field_output y1)=@literal_swu Alg.CoreFunSem (@literal_generator_hash true Alg.CoreFunSem key)) /\
  Mem.range_perm mf br0 0 88 Cur Freeable /\Mem.range_perm mf bc0 0 88 Cur Freeable /\
  Mem.range_perm mf br1 0 88 Cur Freeable /\Mem.range_perm mf bc1 0 88 Cur Freeable /\
  Mem.range_perm mf bs 0 32 Cur Freeable /\Mem.range_perm mf bb 0 32 Cur Freeable /\
  Mem.range_perm mf bt 0 40 Cur Freeable /\Mem.range_perm mf bp 0 88 Cur Freeable /\Mem.range_perm mf bx 0 128 Cur Freeable /\
  (forall i,(i<32)%nat ->Mem.load Mint8unsigned mf ba (Ptrofs.unsigned oa+Z.of_nat i)=
    Some (Vint (nth i (map word8_array_value (vector_values (Word 3) 5 key)) Int.zero))) /\
  lframe (fun b _=>b<>br0 /\b<>bc0 /\b<>br1 /\b<>bc1 /\b<>bs /\b<>bb /\b<>bt /\b<>bp /\b<>bx) m mf /\
  readonly_preserved m mf /\secp_sha_startup mf /\swu_startup mf /\(forall prefix,generator_sha_prefix_state prefix mf).
Proof.
  intros Count FI FU FF FD SetFun MapFun SetGe Result0 Context0 Result1 Context1 State Bytes T Add Acc Prefix Key Null Ret Sep.
  split_separation Sep.
  intros Hi SHA SWU Prefixes FR0 FC0 FR1 FC1 FS FB FT FP FX Input.
  assert (Distinct0:NoDup [ba;br0;bc0;bs;bb;bt;bp]) by distinct_subset.
  assert (Distinct1:NoDup [ba;br1;bc1;bs;bb;bt;bp]) by distinct_subset.
  destruct (exec_generator_hash_map Hmodel false prior key e le m br0 bc0 bs bb bt bp ba oa
    Count FI FU FF FD SetFun MapFun Result0 Context0 State Bytes T Add (Prefix false) Key Ret
    Distinct0 Hi SHA SWU Prefixes FR0 FC0 FS FB FT FP Input)
    as (m1 & x0 & y0 & First & X0 & Y0 & Flag0 & BX0 & BY0 & Value0 & Accepted0 & FR01 & FC01 & FS1 & FB1 & FT1 & FP1 & Key1 & Frame1 & Read1 & SHA1 & SWU1 & Prefix1).
  set (le1:=generator_hash_map_temps false prior key le).
  assert (FX1:Mem.range_perm m1 bx 0 128 Cur Freeable) by (keep_owned FX Frame1).
  assert (FR11:Mem.range_perm m1 br1 0 88 Cur Freeable) by (keep_owned FR1 Frame1).
  assert (FC11:Mem.range_perm m1 bc1 0 88 Cur Freeable) by (keep_owned FC1 Frame1).
  assert (Null1:le1!_blind32=Some (Vlong Int64.zero)).
  { unfold le1;rewrite generator_hash_map_temps_digest,generator_digest_temps_other by discriminate;exact Null. }
  destruct (exec_generator_first_accumulate e le1 m1 bx bp x0 y0 Acc Add SetGe Null1 ltac:(congruence) FX1 X0 Y0 Flag0)
    as (m2 & Accumulate & AX & AY & AZ & AF & FX2 & Frame2 & Read2).
  assert (FR12:Mem.range_perm m2 br1 0 88 Cur Freeable) by (keep_owned FR11 Frame2).
  assert (FC12:Mem.range_perm m2 bc1 0 88 Cur Freeable) by (keep_owned FC11 Frame2).
  assert (FS2:Mem.range_perm m2 bs 0 32 Cur Freeable) by (keep_owned FS1 Frame2).
  assert (FB2:Mem.range_perm m2 bb 0 32 Cur Freeable) by (keep_owned FB1 Frame2).
  assert (FT2:Mem.range_perm m2 bt 0 40 Cur Freeable) by (keep_owned FT1 Frame2).
  assert (FP2:Mem.range_perm m2 bp 0 88 Cur Freeable) by (keep_owned FP1 Frame2).
  assert (SHA2:secp_sha_startup m2).
  { eapply secp_sha_startup_preserved;[exact SHA1|exact Read2|exact Frame2|].
    pose proof (proj1 (secp_sha_startup_separate m1 bx 128 SHA1 ltac:(lia) FX1));intros;congruence. }
  assert (SWU2:swu_startup m2) by (eapply swu_startup_preserved;[exact SWU1|exact Read2]).
  assert (Prefix2:forall prefix,generator_sha_prefix_state prefix m2).
  { intro prefix;eapply generator_sha_prefix_preserved;[apply Prefix1|exact Read2]. }
  assert (Input2:forall i,(i<32)%nat ->Mem.load Mint8unsigned m2 ba (Ptrofs.unsigned oa+Z.of_nat i)=
    Some (Vint (nth i (map word8_array_value (vector_values (Word 3) 5 key)) Int.zero))).
  { intros i Index;rewrite (proj1 Frame2);[apply Key1;exact Index| |intros;congruence].
    pose proof (Key1 0%nat ltac:(lia)) as Load;apply Mem.load_valid_access in Load.
    eapply Mem.valid_access_valid_block;eapply Mem.valid_access_implies;[exact Load|constructor]. }
  assert (KeyLe1:le1!_key32=Some (Vptr ba oa)).
  { unfold le1;rewrite generator_hash_map_key;exact Key. }
  assert (RetLe1:le1!_ret=Some (Vint (cmov_int (prior && generator_hash_accepted false key)))).
  { exact (generator_hash_map_ret false prior key le). }
  destruct (exec_generator_hash_map Hmodel true (prior && generator_hash_accepted false key) key e le1 m2 br1 bc1 bs bb bt bp ba oa
    Count FI FU FF FD SetFun MapFun Result1 Context1 State Bytes T Add (Prefix true)
    KeyLe1 RetLe1 Distinct1 Hi SHA2 SWU2 Prefix2 FR12 FC12 FS2 FB2 FT2 FP2 Input2)
    as (mf & x1 & y1 & Second & X1 & Y1 & Flag1 & BX1 & BY1 & Value1 & Accepted1 & FR1F & FC1F & FSF & FBF & FTF & FPF & KeyF & Frame3 & Read3 & SHAF & SWUF & PrefixF).
  assert (AXF:fe_at mf bx 0 (words5 x0)).
  { eapply curve_keep_field_range;[reflexivity|exact AX|exact Frame3|];intros;repeat split;congruence. }
  assert (AYF:fe_at mf bx 40 (words5 y0)).
  { eapply curve_keep_field_range;[reflexivity|exact AY|exact Frame3|];intros;repeat split;congruence. }
  assert (AZF:fe_at mf bx 80 (words5 (point_set_bit_words true))).
  { eapply curve_keep_field_range;[reflexivity|exact AZ|exact Frame3|];intros;repeat split;congruence. }
  assert (AFF:Mem.load Mint32 mf bx 120=Some (Vint Int.zero)).
  { rewrite (proj1 Frame3);[exact AF| |intros;repeat split;congruence].
    eapply Mem.perm_valid_block;apply (FX2 0);lia. }
  assert (FXF:Mem.range_perm mf bx 0 128 Cur Freeable) by (keep_owned FX2 Frame3).
  assert (FR02:Mem.range_perm m2 br0 0 88 Cur Freeable) by (keep_owned FR01 Frame2).
  assert (FC02:Mem.range_perm m2 bc0 0 88 Cur Freeable) by (keep_owned FC01 Frame2).
  assert (FR0F:Mem.range_perm mf br0 0 88 Cur Freeable) by (keep_owned FR02 Frame3).
  assert (FC0F:Mem.range_perm mf bc0 0 88 Cur Freeable) by (keep_owned FC02 Frame3).
  exists mf,x0,y0,x1,y1;split.
  - rewrite generator_two_maps_source;unfold generator_two_maps_temps.
    eapply exec_statement_prefix_then_last;[exact First|].
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact Accumulate|exact Second].
  - split;[exact AXF|];split;[exact AYF|];split;[exact AZF|];split;[exact AFF|];
      split;[exact X1|];split;[exact Y1|];split;[exact Flag1|];
      split;[exact BX0|];split;[exact BY0|];split;[exact BX1|];split;[exact BY1|];
      split;[exact Value0|];split;[exact Value1|];split;[exact Accepted0|];split;[exact Accepted1|];
      split;[exact FR0F|];split;[exact FC0F|];split;[exact FR1F|];split;[exact FC1F|];
      split;[exact FSF|];split;[exact FBF|];split;[exact FTF|];split;[exact FPF|];split;[exact FXF|];split;[exact KeyF|];split.
    + eapply lframe_trans.
      * eapply lframe_implies;[exact Frame1|];intros b pos Outside Valid;clear -Outside;tauto.
      * eapply lframe_trans.
        -- eapply lframe_implies;[exact Frame2|];intros b pos Outside Valid;clear -Outside;tauto.
        -- eapply lframe_implies;[exact Frame3|];intros b pos Outside Valid;clear -Outside;tauto.
    + split;[eapply preserved_trans;[exact Read1|eapply preserved_trans;[exact Read2|exact Read3]]|].
      split;[exact SHAF|];split;[exact SWUF|exact PrefixF].
Qed.
