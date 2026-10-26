(** Original generator execution from its first statement through both
    SHA/SWU passes, before mixed addition. Derive ret=1 and all state passed
    to the existing two-pass theorem from the actual initialization. *)
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
  C.jet_buffer_input C.jet_read8s_layout C.jet_secp_sha_startup
  C.jet_secp_generator_sha_start C.jet_secp_generator_sha_absorb
  C.jet_secp_generator_hash_literal C.jet_secp_generator_hash_map
  C.jet_secp_generator_two_maps C.jet_secp_point_set_bit C.jet_secp_generator_begin.
Import ListNotations Ctypes Values Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge literal_swu rescale_field_output swu_words_literal_output literal_generator_hash.

Definition generator_points_prefix := statement_sequence
  (firstn 14 (fst (split_statement_last (fn_body f_secp256k1_generator_generate_internal)))) Sskip.
Definition generator_points_temps key le := generator_two_maps_temps true key (generator_initial_temps le).
Lemma generator_points_prefix_source : generator_points_prefix=statement_sequence
  (firstn 7 (fst (split_statement_last (fn_body f_secp256k1_generator_generate_internal)))) generator_two_maps.
Proof. reflexivity. Qed.
Lemma generator_points_ret key le : (generator_points_temps key le)!_ret=
  Some (Vint (cmov_int (generator_hash_accepted false key && generator_hash_accepted true key))).
Proof. unfold generator_points_temps;rewrite generator_two_maps_ret;reflexivity. Qed.
Local Ltac keep_owned H F :=
  eapply curve_keep_free;[lia|exact H|exact F|];intro pos;congruence.

Theorem exec_generator_points_prefix (Hmodel:memcpy_model) (key:Ty.tySem (Word 8))
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
  le!_key32=Some (Vptr ba oa) ->le!_blind32=Some (Vlong Int64.zero) ->
  NoDup [ba;br0;bc0;br1;bc1;bs;bb;bt;bp;bx] ->Ptrofs.unsigned oa+32<=Ptrofs.max_unsigned ->
  secp_sha_startup m ->swu_startup m ->(forall prefix,generator_sha_prefix_state prefix m) ->
  Mem.range_perm m br0 0 88 Cur Freeable ->Mem.range_perm m bc0 0 88 Cur Freeable ->
  Mem.range_perm m br1 0 88 Cur Freeable ->Mem.range_perm m bc1 0 88 Cur Freeable ->
  Mem.range_perm m bs 0 32 Cur Freeable ->Mem.range_perm m bb 0 32 Cur Freeable ->
  Mem.range_perm m bt 0 40 Cur Freeable ->Mem.range_perm m bp 0 88 Cur Freeable ->Mem.range_perm m bx 0 128 Cur Freeable ->
  (forall i,(i<32)%nat ->Mem.load Mint8unsigned m ba (Ptrofs.unsigned oa+Z.of_nat i)=
    Some (Vint (nth i (map word8_array_value (vector_values (Word 3) 5 key)) Int.zero))) ->
  exists mf x0 y0 x1 y1,
  Clight2.exec_stmt secp_ge e le m generator_points_prefix E0 (generator_points_temps key le) mf Out_normal /\
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
  intros Count FI FU FF FD SetFun MapFun SetGe Result0 Context0 Result1 Context1 State Bytes T Add Acc Prefix Key Null Sep
    Hi SHA SWU Prefixes FR0 FC0 FR1 FC1 FS FB FT FP FX Input.
  assert (Apart:ba<>bt /\br0<>bt /\bc0<>bt /\br1<>bt /\bc1<>bt /\bs<>bt /\bb<>bt /\bp<>bt /\bx<>bt).
  { pose proof Sep as D;repeat rewrite NoDup_cons_iff in D;cbn [In] in D;intuition congruence. }
  destruct Apart as (AT & RT0 & CT0 & RT1 & CT1 & ST & BT & PT & XT).
  destruct (exec_generator_initial_prefix e le m bt T Null FT) as (mi & Init & FTI & FrameI & ReadI).
  assert (FR0I:Mem.range_perm mi br0 0 88 Cur Freeable) by (keep_owned FR0 FrameI).
  assert (FC0I:Mem.range_perm mi bc0 0 88 Cur Freeable) by (keep_owned FC0 FrameI).
  assert (FR1I:Mem.range_perm mi br1 0 88 Cur Freeable) by (keep_owned FR1 FrameI).
  assert (FC1I:Mem.range_perm mi bc1 0 88 Cur Freeable) by (keep_owned FC1 FrameI).
  assert (FSI:Mem.range_perm mi bs 0 32 Cur Freeable) by (keep_owned FS FrameI).
  assert (FBI:Mem.range_perm mi bb 0 32 Cur Freeable) by (keep_owned FB FrameI).
  assert (FPI:Mem.range_perm mi bp 0 88 Cur Freeable) by (keep_owned FP FrameI).
  assert (FXI:Mem.range_perm mi bx 0 128 Cur Freeable) by (keep_owned FX FrameI).
  assert (SHAI:secp_sha_startup mi).
  { eapply secp_sha_startup_preserved;[exact SHA|exact ReadI|exact FrameI|].
    pose proof (proj1 (secp_sha_startup_separate m bt 40 SHA ltac:(lia) FT));intros;congruence. }
  assert (SWUI:swu_startup mi) by (eapply swu_startup_preserved;[exact SWU|exact ReadI]).
  assert (PrefixI:forall prefix,generator_sha_prefix_state prefix mi).
  { intro prefix;eapply generator_sha_prefix_preserved;[apply Prefixes|exact ReadI]. }
  assert (KeyI:(generator_initial_temps le)!_key32=Some (Vptr ba oa)).
  { unfold generator_initial_temps;rewrite PTree.gso by discriminate;exact Key. }
  assert (NullI:(generator_initial_temps le)!_blind32=Some (Vlong Int64.zero)).
  { unfold generator_initial_temps;rewrite PTree.gso by discriminate;exact Null. }
  assert (RetI:(generator_initial_temps le)!_ret=Some (Vint (cmov_int true))) by apply PTree.gss.
  assert (InputI:forall i,(i<32)%nat ->Mem.load Mint8unsigned mi ba (Ptrofs.unsigned oa+Z.of_nat i)=
    Some (Vint (nth i (map word8_array_value (vector_values (Word 3) 5 key)) Int.zero))).
  { intros i Index;rewrite (proj1 FrameI);[apply Input;exact Index| |intros;exact AT].
    pose proof (Input 0%nat ltac:(lia)) as Load;apply Mem.load_valid_access in Load.
    eapply Mem.valid_access_valid_block;eapply Mem.valid_access_implies;[exact Load|constructor]. }
  destruct (exec_generator_two_maps Hmodel true key e (generator_initial_temps le) mi br0 bc0 br1 bc1 bs bb bt bp bx ba oa
    Count FI FU FF FD SetFun MapFun SetGe Result0 Context0 Result1 Context1 State Bytes T Add Acc Prefix KeyI NullI RetI
    Sep Hi SHAI SWUI PrefixI FR0I FC0I FR1I FC1I FSI FBI FTI FPI FXI InputI)
    as (mf & x0 & y0 & x1 & y1 & Maps & X0 & Y0 & Z0 & Flag0 & X1 & Y1 & Flag1 & BX0 & BY0 & BX1 & BY1 &
      Value0 & Value1 & Accepted0 & Accepted1 & FR0F & FC0F & FR1F & FC1F & FSF & FBF & FTF & FPF & FXF & KeyF & FrameM & ReadM & SHAF & SWUF & PrefixF).
  exists mf,x0,y0,x1,y1;split.
  - rewrite generator_points_prefix_source;unfold generator_points_temps.
    eapply exec_statement_prefix_then_last;[exact Init|exact Maps].
  - split;[exact X0|];split;[exact Y0|];split;[exact Z0|];split;[exact Flag0|];
      split;[exact X1|];split;[exact Y1|];split;[exact Flag1|];
      split;[exact BX0|];split;[exact BY0|];split;[exact BX1|];split;[exact BY1|];
      split;[exact Value0|];split;[exact Value1|];split;[exact Accepted0|];split;[exact Accepted1|];
      split;[exact FR0F|];split;[exact FC0F|];split;[exact FR1F|];split;[exact FC1F|];
      split;[exact FSF|];split;[exact FBF|];split;[exact FTF|];split;[exact FPF|];split;[exact FXF|];split;[exact KeyF|];split.
    + eapply lframe_trans.
      * eapply lframe_implies;[exact FrameI|];intros b pos Outside Valid;clear -Outside;tauto.
      * exact FrameM.
    + split;[eapply preserved_trans;[exact ReadI|exact ReadM]|];split;[exact SHAF|];split;[exact SWUF|exact PrefixF].
Qed.
