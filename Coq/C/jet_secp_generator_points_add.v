(** Original generator through both hash/SWU passes and actual mixed addition.
    Execute every key, including rejected digests; identify the canonical point
    sum when both original conversion flags accept. This is not a public jet. *)
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
  C.jet_secp_point_set_bit C.jet_secp_generator_points_prefix C.jet_secp_generator_add
  C.jet_secp_mixed_body_loose C.jet_secp_mixed_infinite_literal C.jet_secp_mixed_xy_literal
  C.jet_secp_add_literal C.jet_secp_literal_add_program.
Import ListNotations Ctypes Values Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge literal_swu rescale_field_output swu_words_literal_output literal_generator_hash literal_gej_ge_add.

Definition generator_points_add_prefix := statement_sequence
  (firstn 15 (fst (split_statement_last (fn_body f_secp256k1_generator_generate_internal)))) Sskip.
Lemma generator_points_add_source : generator_points_add_prefix=statement_sequence
  (firstn 14 (fst (split_statement_last (fn_body f_secp256k1_generator_generate_internal))))
  (Ssequence generator_add_stmt Sskip).
Proof. reflexivity. Qed.
Local Ltac keep_owned H F :=
  eapply curve_keep_free;[lia|exact H|exact F|];intro pos;split;congruence.

Theorem exec_generator_points_add (Hmodel:memcpy_model) (key:Ty.tySem (Word 8))
    e le m br0 bc0 br1 bc1 bs bb bt bp bx ba oa :
  (forall mc x,Int64.unsigned x<>0 ->
    Clight2.eval_funcall secp_ge mc (Internal f_secp256k1_ctz64_var) [Vlong x]
      E0 mc (Vint (Int.repr (Z_ctz (Int64.unsigned x))))) ->
  e!_sha256_init=None ->e!_sha256_uchars=None ->e!_sha256_finalize=None ->e!_sha256_fromMidstate=None ->
  e!_secp256k1_fe_set_b32=None ->e!_shallue_van_de_woestijne=None ->e!_secp256k1_gej_set_ge=None ->
  e!_secp256k1_gej_add_ge_var=None ->
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
  Clight2.exec_stmt secp_ge e le m generator_points_add_prefix E0 (generator_points_temps key le) mf Out_normal /\
  fe_at mf bx 0 (words5 (mixed_mode_body_x_words true Int.zero x0 y0 (point_set_bit_words true) x1 y1)) /\
  fe_at mf bx 40 (words5 (mixed_mode_body_y_words true Int.zero x0 y0 (point_set_bit_words true) x1 y1)) /\
  fe_at mf bx 80 (words5 (mixed_mode_body_z_words true Int.zero x0 y0 (point_set_bit_words true) x1 y1)) /\
  Mem.load Mint32 mf bx 120=Some (Vint (mixed_mode_body_flag true Int.zero x0 y0 (point_set_bit_words true) x1 y1)) /\
  square_input_bounds (mixed_mode_body_x_words true Int.zero x0 y0 (point_set_bit_words true) x1 y1) /\
  square_input_bounds (mixed_mode_body_y_words true Int.zero x0 y0 (point_set_bit_words true) x1 y1) /\
  square_input_bounds (mixed_mode_body_z_words true Int.zero x0 y0 (point_set_bit_words true) x1 y1) /\
  (generator_hash_accepted false key=true ->generator_hash_accepted true key=true ->
    ((rescale_field_output (mixed_mode_body_x_words true Int.zero x0 y0 (point_set_bit_words true) x1 y1),
      rescale_field_output (mixed_mode_body_y_words true Int.zero x0 y0 (point_set_bit_words true) x1 y1)),
      rescale_field_output (mixed_mode_body_z_words true Int.zero x0 y0 (point_set_bit_words true) x1 y1))=
    @literal_gej_ge_add Alg.CoreFunSem
      ((@literal_swu Alg.CoreFunSem (@literal_generator_hash false Alg.CoreFunSem key),
         @literal_fe_one256 Alg.CoreFunSem tt),
        @literal_swu Alg.CoreFunSem (@literal_generator_hash true Alg.CoreFunSem key))) /\
  Mem.range_perm mf br0 0 88 Cur Freeable /\Mem.range_perm mf bc0 0 88 Cur Freeable /\
  Mem.range_perm mf br1 0 88 Cur Freeable /\Mem.range_perm mf bc1 0 88 Cur Freeable /\
  Mem.range_perm mf bs 0 32 Cur Freeable /\Mem.range_perm mf bb 0 32 Cur Freeable /\
  Mem.range_perm mf bt 0 40 Cur Freeable /\Mem.range_perm mf bp 0 88 Cur Freeable /\Mem.range_perm mf bx 0 128 Cur Freeable /\
  (forall i,(i<32)%nat ->Mem.load Mint8unsigned mf ba (Ptrofs.unsigned oa+Z.of_nat i)=
    Some (Vint (nth i (map word8_array_value (vector_values (Word 3) 5 key)) Int.zero))) /\
  lframe (fun b _=>b<>br0 /\b<>bc0 /\b<>br1 /\b<>bc1 /\b<>bs /\b<>bb /\b<>bt /\b<>bp /\b<>bx) m mf /\
  readonly_preserved m mf /\secp_sha_startup mf /\swu_startup mf /\(forall prefix,generator_sha_prefix_state prefix mf).
Proof.
 intros Count FI FU FF FD SetFun MapFun SetGe AddFun Result0 Context0 Result1 Context1 State Bytes T Add Acc Prefix Key Null Sep
   Hi SHA SWU Prefixes FR0 FC0 FR1 FC1 FS FB FT FP FX Input.
 assert (Apart:bx<>bp /\br0<>bx /\br0<>bp /\bc0<>bx /\bc0<>bp /\br1<>bx /\br1<>bp /\
   bc1<>bx /\bc1<>bp /\bs<>bx /\bs<>bp /\bb<>bx /\bb<>bp /\bt<>bx /\bt<>bp /\ba<>bx /\ba<>bp).
 { pose proof Sep as D;repeat rewrite NoDup_cons_iff in D;cbn [In] in D;intuition congruence. }
 destruct Apart as (XP & RX0 & RP0 & CX0 & CP0 & RX1 & RP1 & CX1 & CP1 & SX & SP & BBX & BBP & TX & TP & AX & AP).
 destruct (exec_generator_points_prefix Hmodel key e le m br0 bc0 br1 bc1 bs bb bt bp bx ba oa
   Count FI FU FF FD SetFun MapFun SetGe Result0 Context0 Result1 Context1 State Bytes T Add Acc Prefix Key Null
   Sep Hi SHA SWU Prefixes FR0 FC0 FR1 FC1 FS FB FT FP FX Input)
   as (mi & x0 & y0 & x1 & y1 & Points & X0 & Y0 & Z0 & Flag0 & X1 & Y1 & Flag1 & BX0 & BY0 & BX1 & BY1 &
     Value0 & Value1 & Accepted0 & Accepted1 & FR0I & FC0I & FR1I & FC1I & FSI & FBI & FTI & FPI & FXI & KeyI & FrameP & ReadP & SHAI & SWUI & PrefixI).
 destruct (exec_generator_add e (generator_points_temps key le) mi bx bp x0 y0 (point_set_bit_words true) x1 y1
   Acc Add AddFun XP BX0 BY0 mixed_one_bounds BX1 BY1 X0 Y0 Z0 Flag0 X1 Y1 Flag1 FXI FPI SHAI SWUI PrefixI)
   as (mf & Call & XO & YO & ZO & FlagO & BXO & BYO & BZO & FXF & FPF & FrameA & ReadA & SHAF & SWUF & PrefixF).
 assert (FR0F:Mem.range_perm mf br0 0 88 Cur Freeable) by (keep_owned FR0I FrameA).
 assert (FC0F:Mem.range_perm mf bc0 0 88 Cur Freeable) by (keep_owned FC0I FrameA).
 assert (FR1F:Mem.range_perm mf br1 0 88 Cur Freeable) by (keep_owned FR1I FrameA).
 assert (FC1F:Mem.range_perm mf bc1 0 88 Cur Freeable) by (keep_owned FC1I FrameA).
 assert (FSF:Mem.range_perm mf bs 0 32 Cur Freeable) by (keep_owned FSI FrameA).
 assert (FBF:Mem.range_perm mf bb 0 32 Cur Freeable) by (keep_owned FBI FrameA).
 assert (FTF:Mem.range_perm mf bt 0 40 Cur Freeable) by (keep_owned FTI FrameA).
 assert (KeyF:forall i,(i<32)%nat ->Mem.load Mint8unsigned mf ba (Ptrofs.unsigned oa+Z.of_nat i)=
   Some (Vint (nth i (map word8_array_value (vector_values (Word 3) 5 key)) Int.zero))).
 { intros i Index;rewrite (proj1 FrameA);[apply KeyI;exact Index| |intros;split;assumption].
   pose proof (KeyI 0%nat ltac:(lia)) as Load;apply Mem.load_valid_access in Load.
   eapply Mem.valid_access_valid_block;eapply Mem.valid_access_implies;[exact Load|constructor]. }
 exists mf,x0,y0,x1,y1;split.
 - rewrite generator_points_add_source;eapply exec_statement_prefix_then_last;[exact Points|].
   change E0 with (E0**E0);eapply exec_Sseq_1;[exact Call|constructor].
 - split;[exact XO|];split;[exact YO|];split;[exact ZO|];split;[exact FlagO|];
   split;[exact BXO|];split;[exact BYO|];split;[exact BZO|];split.
   + intros Good0 Good1;rewrite (mixed_xy_affine_outputs_literal x0 y0 x1 y1 BX0 BY0 BX1 BY1),
       (Accepted0 Good0),(Accepted1 Good1);reflexivity.
   + split;[exact FR0F|];split;[exact FC0F|];split;[exact FR1F|];split;[exact FC1F|];
     split;[exact FSF|];split;[exact FBF|];split;[exact FTF|];split;[exact FPF|];split;[exact FXF|];split;[exact KeyF|];split.
     * eapply lframe_trans;[exact FrameP|].
       eapply lframe_implies;[exact FrameA|];intros b pos Outside Valid;clear -Outside;tauto.
     * split;[eapply preserved_trans;[exact ReadP|exact ReadA]|];split;[exact SHAF|];split;[exact SWUF|exact PrefixF].
Qed.
