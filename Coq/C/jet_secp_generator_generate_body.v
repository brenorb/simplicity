(** Entire original NULL-blinding generator body: both hashes/maps, point sum,
    affine conversion, save and the actual return flag. Entry/free and the
    outer public jet remain separate obligations. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg Simplicity.Bit.
Require Import C.extraMath C.jet_memcpy_model C.jet_sx_mem C.jet_sx_zval C.jet_readBit_layout
  C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_fe_math
  C.jet_secp_field_cmov C.jet_secp_field_pair_multiply C.jet_secp_square_columns
  C.jet_secp_square_numeric C.jet_secp_point_mul_storage C.jet_secp_multiply_normalize_bridge
  C.jet_secp_multiply_finish_product C.jet_secp_invert_literal C.jet_secp_fe_inv_prefix
  C.jet_secp_rescale_literal C.jet_secp_swu_literal C.jet_secp_swu_startup C.jet_secp_curve_statements
  C.jet_secp_curve_frame C.jet_secp_statement_prefix C.jet_clight_internal_preserve
  C.jet_buffer_input C.jet_read8s_layout C.jet_secp_sha_startup C.jet_secp_generator_sha_start
  C.jet_secp_generator_sha_absorb C.jet_secp_generator_hash_literal C.jet_secp_generator_hash_map
  C.jet_secp_generator_two_maps C.jet_secp_generator_begin C.jet_secp_point_set_bit
  C.jet_secp_generator_points_prefix C.jet_secp_generator_add C.jet_secp_generator_finish
  C.jet_secp_generator_sum_flag C.jet_secp_generator_codec C.jet_secp_generator_affine_roundtrip
  C.jet_secp_mixed_body_loose C.jet_secp_mixed_xy_literal C.jet_secp_mixed_infinite_literal
  C.jet_secp_add_literal C.jet_secp_literal_add_program C.jet_secp_canonical_zero.
Import ListNotations Ctypes Values Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge literal_swu rescale_field_output literal_generator_hash literal_gej_ge_add generator_saved_bytes.

Lemma generator_generate_body_source : fn_body f_secp256k1_generator_generate_internal=statement_sequence
  (firstn 14 (fst (split_statement_last (fn_body f_secp256k1_generator_generate_internal))))
  (Ssequence generator_add_stmt generator_finish).
Proof. reflexivity. Qed.
Lemma generator_points_gen key le : (generator_points_temps key le)!_gen=le!_gen.
Proof.
  unfold generator_points_temps,generator_two_maps_temps,generator_hash_map_temps,generator_initial_temps.
  cbn [C.jet_secp_generator_digest_mapping.generator_digest_slot];rewrite !PTree.gso by discriminate;reflexivity.
Qed.
Local Ltac keep_owned Perm Frame Sep :=
  eapply curve_keep_free;[clear;lia|exact Perm|exact Frame|];
    intros;clear -Sep;repeat split;intuition congruence.

Theorem exec_generator_generate_body (Hmodel:memcpy_model) (key:Ty.tySem (Word 8))
    e le m br0 bc0 br1 bc1 bs bb bt bp bx ba oa bg :
  (forall mc x,Int64.unsigned x<>0 ->
    Clight2.eval_funcall secp_ge mc (Internal f_secp256k1_ctz64_var) [Vlong x]
      E0 mc (Vint (Int.repr (Z_ctz (Int64.unsigned x))))) ->
  e!_sha256_init=None ->e!_sha256_uchars=None ->e!_sha256_finalize=None ->e!_sha256_fromMidstate=None ->
  e!_secp256k1_fe_set_b32=None ->e!_shallue_van_de_woestijne=None ->e!_secp256k1_gej_set_ge=None ->
  e!_secp256k1_gej_add_ge_var=None ->e!_secp256k1_ge_set_gej_var=None ->e!_secp256k1_generator_save=None ->
  e!(generator_sha_result_id false)=Some (br0,generator_sha_ctx_type) ->
  e!(generator_sha_context_id false)=Some (bc0,generator_sha_ctx_type) ->
  e!(generator_sha_result_id true)=Some (br1,generator_sha_ctx_type) ->
  e!(generator_sha_context_id true)=Some (bc1,generator_sha_ctx_type) ->
  e!_sha256_buf=Some (bs,generator_sha_state_type) ->e!_b32=Some (bb,tarray tuchar 32) ->
  e!_t=Some (bt,curve_fe_type) ->e!_add=Some (bp,curve_ge_type) ->e!_accum=Some (bx,Tstruct __6123 noattr) ->
  (forall second,e!(generator_sha_prefix_id second)=None) ->
  le!_key32=Some (Vptr ba oa) ->le!_blind32=Some (Vlong Int64.zero) ->le!_gen=Some (Vptr bg Ptrofs.zero) ->
  NoDup [ba;br0;bc0;br1;bc1;bs;bb;bt;bp;bx;bg] ->Ptrofs.unsigned oa+32<=Ptrofs.max_unsigned ->
  secp_sha_startup m ->swu_startup m ->(forall prefix,generator_sha_prefix_state prefix m) ->
  Mem.range_perm m br0 0 88 Cur Freeable ->Mem.range_perm m bc0 0 88 Cur Freeable ->
  Mem.range_perm m br1 0 88 Cur Freeable ->Mem.range_perm m bc1 0 88 Cur Freeable ->
  Mem.range_perm m bs 0 32 Cur Freeable ->Mem.range_perm m bb 0 32 Cur Freeable ->
  Mem.range_perm m bt 0 40 Cur Freeable ->Mem.range_perm m bp 0 88 Cur Freeable ->
  Mem.range_perm m bx 0 128 Cur Freeable ->Mem.range_perm m bg 0 64 Cur Freeable ->
  (forall i,(i<32)%nat ->Mem.load Mint8unsigned m ba (Ptrofs.unsigned oa+Z.of_nat i)=
    Some (Vint (nth i (map word8_array_value (vector_values (Word 3) 5 key)) Int.zero))) ->
  exists mf sx sy sz sumflag ox oy,
  Clight2.exec_stmt secp_ge e le m (fn_body f_secp256k1_generator_generate_internal) E0
    (generator_points_temps key le) mf
    (Out_return (Some (Vint (cmov_int (generator_hash_accepted false key && generator_hash_accepted true key)),tint))) /\
  square_input_bounds sx /\square_input_bounds sy /\square_input_bounds sz /\
  sumflag=bit_int (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem (rescale_field_output sz))) /\
  (generator_hash_accepted false key=true ->generator_hash_accepted true key=true ->
    ((rescale_field_output sx,rescale_field_output sy),rescale_field_output sz)=
    @literal_gej_ge_add Alg.CoreFunSem
      ((@literal_swu Alg.CoreFunSem (@literal_generator_hash false Alg.CoreFunSem key),
         @literal_fe_one256 Alg.CoreFunSem tt),
        @literal_swu Alg.CoreFunSem (@literal_generator_hash true Alg.CoreFunSem key))) /\
  (forall (second:bool) i,(i<32)%nat ->
    Mem.load Mint8unsigned mf bg ((if second then 32 else 0)+Z.of_nat i)=
      Some (Vint (nth i (map Int.repr (generator_saved_bytes (field_pair_valuation ox oy)
        (if second then 5 else 0))) Int.zero))) /\
  square_input_bounds ox /\square_input_bounds oy /\
  (sumflag=Int.zero ->exists zi,radix_value zi=literal_invert_numeric (fe_inv_value sz) /\
    ox=point_mul_words sx (square_words zi) /\oy=point_mul_words sy (point_mul_words zi (square_words zi))) /\
  (sumflag<>Int.zero ->ox=generator_infinite_words /\oy=generator_infinite_words) /\
  Mem.range_perm mf br0 0 88 Cur Freeable /\Mem.range_perm mf bc0 0 88 Cur Freeable /\
  Mem.range_perm mf br1 0 88 Cur Freeable /\Mem.range_perm mf bc1 0 88 Cur Freeable /\
  Mem.range_perm mf bs 0 32 Cur Freeable /\Mem.range_perm mf bb 0 32 Cur Freeable /\
  Mem.range_perm mf bt 0 40 Cur Freeable /\Mem.range_perm mf bp 0 88 Cur Freeable /\
  Mem.range_perm mf bx 0 128 Cur Freeable /\Mem.range_perm mf bg 0 64 Cur Freeable /\
  (forall i,(i<32)%nat ->Mem.load Mint8unsigned mf ba (Ptrofs.unsigned oa+Z.of_nat i)=
    Some (Vint (nth i (map word8_array_value (vector_values (Word 3) 5 key)) Int.zero))) /\
  lframe (fun b _=>b<>br0 /\b<>bc0 /\b<>br1 /\b<>bc1 /\b<>bs /\b<>bb /\b<>bt /\b<>bp /\b<>bx /\b<>bg) m mf /\
  readonly_preserved m mf /\secp_sha_startup mf /\swu_startup mf /\(forall prefix,generator_sha_prefix_state prefix mf).
Proof.
  intros Count FI FU FF FD SetFun MapFun SetGe AddFun AffFun SaveFun Result0 Context0 Result1 Context1 State Bytes T Add Acc
    Prefix Key Null Gen Sep Hi SHA SWU Prefixes FR0 FC0 FR1 FC1 FS FB FT FP FX FG Input.
  assert (SepP:NoDup [ba;br0;bc0;br1;bc1;bs;bb;bt;bp;bx]).
  { pose proof Sep as D;repeat rewrite NoDup_cons_iff in D;cbn [In] in D;
      repeat rewrite NoDup_cons_iff;cbn [In];intuition congruence. }
  pose proof Sep as Distinct;repeat rewrite NoDup_cons_iff in Distinct;cbn [In] in Distinct.
  destruct (exec_generator_points_prefix Hmodel key e le m br0 bc0 br1 bc1 bs bb bt bp bx ba oa
    Count FI FU FF FD SetFun MapFun SetGe Result0 Context0 Result1 Context1 State Bytes T Add Acc Prefix Key Null
    SepP Hi SHA SWU Prefixes FR0 FC0 FR1 FC1 FS FB FT FP FX Input)
    as (mi & x0 & y0 & x1 & y1 & Points & X0 & Y0 & Z0 & Flag0 & X1 & Y1 & Flag1 & BX0 & BY0 & BX1 & BY1 &
      Value0 & Value1 & Accepted0 & Accepted1 & FR0I & FC0I & FR1I & FC1I & FSI & FBI & FTI & FPI & FXI & KeyI & FrameP & ReadP & SHAI & SWUI & PrefixI).
  assert (FGI:Mem.range_perm mi bg 0 64 Cur Freeable) by (keep_owned FG FrameP Distinct).
  destruct (exec_generator_add e (generator_points_temps key le) mi bx bp x0 y0 (point_set_bit_words true) x1 y1
    Acc Add AddFun ltac:(clear -Distinct;intuition congruence) BX0 BY0 mixed_one_bounds BX1 BY1
    X0 Y0 Z0 Flag0 X1 Y1 Flag1 FXI FPI SHAI SWUI PrefixI)
    as (ms & Plus & XS & YS & ZS & FlagS & BXS & BYS & BZS & FXS & FPS & FrameA & ReadA & SHAS & SWUS & PrefixS).
  assert (FGS:Mem.range_perm ms bg 0 64 Cur Freeable) by (keep_owned FGI FrameA Distinct).
  set (sx:=mixed_mode_body_x_words true Int.zero x0 y0 (point_set_bit_words true) x1 y1) in *.
  set (sy:=mixed_mode_body_y_words true Int.zero x0 y0 (point_set_bit_words true) x1 y1) in *.
  set (sz:=mixed_mode_body_z_words true Int.zero x0 y0 (point_set_bit_words true) x1 y1) in *.
  set (sumflag:=mixed_mode_body_flag true Int.zero x0 y0 (point_set_bit_words true) x1 y1) in *.
  assert (GenS:(generator_points_temps key le)!_gen=Some (Vptr bg Ptrofs.zero)) by (rewrite generator_points_gen;exact Gen).
  destruct (exec_generator_finish e (generator_points_temps key le) ms bx bp bg sx sy sz sumflag
    (cmov_int (generator_hash_accepted false key && generator_hash_accepted true key))
    Count Acc Add AffFun SaveFun GenS (generator_points_ret key le)
    ltac:(clear -Distinct;intuition congruence) ltac:(clear -Distinct;intuition congruence) ltac:(clear -Distinct;intuition congruence)
    BXS BYS BZS XS YS ZS FlagS FXS FPS FGS SHAS SWUS PrefixS)
    as (mf & ox & oy & Finish & Saved & BXO & BYO & Finite & Infinite & FXF & FPF & FGF & FrameT & ReadT & SHAF & SWUF & PrefixF).
  assert (FR0F:Mem.range_perm mf br0 0 88 Cur Freeable).
  { assert (Tmp:Mem.range_perm ms br0 0 88 Cur Freeable) by (keep_owned FR0I FrameA Distinct);keep_owned Tmp FrameT Distinct. }
  assert (FC0F:Mem.range_perm mf bc0 0 88 Cur Freeable).
  { assert (Tmp:Mem.range_perm ms bc0 0 88 Cur Freeable) by (keep_owned FC0I FrameA Distinct);keep_owned Tmp FrameT Distinct. }
  assert (FR1F:Mem.range_perm mf br1 0 88 Cur Freeable).
  { assert (Tmp:Mem.range_perm ms br1 0 88 Cur Freeable) by (keep_owned FR1I FrameA Distinct);keep_owned Tmp FrameT Distinct. }
  assert (FC1F:Mem.range_perm mf bc1 0 88 Cur Freeable).
  { assert (Tmp:Mem.range_perm ms bc1 0 88 Cur Freeable) by (keep_owned FC1I FrameA Distinct);keep_owned Tmp FrameT Distinct. }
  assert (FSF:Mem.range_perm mf bs 0 32 Cur Freeable).
  { assert (Tmp:Mem.range_perm ms bs 0 32 Cur Freeable) by (keep_owned FSI FrameA Distinct);keep_owned Tmp FrameT Distinct. }
  assert (FBF:Mem.range_perm mf bb 0 32 Cur Freeable).
  { assert (Tmp:Mem.range_perm ms bb 0 32 Cur Freeable) by (keep_owned FBI FrameA Distinct);keep_owned Tmp FrameT Distinct. }
  assert (FTF:Mem.range_perm mf bt 0 40 Cur Freeable).
  { assert (Tmp:Mem.range_perm ms bt 0 40 Cur Freeable) by (keep_owned FTI FrameA Distinct);keep_owned Tmp FrameT Distinct. }
  assert (Frame:lframe (fun b _=>b<>br0 /\b<>bc0 /\b<>br1 /\b<>bc1 /\b<>bs /\b<>bb /\b<>bt /\b<>bp /\b<>bx /\b<>bg) m mf).
  { eapply lframe_trans.
    - eapply lframe_implies;[exact FrameP|];intros b pos Outside Valid;clear -Outside;tauto.
    - eapply lframe_trans.
      + eapply lframe_implies;[exact FrameA|];intros b pos Outside Valid;clear -Outside;tauto.
      + eapply lframe_implies;[exact FrameT|];intros b pos Outside Valid;clear -Outside;tauto. }
  assert (KeyF:forall i,(i<32)%nat ->Mem.load Mint8unsigned mf ba (Ptrofs.unsigned oa+Z.of_nat i)=
    Some (Vint (nth i (map word8_array_value (vector_values (Word 3) 5 key)) Int.zero))).
  { intros i Index;rewrite (proj1 Frame);[apply Input;exact Index| |intros;clear -Distinct;repeat split;intuition congruence].
    pose proof (Input 0%nat ltac:(clear;lia)) as Load;apply Mem.load_valid_access in Load.
    eapply Mem.valid_access_valid_block;eapply Mem.valid_access_implies;[exact Load|constructor]. }
  exists mf,sx,sy,sz,sumflag,ox,oy;split.
  - rewrite generator_generate_body_source;eapply exec_statement_prefix_then_last;[exact Points|].
    change E0 with (E0**E0);eapply exec_Sseq_1;[exact Plus|exact Finish].
  - split;[exact BXS|];split;[exact BYS|];split;[exact BZS|];split.
    + exact (generator_sum_flag_consistent x0 y0 x1 y1 BX0 BY0 BX1 BY1).
    + split.
      * intros Good0 Good1;unfold sx,sy,sz;rewrite (mixed_xy_affine_outputs_literal x0 y0 x1 y1 BX0 BY0 BX1 BY1),
          (Accepted0 Good0),(Accepted1 Good1);reflexivity.
      * split;[exact Saved|];split;[exact BXO|];split;[exact BYO|];split;[exact Finite|];split;[exact Infinite|];
        split;[exact FR0F|];split;[exact FC0F|];split;[exact FR1F|];split;[exact FC1F|];
        split;[exact FSF|];split;[exact FBF|];split;[exact FTF|];split;[exact FPF|];split;[exact FXF|];split;[exact FGF|];
        split;[exact KeyF|];split;[exact Frame|];split.
        -- eapply preserved_trans;[exact ReadP|];eapply preserved_trans;[exact ReadA|exact ReadT].
        -- split;[exact SHAF|];split;[exact SWUF|exact PrefixF].
Qed.
