(** The original H=0, I<>0 mixed-addition branch: an indexed ratio is set
    to zero by the actual set_int call, then the point is set to infinity. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_fe_math
 C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product C.jet_secp_square_columns
 C.jet_secp_curve_statements C.jet_secp_curve_frame C.jet_secp_field_read_preservation
 C.jet_secp_field_zero_owned C.jet_secp_mixed_zero C.jet_secp_mixed_zero_branch
 C.jet_secp_double_var_ratio_slice C.jet_secp_mixed_equal_ratio_slice C.jet_secp_field_slice_set
 C.jet_secp_point_set_bit C.jet_secp_gej_infinity_owned C.jet_secp_local_regions
 C.jet_secp_double_var_owned C.jet_secp_double_all_calls C.jet_secp_field_weak_loose C.jet_secp_mixed_zero_return
 C.jet_secp_slice_permissions C.jet_clight_internal_permissions.
Import ListNotations Values Ctypes.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Theorem exec_mixed_inverse_ratio_slice e le m bp bi br base size i :
 le!_r=Some (Vptr bp Ptrofs.zero) -> le!_rzr=Some (Vptr br (Ptrofs.repr base)) ->
 e!_i=Some (bi,curve_fe_type) -> e!_secp256k1_fe_normalizes_to_zero_var=None ->
 e!_secp256k1_gej_set_infinity=None -> e!_secp256k1_fe_set_int=None ->
 bp<>bi -> bp<>br -> bi<>br ->
 0<=base -> (8|base) -> base+40<=size -> size<=Ptrofs.max_unsigned ->
 square_input_bounds i -> radix_value i mod feP<>0 -> fe_at m bi 0 (words5 i) ->
 Mem.range_perm m bp 0 128 Cur Freeable -> Mem.range_perm m bi 0 40 Cur Freeable ->
 Mem.range_perm m br 0 size Cur Freeable -> exists mf,
 Clight2.exec_stmt secp_ge e le m mixed_zero_branch E0
  (PTree.set _t'1 (Vint Int.zero) le) mf (Out_return None) /\
 fe_at mf bp 0 (repeat Int64.zero 5) /\ fe_at mf bp 40 (repeat Int64.zero 5) /\
 fe_at mf bp 80 (repeat Int64.zero 5) /\ Mem.load Mint32 mf bp 120=Some (Vint Int.one) /\
 fe_at mf bi 0 (words5 i) /\ fe_at mf br base (words5 (point_set_bit_words false)) /\
 Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf bi 0 40 Cur Freeable /\
 Mem.range_perm mf br 0 size Cur Freeable /\ lframe (mixed_equal_slice_frame bp bi br base) m mf.
Proof.
 intros R Ratio ILocal ZeroGlobal InfinityGlobal SetGlobal PI PR IR Base Align Fit Max BI Nonzero I FreeP FreeI FreeR.
 destruct (exec_mixed_zero_call true i e le m bi ILocal ZeroGlobal BI I FreeI)
  as (mz & TestI & IZ & FreeIZ & FrameI).
 assert (Result:field_zero_result i=Int.zero) by
  (unfold field_zero_result;apply Z.eqb_neq in Nonzero;rewrite Nonzero;reflexivity).
 rewrite Result in TestI.
 assert (FreePZ:Mem.range_perm mz bp 0 128 Cur Freeable) by
  (eapply curve_keep_free;[lia|exact FreeP|exact FrameI|];intros;exact PI).
 assert (FreeRZ:Mem.range_perm mz br 0 size Cur Freeable) by
  (eapply curve_keep_free;[lia|exact FreeR|exact FrameI|];intros;congruence).
 destruct (eval_field_slice_set false mz br base Base Align ltac:(lia)
   ltac:(intros pos Range;apply (freeable_range_writable _ _ _ _ FreeRZ);lia))
  as (ms & SetCall & RatioS & KeepS & FrameS & ReadonlyS).
 assert (FreePS:Mem.range_perm ms bp 0 128 Cur Freeable) by
  (eapply keeps_range_permissions;[exact KeepS|exact FreePZ]).
 assert (FreeIS:Mem.range_perm ms bi 0 40 Cur Freeable) by
  (eapply keeps_range_permissions;[exact KeepS|exact FreeIZ]).
 assert (FreeRS:Mem.range_perm ms br 0 size Cur Freeable) by
  (eapply keeps_range_permissions;[exact KeepS|exact FreeRZ]).
 assert (IS:fe_at ms bi 0 (words5 i)) by
  (eapply field_at_lframe;[exact IZ|exact FrameS|];intros;left;exact IR).
 destruct (eval_gej_infinity_initializer_owned ms bp 0 ltac:(lia) ltac:(exists 0;reflexivity)
   ltac:(change (128<=18446744073709551615);lia) (freeable_range_writable _ _ _ _ FreePS))
  as (mf & Infinity & XO & YO & ZO & FlagO & Loads & Perm & Valid).
 assert (FrameInfinity:lframe (fun b _=>b<>bp) ms mf).
 { split.
   - intros ch b pos Old Outside;apply Loads;left;apply (Outside pos);pose proof (size_chunk_pos ch);lia.
   - split;[intros b pos k p Old Outside PermS;apply (proj2 (Perm b pos k p));exact PermS|exact Valid]. }
 assert (IF:fe_at mf bi 0 (words5 i)) by
  (eapply field_at_lframe;[exact IS|exact FrameInfinity|];intros;congruence).
 assert (RatioF:fe_at mf br base (words5 (point_set_bit_words false))) by
  (eapply field_at_lframe;[exact RatioS|exact FrameInfinity|];intros;congruence).
 assert (FreePF:Mem.range_perm mf bp 0 128 Cur Freeable).
 { intros pos Range;apply (proj2 (Perm bp pos Cur Freeable));apply FreePS;exact Range. }
 assert (FreeIF:Mem.range_perm mf bi 0 40 Cur Freeable).
 { intros pos Range;apply (proj2 (Perm bi pos Cur Freeable));apply FreeIS;exact Range. }
 assert (FreeRF:Mem.range_perm mf br 0 size Cur Freeable).
 { intros pos Range;apply (proj2 (Perm br pos Cur Freeable));apply FreeRS;exact Range. }
 exists mf;split.
 - rewrite mixed_i_zero_source;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mf)
    (le1:=PTree.set _t'1 (Vint Int.zero) le).
   + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mz) (le1:=PTree.set _t'1 (Vint Int.zero) le);
      [exact TestI|].
     rewrite mixed_i_dispatch_source;eapply exec_Sifthenelse with (v1:=Vint Int.zero) (b:=false).
     * apply eval_Etempvar;apply PTree.gss.
     * reflexivity.
     * rewrite mixed_inverse_source;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=ms)
        (le1:=PTree.set _t'1 (Vint Int.zero) le).
       -- eapply exec_Sifthenelse with (v1:=Vint Int.one) (b:=true).
          ++ apply eval_double_var_nonnull_slice with (br:=br) (base:=base).
             ** lia.
             ** rewrite PTree.gso by discriminate;exact Ratio.
             ** apply Mem.valid_pointer_nonempty_perm;eapply Mem.perm_implies;
                 [apply (FreeRZ base);lia|constructor].
          ++ reflexivity.
          ++ change (Clight2.exec_stmt secp_ge e (PTree.set _t'1 (Vint Int.zero) le) mz
              (curve_call _secp256k1_fe_set_int f_secp256k1_fe_set_int None
                [Etempvar _rzr (tptr curve_fe_type);Econst_int Int.zero tint])
              E0 (PTree.set _t'1 (Vint Int.zero) le) ms Out_normal).
             eapply exec_curve_call with (vargs:=[Vptr br (Ptrofs.repr base);Vint Int.zero]) (v:=Vundef).
             ** unfold C.jet_secp_fns.secp_pure;repeat (first [left;reflexivity|right]).
             ** exact SetGlobal.
             ** eapply eval_Econs;[apply eval_Etempvar;rewrite PTree.gso by discriminate;exact Ratio|reflexivity|].
                eapply eval_Econs;[constructor|reflexivity|constructor].
             ** exact SetCall.
       -- unfold mixed_infinity_call;eapply exec_curve_call with (vargs:=[Vptr bp Ptrofs.zero]) (v:=Vundef).
          ++ unfold C.jet_secp_fns.secp_pure;repeat (first [left;reflexivity|right]).
          ++ exact InfinityGlobal.
          ++ eapply eval_Econs;[apply eval_Etempvar;rewrite PTree.gso by discriminate;exact R|reflexivity|constructor].
          ++ exact Infinity.
   + apply exec_Sreturn_none.
 - split;[exact XO|];split;[exact YO|];split;[exact ZO|];split;[exact FlagO|];split;[exact IF|];
    split;[exact RatioF|];split;[exact FreePF|];split;[exact FreeIF|];split;[exact FreeRF|].
   eapply lframe_trans.
   + eapply lframe_implies;[exact FrameI|];intros b pos (NP & NI & Outside) Old;exact NI.
   + eapply lframe_trans.
     * eapply lframe_implies;[exact FrameS|];intros b pos (NP & NI & Outside) Old;exact Outside.
     * eapply lframe_implies;[exact FrameInfinity|];intros b pos (NP & NI & Outside) Old;exact NP.
Qed.

Definition mixed_zero_slice_frame (bp bh bi br:block) base (b:block) pos :=
 b<>bp /\ b<>bh /\ b<>bi /\ (b<>br \/ pos<base \/ base+40<=pos).

Theorem exec_mixed_zero_head_ratio_slice e le m bp bh bi br base size x y z h i :
 le!_a=Some (Vptr bp Ptrofs.zero) -> le!_r=Some (Vptr bp Ptrofs.zero) ->
 le!_rzr=Some (Vptr br (Ptrofs.repr base)) ->
 e!_h=Some (bh,curve_fe_type) -> e!_i=Some (bi,curve_fe_type) ->
 e!_secp256k1_fe_normalizes_to_zero_var=None -> e!_secp256k1_gej_double_var=None ->
 e!_secp256k1_gej_set_infinity=None -> e!_secp256k1_fe_set_int=None ->
 NoDup [bp;bh;bi;br] -> 0<=base -> (8|base) -> base+40<=size -> size<=Ptrofs.max_unsigned ->
 square_input_bounds x -> square_input_bounds y -> square_input_bounds z ->
 square_input_bounds h -> square_input_bounds i -> radix_value h mod feP=0 ->
 Mem.load Mint32 m bp 120=Some (Vint Int.zero) ->
 fe_at m bp 0 (words5 x) -> fe_at m bp 40 (words5 y) -> fe_at m bp 80 (words5 z) ->
 fe_at m bh 0 (words5 h) -> fe_at m bi 0 (words5 i) ->
 Mem.range_perm m bp 0 128 Cur Freeable -> Mem.range_perm m bh 0 40 Cur Freeable ->
 Mem.range_perm m bi 0 40 Cur Freeable -> Mem.range_perm m br 0 size Cur Freeable -> exists mf,
 Clight2.exec_stmt secp_ge e le m mixed_zero_head E0 (mixed_zero_return_temps le i) mf (Out_return None) /\
 fe_at mf bp 0 (words5 (mixed_zero_words i (double_output_x_words x y))) /\
 fe_at mf bp 40 (words5 (mixed_zero_words i (double_output_y_words x y))) /\
 fe_at mf bp 80 (words5 (mixed_zero_words i (double_output_z_words y z))) /\
 Mem.load Mint32 mf bp 120=Some (Vint (mixed_zero_flag i y z)) /\
 fe_at mf bh 0 (words5 h) /\ fe_at mf bi 0 (words5 i) /\
 fe_at mf br base (words5 (mixed_zero_words i (weak_loose_words y))) /\
 Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf bh 0 40 Cur Freeable /\
 Mem.range_perm mf bi 0 40 Cur Freeable /\ Mem.range_perm mf br 0 size Cur Freeable /\
 square_input_bounds (mixed_zero_words i (double_output_x_words x y)) /\
 square_input_bounds (mixed_zero_words i (double_output_y_words x y)) /\
 square_input_bounds (mixed_zero_words i (double_output_z_words y z)) /\
 square_input_bounds (mixed_zero_words i (weak_loose_words y)) /\
 lframe (mixed_zero_slice_frame bp bh bi br base) m mf.
Proof.
 intros A R Ratio HLocal ILocal ZeroGlobal DoubleGlobal InfinityGlobal SetGlobal Distinct Base Align Fit Max
  BX BY BZ BH BI HZero Flag X Y Z H I FreeP FreeH FreeI FreeR.
 assert (Apart:bp<>bh /\ bp<>bi /\ bp<>br /\ bh<>bi /\ bh<>br /\ bi<>br).
 { clear -Distinct;repeat match goal with ND:NoDup (_::_) |- _=>inversion ND;subst;clear ND end;
    cbn [In] in *;intuition congruence. }
 destruct Apart as (PH & PI & PR & HI & HR & IR).
 destruct (exec_mixed_zero_call false h e le m bh HLocal ZeroGlobal BH H FreeH)
  as (mh & TestH & HH & FreeHH & FrameH).
 assert (HResult:field_zero_result h=Int.one) by (unfold field_zero_result;rewrite HZero;reflexivity).
 rewrite HResult in TestH.
 set (lh:=PTree.set _t'2 (Vint Int.one) le).
 assert (AH:lh!_a=Some (Vptr bp Ptrofs.zero)) by (unfold lh;rewrite PTree.gso by discriminate;exact A).
 assert (RH:lh!_r=Some (Vptr bp Ptrofs.zero)) by (unfold lh;rewrite PTree.gso by discriminate;exact R).
 assert (RatioH:lh!_rzr=Some (Vptr br (Ptrofs.repr base))) by
  (unfold lh;rewrite PTree.gso by discriminate;exact Ratio).
 assert (XH:fe_at mh bp 0 (words5 x)) by
  (eapply field_at_lframe;[exact X|exact FrameH|];intros;exact PH).
 assert (YH:fe_at mh bp 40 (words5 y)) by
  (eapply field_at_lframe;[exact Y|exact FrameH|];intros;exact PH).
 assert (ZH:fe_at mh bp 80 (words5 z)) by
  (eapply field_at_lframe;[exact Z|exact FrameH|];intros;exact PH).
 assert (IH:fe_at mh bi 0 (words5 i)) by
  (eapply field_at_lframe;[exact I|exact FrameH|];intros;congruence).
 assert (FreePH:Mem.range_perm mh bp 0 128 Cur Freeable) by
  (eapply curve_keep_free;[lia|exact FreeP|exact FrameH|];intros;exact PH).
 assert (FreeIH:Mem.range_perm mh bi 0 40 Cur Freeable) by
  (eapply curve_keep_free;[lia|exact FreeI|exact FrameH|];intros;congruence).
 assert (FreeRH:Mem.range_perm mh br 0 size Cur Freeable) by
  (eapply curve_keep_free;[lia|exact FreeR|exact FrameH|];intros;congruence).
 assert (FlagH:Mem.load Mint32 mh bp 120=Some (Vint Int.zero)).
 { rewrite (proj1 FrameH Mint32 bp 120);[exact Flag| |intros;exact PH].
   eapply Mem.perm_valid_block;apply (FreeP 0);lia. }
 assert (Branch:exists mf,
   Clight2.exec_stmt secp_ge e lh mh mixed_zero_branch E0
    (PTree.set _t'1 (Vint (field_zero_result i)) lh) mf (Out_return None) /\
   fe_at mf bp 0 (words5 (mixed_zero_words i (double_output_x_words x y))) /\
   fe_at mf bp 40 (words5 (mixed_zero_words i (double_output_y_words x y))) /\
   fe_at mf bp 80 (words5 (mixed_zero_words i (double_output_z_words y z))) /\
   Mem.load Mint32 mf bp 120=Some (Vint (mixed_zero_flag i y z)) /\ fe_at mf bi 0 (words5 i) /\
   fe_at mf br base (words5 (mixed_zero_words i (weak_loose_words y))) /\
   Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf bi 0 40 Cur Freeable /\
   Mem.range_perm mf br 0 size Cur Freeable /\
   square_input_bounds (mixed_zero_words i (double_output_x_words x y)) /\
   square_input_bounds (mixed_zero_words i (double_output_y_words x y)) /\
   square_input_bounds (mixed_zero_words i (double_output_z_words y z)) /\
   square_input_bounds (mixed_zero_words i (weak_loose_words y)) /\
   lframe (mixed_equal_slice_frame bp bi br base) mh mf).
 { unfold mixed_zero_words,mixed_zero_flag,field_zero_result.
   destruct (Z.eqb (radix_value i mod feP) 0) eqn:IZero.
   - apply Z.eqb_eq in IZero.
     destruct (exec_mixed_equal_ratio_slice e lh mh bp bi br base size x y z i AH RH RatioH ILocal ZeroGlobal
       DoubleGlobal PI PR IR Base Align Fit Max BX BY BZ BI IZero FlagH XH YH ZH IH FreePH FreeIH FreeRH)
      as (mf & Run & XO & YO & ZO & FlagO & IO & RY & FreePO & FreeIO & FreeRO & BXO & BYO & BZO & BRY & Frame).
     exists mf;repeat (first [assumption|split]).
   - apply Z.eqb_neq in IZero.
     destruct (exec_mixed_inverse_ratio_slice e lh mh bp bi br base size i RH RatioH ILocal ZeroGlobal
       InfinityGlobal SetGlobal PI PR IR Base Align Fit Max BI IZero IH FreePH FreeIH FreeRH)
      as (mf & Run & XO & YO & ZO & FlagO & IO & RZ & FreePO & FreeIO & FreeRO & Frame).
     exists mf;repeat (first [assumption|exact square_zero_bounds|split]). }
 destruct Branch as (mf & Run & XO & YO & ZO & FlagO & IO & RO & FreePO & FreeIO & FreeRO & BXO & BYO & BZO & BRO & FrameB).
 assert (HO:fe_at mf bh 0 (words5 h)).
 { eapply field_at_lframe;[exact HH|exact FrameB|];intros;split;[congruence|];split;[exact HI|left;exact HR]. }
 assert (FreeHO:Mem.range_perm mf bh 0 40 Cur Freeable).
 { eapply curve_keep_free;[lia|exact FreeHH|exact FrameB|];intros;split;[congruence|];split;[exact HI|left;exact HR]. }
 exists mf;split.
 - change (Clight2.exec_stmt secp_ge e le m
    (Ssequence (mixed_zero_call false) (Sifthenelse (Etempvar _t'2 tint) mixed_zero_branch Sskip))
    E0 (mixed_zero_return_temps le i) mf (Out_return None)).
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mh) (le1:=lh);[exact TestH|].
   eapply exec_Sifthenelse with (v1:=Vint Int.one) (b:=true).
   + apply eval_Etempvar;unfold lh;apply PTree.gss.
   + reflexivity.
   + exact Run.
 - split;[exact XO|];split;[exact YO|];split;[exact ZO|];split;[exact FlagO|];split;[exact HO|];split;[exact IO|];
    split;[exact RO|];split;[exact FreePO|];split;[exact FreeHO|];split;[exact FreeIO|];split;[exact FreeRO|];
    split;[exact BXO|];split;[exact BYO|];split;[exact BZO|];split;[exact BRO|].
   eapply lframe_trans.
   + eapply lframe_implies;[exact FrameH|];intros b pos (NP & NH & NI & Outside) Old;exact NH.
   + eapply lframe_implies;[exact FrameB|];intros b pos (NP & NH & NI & Outside) Old;split;[exact NP|];split;assumption.
Qed.
