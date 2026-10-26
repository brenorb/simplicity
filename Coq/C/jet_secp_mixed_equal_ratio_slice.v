(** The actual mixed-addition equal-point branch with loose raw coordinates
    and an indexed ratio output. The I test and returning doubling call execute. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_fe_math
 C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product C.jet_secp_square_columns
 C.jet_secp_curve_statements C.jet_secp_curve_frame C.jet_secp_field_read_preservation
 C.jet_secp_field_zero_owned C.jet_secp_mixed_zero C.jet_secp_mixed_zero_branch
 C.jet_secp_double_var_ratio_slice C.jet_secp_double_var_owned C.jet_secp_double_all_calls
 C.jet_secp_field_weak_loose C.jet_secp_slice_permissions C.jet_clight_internal_permissions.
Import ListNotations Values Ctypes.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge weak_loose_words.

Definition mixed_equal_slice_frame (bp bi br:block) base (b:block) pos :=
 b<>bp /\ b<>bi /\ (b<>br \/ pos<base \/ base+40<=pos).

Theorem exec_mixed_equal_ratio_slice e le m bp bi br base size x y z i :
 le!_a=Some (Vptr bp Ptrofs.zero) -> le!_r=Some (Vptr bp Ptrofs.zero) ->
 le!_rzr=Some (Vptr br (Ptrofs.repr base)) ->
 e!_i=Some (bi,curve_fe_type) -> e!_secp256k1_fe_normalizes_to_zero_var=None ->
 e!_secp256k1_gej_double_var=None -> bp<>bi -> bp<>br -> bi<>br ->
 0<=base -> (8|base) -> base+40<=size -> size<=Ptrofs.max_unsigned ->
 square_input_bounds x -> square_input_bounds y -> square_input_bounds z -> square_input_bounds i ->
 radix_value i mod feP=0 -> Mem.load Mint32 m bp 120=Some (Vint Int.zero) ->
 fe_at m bp 0 (words5 x) -> fe_at m bp 40 (words5 y) -> fe_at m bp 80 (words5 z) ->
 fe_at m bi 0 (words5 i) -> Mem.range_perm m bp 0 128 Cur Freeable ->
 Mem.range_perm m bi 0 40 Cur Freeable -> Mem.range_perm m br 0 size Cur Freeable -> exists mf,
 Clight2.exec_stmt secp_ge e le m mixed_zero_branch E0
  (PTree.set _t'1 (Vint Int.one) le) mf (Out_return None) /\
 fe_at mf bp 0 (words5 (double_output_x_words x y)) /\
 fe_at mf bp 40 (words5 (double_output_y_words x y)) /\
 fe_at mf bp 80 (words5 (double_output_z_words y z)) /\
 Mem.load Mint32 mf bp 120=Some (Vint (double_var_zflag y z)) /\
 fe_at mf bi 0 (words5 i) /\ fe_at mf br base (words5 (weak_loose_words y)) /\
 Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf bi 0 40 Cur Freeable /\
 Mem.range_perm mf br 0 size Cur Freeable /\
 square_input_bounds (double_output_x_words x y) /\ square_input_bounds (double_output_y_words x y) /\
 square_input_bounds (double_output_z_words y z) /\ square_input_bounds (weak_loose_words y) /\
 lframe (mixed_equal_slice_frame bp bi br base) m mf.
Proof.
 intros A R Ratio ILocal ZeroGlobal DoubleGlobal PI PR IR Base Align Fit Max BX BY BZ BI IZ Flag X Y Z I
  FreeP FreeI FreeR.
 destruct (exec_mixed_zero_call true i e le m bi ILocal ZeroGlobal BI I FreeI)
  as (mz & TestI & IZ0 & FreeIZ & FrameI).
 assert (Result:field_zero_result i=Int.one) by (unfold field_zero_result;rewrite IZ,Z.eqb_refl;reflexivity).
 rewrite Result in TestI.
 assert (XZ:fe_at mz bp 0 (words5 x)) by
  (eapply field_at_lframe;[exact X|exact FrameI|];intros;exact PI).
 assert (YZ:fe_at mz bp 40 (words5 y)) by
  (eapply field_at_lframe;[exact Y|exact FrameI|];intros;exact PI).
 assert (ZZ:fe_at mz bp 80 (words5 z)) by
  (eapply field_at_lframe;[exact Z|exact FrameI|];intros;exact PI).
 assert (FreePZ:Mem.range_perm mz bp 0 128 Cur Freeable) by
  (eapply curve_keep_free;[lia|exact FreeP|exact FrameI|];intros;exact PI).
 assert (FreeRZ:Mem.range_perm mz br 0 size Cur Freeable) by
  (eapply curve_keep_free;[lia|exact FreeR|exact FrameI|];intros;congruence).
 assert (FlagZ:Mem.load Mint32 mz bp 120=Some (Vint Int.zero)).
 { rewrite (proj1 FrameI Mint32 bp 120);[exact Flag| |intros;exact PI].
   eapply Mem.perm_valid_block;apply (FreeP 0);lia. }
 destruct (eval_double_var_finite_ratio_slice x y z mz bp br base size PR Base Align Fit Max BX BY BZ
   FlagZ XZ YZ ZZ FreePZ FreeRZ)
  as (mf & Double & XO & YO & ZO & FlagO & RatioY & FreePO & FreeRO & BXO & BYO & BZO & BoundsRatio
   & KeepD & FrameD & ReadonlyD).
 assert (IO:fe_at mf bi 0 (words5 i)).
 { eapply field_at_lframe;[exact IZ0|exact FrameD|];intros;split;[congruence|left;exact IR]. }
 assert (FreeIO:Mem.range_perm mf bi 0 40 Cur Freeable) by
  (eapply keeps_range_permissions;[exact KeepD|exact FreeIZ]).
 exists mf;split.
 - rewrite mixed_i_zero_source;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mf)
    (le1:=PTree.set _t'1 (Vint Int.one) le).
   + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mz) (le1:=PTree.set _t'1 (Vint Int.one) le);
      [exact TestI|].
     rewrite mixed_i_dispatch_source;eapply exec_Sifthenelse with (v1:=Vint Int.one) (b:=true).
     * apply eval_Etempvar;apply PTree.gss.
     * reflexivity.
     * unfold mixed_double_call;eapply exec_curve_call with
        (vargs:=[Vptr bp Ptrofs.zero;Vptr bp Ptrofs.zero;Vptr br (Ptrofs.repr base)]) (v:=Vundef).
       -- unfold C.jet_secp_fns.secp_pure;repeat (first [left;reflexivity|right]).
       -- exact DoubleGlobal.
       -- eapply eval_Econs;[apply eval_Etempvar;rewrite PTree.gso by discriminate;exact R|reflexivity|].
          eapply eval_Econs;[apply eval_Etempvar;rewrite PTree.gso by discriminate;exact A|reflexivity|].
          eapply eval_Econs;[apply eval_Etempvar;rewrite PTree.gso by discriminate;exact Ratio|reflexivity|constructor].
       -- exact Double.
   + apply exec_Sreturn_none.
 - split;[exact XO|];split;[exact YO|];split;[exact ZO|];split;[exact FlagO|];split;[exact IO|];
    split;[exact RatioY|];split;[exact FreePO|];split;[exact FreeIO|];split;[exact FreeRO|];
    split;[exact BXO|];split;[exact BYO|];split;[exact BZO|];split;[exact BoundsRatio|].
   eapply lframe_trans.
   + eapply lframe_implies;[exact FrameI|];intros b pos (NP & NI & Outside) Valid;exact NI.
   + eapply lframe_implies;[exact FrameD|];intros b pos (NP & NI & Outside) Valid;split;assumption.
Qed.
