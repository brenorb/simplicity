(** Original double_var ratio path at an arbitrary caller-owned array slice.
    Loose Y is normalized in the ratio output, while doubling reads raw Y. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_exec C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv
 C.jet_secp_double_var_ratio C.jet_secp_double_var_statements C.jet_secp_double_var_owned
 C.jet_secp_double_function C.jet_secp_double_all_calls C.jet_secp_point_normalizes_zero
 C.jet_secp_point_write_run C.jet_secp_square_columns C.jet_secp_multiply_normalize_bridge
 C.jet_secp_curve_frame C.jet_secp_local_regions C.jet_secp_field_read_preservation
 C.jet_secp_field_copy_owned C.jet_secp_mixed_copy_weak C.jet_secp_field_slice_weak
 C.jet_secp_field_weak_loose C.jet_secp_curve_statements C.jet_secp_double_statements
 C.jet_secp_slice_permissions C.jet_clight_internal_permissions C.jet_clight_internal_preserve
 C.jet_secp_closed_helpers.
Import ListNotations Values Ctypes.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge weak_loose_words.

Lemma eval_double_var_nonnull_slice e le m br base : 0<=base<=Ptrofs.max_unsigned ->
 le!_rzr=Some (Vptr br (Ptrofs.repr base)) -> Mem.valid_pointer m br base=true ->
 eval_expr secp_ge e le m double_var_null_test (Vint Int.one).
Proof.
 intros Base R Valid;unfold double_var_null_test.
 eapply eval_Ebinop with (v1:=Vptr br (Ptrofs.repr base)) (v2:=Vlong Int64.zero).
 - apply eval_Etempvar;exact R.
 - eapply eval_Ecast with (v1:=Vint Int.zero);[constructor|reflexivity].
 - change (option_map Val.of_bool
     (if (Mem.valid_pointer m br (Ptrofs.unsigned (Ptrofs.repr base)) ||
       Mem.valid_pointer m br (Ptrofs.unsigned (Ptrofs.repr base)-1))%bool
      then Some true else None)=Some (Vint Int.one)).
   rewrite Ptrofs.unsigned_repr by exact Base;rewrite Valid;reflexivity.
Qed.

Definition double_var_slice_temps ba br base := PTree.set _rzr (Vptr br (Ptrofs.repr base))
 (PTree.set _a (Vptr ba Ptrofs.zero) (PTree.set _r (Vptr ba Ptrofs.zero)
 (create_undef_temps (fn_temps f_secp256k1_gej_double_var)))).
Lemma double_var_slice_entry m ba br base : function_entry2 secp_ge f_secp256k1_gej_double_var
 [Vptr ba Ptrofs.zero;Vptr ba Ptrofs.zero;Vptr br (Ptrofs.repr base)]
 m empty_env (double_var_slice_temps ba br base) m.
Proof.
 destruct (fn_okb_true _ double_var_function_ok) as (Vars & Params & Disjoint).
 constructor;[exact Vars|exact Params|exact Disjoint|constructor|reflexivity].
Qed.

Theorem exec_double_var_ratio_slice e le m ba br base y :
 le!_a=Some (Vptr ba Ptrofs.zero) -> le!_rzr=Some (Vptr br (Ptrofs.repr base)) ->
 e!_secp256k1_fe_normalize_weak=None -> ba<>br ->
 0<=base -> (8|base) -> base+40<=Ptrofs.max_unsigned ->
 (forall i,(i<5)%nat -> Int64.unsigned (y i)<=2^60) ->
 fe_at m ba 40 (words5 y) -> Mem.range_perm m ba 0 128 Cur Freeable ->
 Mem.range_perm m br base (base+40) Cur Freeable -> exists mf,
 Clight2.exec_stmt secp_ge e le m
  (Sifthenelse double_var_null_test (Ssequence double_var_ratio_copy double_var_ratio_weak) Sskip)
  E0 le mf Out_normal /\
 fe_at mf br base (words5 (weak_loose_words y)) /\ fe_at mf ba 40 (words5 y) /\
 Mem.range_perm mf br base (base+40) Cur Freeable /\ Mem.range_perm mf ba 0 128 Cur Freeable /\
 square_input_bounds (weak_loose_words y) /\ keeps_permissions m mf /\
 lframe (fun b pos=>b<>br \/ pos<base \/ base+40<=pos) m mf /\ readonly_preserved m mf.
Proof.
 intros A R Global Separate Base Align Max Bound Y FreeA FreeR.
 destruct (exec_field_copy_owned e le m (double_point_field _a _y curve_fe_type)
   (Ederef (Etempvar _rzr (tptr curve_fe_type)) curve_fe_type) ba 40 br base y eq_refl eq_refl
   ltac:(eapply eval_Elvalue;[exact (eval_mixed_a_copy_field e le m ba true A)|apply deref_loc_copy;reflexivity])
   ltac:(apply eval_Ederef;apply eval_Etempvar;exact R) Separate Y Base Align Max FreeR)
  as (mc & Copy & YC & PermC & FrameC).
 destruct (eval_field_slice_weak y mc br base Bound YC)
  as (mf & Weak & YF & Numeric & Bounds & KeepW & FrameW & ReadonlyW).
 assert (Keep:keeps_permissions m mf).
 { intros b pos k p Perm;apply KeepW;apply (proj2 (PermC b pos k p));exact Perm. }
 assert (Frame:lframe (fun b pos=>b<>br \/ pos<base \/ base+40<=pos) m mf) by
  (eapply lframe_trans;[exact FrameC|exact FrameW]).
 exists mf;split.
 - eapply exec_Sifthenelse with (v1:=Vint Int.one) (b:=true).
   + apply eval_double_var_nonnull_slice with (br:=br) (base:=base);[lia|exact R|].
     apply Mem.valid_pointer_nonempty_perm;eapply Mem.perm_implies;[apply (FreeR base);lia|constructor].
   + reflexivity.
   + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le) (m1:=mc);[exact Copy|].
     unfold double_var_ratio_weak;eapply exec_curve_call with (vargs:=[Vptr br (Ptrofs.repr base)]) (v:=Vundef).
     * unfold C.jet_secp_fns.secp_pure;repeat (first [left;reflexivity|right]).
     * exact Global.
     * eapply eval_Econs;[apply eval_Etempvar;exact R|reflexivity|constructor].
     * exact Weak.
 - split;[exact YF|];split.
   + eapply field_at_lframe;[exact Y|exact Frame|];intros;left;exact Separate.
   + split;[eapply keeps_range_permissions;[exact Keep|exact FreeR]|];
      split;[eapply keeps_range_permissions;[exact Keep|exact FreeA]|];split;[exact Bounds|];
      split;[exact Keep|];split;[exact Frame|].
     eapply preserved_trans;[|exact ReadonlyW];inversion Copy;subst;eapply assign_preserved;eassumption.
Qed.

Theorem eval_double_var_finite_ratio_slice x y z m ba br base size :
 ba<>br -> 0<=base -> (8|base) -> base+40<=size -> size<=Ptrofs.max_unsigned ->
 square_input_bounds x -> square_input_bounds y -> square_input_bounds z ->
 Mem.load Mint32 m ba 120=Some (Vint Int.zero) ->
 fe_at m ba 0 (words5 x) -> fe_at m ba 40 (words5 y) -> fe_at m ba 80 (words5 z) ->
 Mem.range_perm m ba 0 128 Cur Freeable -> Mem.range_perm m br 0 size Cur Freeable -> exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_gej_double_var)
  [Vptr ba Ptrofs.zero;Vptr ba Ptrofs.zero;Vptr br (Ptrofs.repr base)] E0 mf Vundef /\
 fe_at mf ba 0 (words5 (double_output_x_words x y)) /\
 fe_at mf ba 40 (words5 (double_output_y_words x y)) /\
 fe_at mf ba 80 (words5 (double_output_z_words y z)) /\
 Mem.load Mint32 mf ba 120=Some (Vint (double_var_zflag y z)) /\
 fe_at mf br base (words5 (weak_loose_words y)) /\
 Mem.range_perm mf ba 0 128 Cur Freeable /\ Mem.range_perm mf br 0 size Cur Freeable /\
 square_input_bounds (double_output_x_words x y) /\ square_input_bounds (double_output_y_words x y) /\
 square_input_bounds (double_output_z_words y z) /\ square_input_bounds (weak_loose_words y) /\
 keeps_permissions m mf /\
 lframe (fun b pos=>b<>ba /\ (b<>br \/ pos<base \/ base+40<=pos)) m mf /\ readonly_preserved m mf.
Proof.
 intros Separate Base Align Fit Max BX BY BZ Flag X Y Z FreeA FreeR.
 set (le0:=double_var_slice_temps ba br base).
 set (le1:=PTree.set _t'2 (Vint Int.zero) le0).
 assert (A:le1!_a=Some (Vptr ba Ptrofs.zero)) by reflexivity.
 assert (R:le1!_r=Some (Vptr ba Ptrofs.zero)) by reflexivity.
 assert (Ratio:le1!_rzr=Some (Vptr br (Ptrofs.repr base))) by reflexivity.
 destruct (exec_double_var_ratio_slice empty_env le1 m ba br base y A Ratio eq_refl Separate Base Align ltac:(lia)
   ltac:(intros i Bound;pose proof (square_input56 _ BY i Bound);lia) Y FreeA
   ltac:(intros pos Range;apply FreeR;lia))
  as (mr & RatioRun & RatioY & YR & FreeRatio & FreeAR & RatioBounds & KeepR & FrameR & ReadonlyR).
 assert (XR:fe_at mr ba 0 (words5 x)) by
  (eapply field_at_lframe;[exact X|exact FrameR|];intros;left;exact Separate).
 assert (ZR:fe_at mr ba 80 (words5 z)) by
  (eapply field_at_lframe;[exact Z|exact FrameR|];intros;left;exact Separate).
 assert (FlagR:Mem.load Mint32 mr ba 120=Some (Vint Int.zero)).
 { rewrite (proj1 FrameR Mint32 ba 120);[exact Flag| |intros;left;exact Separate].
   eapply Mem.perm_valid_block;apply (FreeA 0);lia. }
 destruct (eval_double_function x y z mr ba Int.zero BX BY BZ FlagR XR YR ZR FreeAR)
  as (md & Double & XD & YD & ZD & FreeD & BXD & BYD & BZD & FrameD).
 destruct (eval_point_normalizes_zero PointZ (double_output_z_words y z) md ba BZD ZD FreeD)
  as (mz & Zero & ZZ & FreeZ & FrameZ).
 assert (XZ:fe_at mz ba 0 (words5 (double_output_x_words x y))).
 { eapply curve_keep_field_range;[reflexivity|exact XD|exact FrameZ|];intros pos Range;right;left;
    change (pos<80);lia. }
 assert (YZ:fe_at mz ba 40 (words5 (double_output_y_words x y))).
 { eapply curve_keep_field_range;[reflexivity|exact YD|exact FrameZ|];intros pos Range;right;left;
    change (pos<80);lia. }
 destruct (double_var_store_flag (double_output_x_words x y) (double_output_y_words x y)
   (double_output_z_words y z) mz ba (double_var_zflag y z) XZ YZ ZZ FreeZ)
  as (mf & Store & FlagF & XF & YF & ZF & FreeAF & FrameFlag).
 assert (FrameTail:lframe (fun b _=>b<>ba) mr mf).
 { eapply lframe_trans;[exact FrameD|];eapply lframe_trans;
    eapply lframe_implies;[exact FrameZ| |exact FrameFlag|];intros b pos NotA Valid;left;exact NotA. }
 assert (RatioF:fe_at mf br base (words5 (weak_loose_words y))) by
  (eapply field_at_lframe;[exact RatioY|exact FrameTail|];intros;congruence).
 assert (Call:Clight2.eval_funcall secp_ge m (Internal f_secp256k1_gej_double_var)
   [Vptr ba Ptrofs.zero;Vptr ba Ptrofs.zero;Vptr br (Ptrofs.repr base)] E0 mf Vundef).
 { eapply eval_funcall_internal with (e:=empty_env) (le1:=le0)
    (le2:=PTree.set _t'1 (Vint (double_var_zflag y z)) le1) (m1:=m) (m2:=mf) (out:=Out_normal).
   - exact (double_var_slice_entry m ba br base).
   - rewrite double_var_source;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le1) (m1:=m).
     + apply exec_double_var_head_finite with (ba:=ba);[reflexivity|exact Flag].
     + rewrite double_var_ratio_source;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le1) (m1:=mr);
        [exact RatioRun|].
       exact (exec_double_var_post_ratio_from_calls empty_env le1 mr md mz mf ba (double_var_zflag y z)
        A R eq_refl eq_refl Double Zero Store).
   - reflexivity.
   - reflexivity. }
 assert (Keep:keeps_permissions m mf) by
  (eapply (secp_internal_keeps_permissions f_secp256k1_gej_double_var);[reflexivity|reflexivity|exact Call]).
 exists mf;split;[exact Call|];split;[exact XF|];split;[exact YF|];split;[exact ZF|];
  split;[exact FlagF|];split;[exact RatioF|];split;[exact FreeAF|];split.
 - eapply keeps_range_permissions;[exact Keep|exact FreeR].
 - split;[exact BXD|];split;[exact BYD|];split;[exact BZD|];split;[exact RatioBounds|];split;[exact Keep|];split.
   + eapply lframe_trans.
     * eapply lframe_implies;[exact FrameR|];intros b pos [NotA Outside] Valid;exact Outside.
     * eapply lframe_implies;[exact FrameTail|];intros b pos [NotA Outside] Valid;exact NotA.
   + eapply (secp_closed_function_preserved f_secp256k1_gej_double_var);[reflexivity|reflexivity|exact Call].
Qed.
