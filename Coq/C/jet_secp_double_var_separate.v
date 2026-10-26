(** Actual finite-input NULL-ratio double_var used by odd-multiple tables.
    The point may be off-curve or have zero Y; finite means the C infinity
    flag is zero. Entry, flag dispatch, double, zero test, store and return
    are all derived from the original generated function. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_exec C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv
 C.jet_secp_double_separate_function C.jet_secp_double_var_statements C.jet_secp_double_var_owned
 C.jet_secp_double_all_calls C.jet_secp_double_statements C.jet_secp_double_flag
 C.jet_secp_curve_statements C.jet_secp_curve_frame C.jet_secp_field_read_preservation
 C.jet_secp_point_normalizes_zero C.jet_secp_point_write_run C.jet_secp_square_columns
 C.jet_secp_multiply_normalize_bridge C.jet_secp_closed_helpers C.jet_clight_internal_preserve.
Import ListNotations Values Ctypes.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition double_var_separate_temps br ba := PTree.set _rzr (Vlong Int64.zero)
 (PTree.set _a (Vptr ba Ptrofs.zero) (PTree.set _r (Vptr br Ptrofs.zero)
  (create_undef_temps (fn_temps f_secp256k1_gej_double_var)))).

Lemma exec_double_var_post_ratio_separate e le m md mz mf br ba flag :
 le!_a=Some (Vptr ba Ptrofs.zero) -> le!_r=Some (Vptr br Ptrofs.zero) ->
 e!_secp256k1_gej_double=None -> e!_secp256k1_fe_normalizes_to_zero_var=None ->
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_gej_double)
  [Vptr br Ptrofs.zero;Vptr ba Ptrofs.zero] E0 md Vundef ->
 Clight2.eval_funcall secp_ge md (Internal f_secp256k1_fe_normalizes_to_zero_var)
  [Vptr br (Ptrofs.repr 80)] E0 mz (Vint flag) ->
 Mem.store Mint32 mz br 120 (Vint flag)=Some mf ->
 Clight2.exec_stmt secp_ge e le m double_var_post_ratio E0
  (PTree.set _t'1 (Vint flag) le) mf Out_normal.
Proof.
 intros HA HR HD HZ CD CZ Store;unfold double_var_post_ratio,double_var_tail.
 eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=md) (le1:=le).
 - change (Clight2.exec_stmt secp_ge e le m
    (curve_call _secp256k1_gej_double f_secp256k1_gej_double None
     [Etempvar _r (tptr (Tstruct __6123 noattr));Etempvar _a (tptr (Tstruct __6123 noattr))]) E0 le md Out_normal).
   eapply exec_curve_call with (vargs:=[Vptr br Ptrofs.zero;Vptr ba Ptrofs.zero]) (v:=Vundef).
   + unfold C.jet_secp_fns.secp_pure;repeat (first [left;reflexivity|right]).
   + exact HD.
   + eapply eval_Econs;[apply eval_Etempvar;exact HR|reflexivity|].
     eapply eval_Econs;[apply eval_Etempvar;exact HA|reflexivity|constructor].
   + exact CD.
 - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mz) (le1:=PTree.set _t'1 (Vint flag) le).
   + change (Clight2.exec_stmt secp_ge e le md
      (curve_call _secp256k1_fe_normalizes_to_zero_var f_secp256k1_fe_normalizes_to_zero_var (Some _t'1)
       [double_point_address _r _z]) E0 (PTree.set _t'1 (Vint flag) le) mz Out_normal).
     eapply exec_curve_call with (vargs:=[Vptr br (Ptrofs.repr 80)]) (v:=Vint flag).
     * unfold C.jet_secp_fns.secp_pure;repeat (first [left;reflexivity|right]).
     * exact HZ.
     * eapply eval_Econs;[apply eval_double_point_address;[cbn [In];tauto|exact HR]|reflexivity|constructor].
     * exact CZ.
   + eapply exec_Sassign with (loc:=br) (ofs:=Ptrofs.repr 120) (bf:=Full) (v2:=Vint flag) (v:=Vint flag).
     * apply eval_double_flag_field;rewrite PTree.gso by discriminate;exact HR.
     * apply eval_Etempvar;apply PTree.gss.
     * reflexivity.
     * eapply assign_loc_value with (chunk:=Mint32);[reflexivity|exact Store].
Qed.

Theorem eval_double_var_separate_finite x y z m br ba :
 square_input_bounds x -> square_input_bounds y -> square_input_bounds z -> br<>ba ->
 Mem.load Mint32 m ba 120=Some (Vint Int.zero) ->
 fe_at m ba 0 (words5 x) -> fe_at m ba 40 (words5 y) -> fe_at m ba 80 (words5 z) ->
 Mem.range_perm m br 0 128 Cur Freeable -> Mem.range_perm m ba 0 128 Cur Freeable -> exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_gej_double_var)
  [Vptr br Ptrofs.zero;Vptr ba Ptrofs.zero;Vlong Int64.zero] E0 mf Vundef /\
 fe_at mf br 0 (words5 (double_output_x_words x y)) /\
 fe_at mf br 40 (words5 (double_output_y_words x y)) /\
 fe_at mf br 80 (words5 (double_output_z_words y z)) /\
 Mem.load Mint32 mf br 120=Some (Vint (double_var_zflag y z)) /\
 Mem.load Mint32 mf ba 120=Some (Vint Int.zero) /\
 fe_at mf ba 0 (words5 x) /\ fe_at mf ba 40 (words5 y) /\ fe_at mf ba 80 (words5 z) /\
 Mem.range_perm mf br 0 128 Cur Freeable /\ Mem.range_perm mf ba 0 128 Cur Freeable /\
 square_input_bounds (double_output_x_words x y) /\
 square_input_bounds (double_output_y_words x y) /\
 square_input_bounds (double_output_z_words y z) /\
 lframe (fun b pos=>(b<>br \/ pos<0 \/ 124<=pos) /\ (b<>ba \/ pos<0 \/ 120<=pos)) m mf /\
 readonly_preserved m mf.
Proof.
 intros BX BY BZ RA Flag X Y ZAt RF AF.
 destruct (eval_double_separate_function x y z m br ba Int.zero BX BY BZ RA Flag X Y ZAt RF AF)
  as (md & CD & RXD & RYD & RZD & RFlagD & AFlagD & AXD & AYD & AZD &
      RFD & AFD & BXD & BYD & BZD & FD & ReadonlyD).
 destruct (eval_point_normalizes_zero PointZ (double_output_z_words y z) md br BZD RZD RFD)
  as (mz & CZ & RZZ & RFZ & FZ).
 assert (RXZ:fe_at mz br 0 (words5 (double_output_x_words x y))).
 { eapply curve_keep_field_range;[reflexivity|exact RXD|exact FZ|];intros pos Range;right;left;change (pos<80);lia. }
 assert (RYZ:fe_at mz br 40 (words5 (double_output_y_words x y))).
 { eapply curve_keep_field_range;[reflexivity|exact RYD|exact FZ|];intros pos Range;right;left;change (pos<80);lia. }
 assert (AXZ:fe_at mz ba 0 (words5 x)) by (eapply field_at_lframe;[exact AXD|exact FZ|];intros;left;congruence).
 assert (AYZ:fe_at mz ba 40 (words5 y)) by (eapply field_at_lframe;[exact AYD|exact FZ|];intros;left;congruence).
 assert (AZZ:fe_at mz ba 80 (words5 z)) by (eapply field_at_lframe;[exact AZD|exact FZ|];intros;left;congruence).
 assert (AFZ:Mem.range_perm mz ba 0 128 Cur Freeable) by
  (eapply curve_keep_free;[lia|exact AFD|exact FZ|];intros;left;congruence).
 assert (AVD:Mem.valid_block md ba) by (eapply Mem.perm_valid_block;exact (AFD 0 ltac:(lia))).
 assert (AFlagZ:Mem.load Mint32 mz ba 120=Some (Vint Int.zero)) by
  (rewrite (proj1 FZ Mint32 ba 120 AVD ltac:(intros;left;congruence));exact AFlagD).
 destruct (double_var_store_flag (double_output_x_words x y) (double_output_y_words x y)
   (double_output_z_words y z) mz br (double_var_zflag y z) RXZ RYZ RZZ RFZ)
  as (mf & Store & RFlagF & RXF & RYF & RZF & RFF & FS).
 assert (AXF:fe_at mf ba 0 (words5 x)) by (eapply field_at_lframe;[exact AXZ|exact FS|];intros;left;congruence).
 assert (AYF:fe_at mf ba 40 (words5 y)) by (eapply field_at_lframe;[exact AYZ|exact FS|];intros;left;congruence).
 assert (AZF:fe_at mf ba 80 (words5 z)) by (eapply field_at_lframe;[exact AZZ|exact FS|];intros;left;congruence).
 assert (AFF:Mem.range_perm mf ba 0 128 Cur Freeable) by
  (eapply curve_keep_free;[lia|exact AFZ|exact FS|];intros;left;congruence).
 assert (AVZ:Mem.valid_block mz ba) by (eapply Mem.perm_valid_block;exact (AFZ 0 ltac:(lia))).
 assert (AFlagF:Mem.load Mint32 mf ba 120=Some (Vint Int.zero)) by
  (rewrite (proj1 FS Mint32 ba 120 AVZ ltac:(intros;left;congruence));exact AFlagZ).
 set (le:=double_var_separate_temps br ba).
 set (lh:=PTree.set _t'2 (Vint Int.zero) le).
 assert (HA:lh!_a=Some (Vptr ba Ptrofs.zero)) by reflexivity.
 assert (HR:lh!_r=Some (Vptr br Ptrofs.zero)) by reflexivity.
 assert (HN:lh!_rzr=Some (Vlong Int64.zero)) by reflexivity.
 assert (Call:Clight2.eval_funcall secp_ge m (Internal f_secp256k1_gej_double_var)
   [Vptr br Ptrofs.zero;Vptr ba Ptrofs.zero;Vlong Int64.zero] E0 mf Vundef).
 { eapply eval_funcall_internal with (e:=empty_env) (le1:=le)
     (le2:=PTree.set _t'1 (Vint (double_var_zflag y z)) lh) (m1:=m) (m2:=mf) (out:=Out_normal).
   - destruct (fn_okb_true _ double_var_function_ok) as (Vars & Params & Disjoint).
     constructor;[exact Vars|exact Params|exact Disjoint|constructor|reflexivity].
   - rewrite double_var_source;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=lh).
     + apply exec_double_var_head_finite with (ba:=ba);[reflexivity|exact Flag].
     + change (Clight2.exec_stmt secp_ge empty_env lh m
        (Ssequence double_var_ratio_guard double_var_post_ratio) E0
        (PTree.set _t'1 (Vint (double_var_zflag y z)) lh) mf Out_normal).
       eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=lh).
       * unfold double_var_ratio_guard,double_var_tail.
         eapply exec_Sifthenelse with (v1:=Vint Int.zero) (b:=false);
          [apply eval_double_var_null_test;exact HN|reflexivity|constructor].
       * eapply exec_double_var_post_ratio_separate;
          [exact HA|exact HR|reflexivity|reflexivity|exact CD|exact CZ|exact Store].
   - reflexivity.
   - reflexivity. }
 exists mf;split;[exact Call|];split;[exact RXF|];split;[exact RYF|];split;[exact RZF|];
  split;[exact RFlagF|];split;[exact AFlagF|];split;[exact AXF|];split;[exact AYF|];
  split;[exact AZF|];split;[exact RFF|];split;[exact AFF|];split;[exact BXD|];
  split;[exact BYD|];split;[exact BZD|];split.
 - eapply lframe_trans;[exact FD|];eapply lframe_trans.
   + eapply lframe_implies;[exact FZ|].
     intros b pos [NR NA] Valid;destruct NR as [NR|[NR|NR]];
      [left;exact NR|right;left;change (pos<80);lia|right;right;change (120<=pos);lia].
   + eapply lframe_implies;[exact FS|].
     intros b pos [NR NA] Valid;destruct NR as [NR|[NR|NR]];intuition lia.
 - eapply (secp_closed_function_preserved f_secp256k1_gej_double_var);
    [reflexivity|reflexivity|exact Call].
Qed.
