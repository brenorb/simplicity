(** Original affine-to-projective conversion on distinct owned allocations.
    This is the actual initializer called by mixed addition when A is infinity. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_exec C.jet_sx_exec C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fns
  C.jet_secp_fe_nv C.jet_secp_local_regions C.jet_secp_curve_frame C.jet_secp_field_read_preservation
  C.jet_secp_multiply_normalize_bridge C.jet_secp_curve_statements C.jet_secp_double_statements
  C.jet_secp_double_flag C.jet_secp_gej_infinity_layout C.jet_secp_field_copy_owned C.jet_secp_point_set_bit C.jet_secp_point_write_run.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition set_ge_flag_stmt := match fn_body f_secp256k1_gej_set_ge with | Ssequence h _ => h | _ => Sskip end.
Definition set_ge_copy_stmt fid := Sassign (double_point_field _r fid curve_fe_type) (curve_affine_field fid curve_fe_type).
Definition set_ge_tail_stmt := Ssequence (Sset _t'1 (double_point_field _r _infinity tint))
  (curve_call _secp256k1_fe_set_int f_secp256k1_fe_set_int None
    [double_point_address _r _z;Eunop Cop.Onotbool (Etempvar _t'1 tint) tint]).
Lemma set_ge_source : fn_body f_secp256k1_gej_set_ge=Ssequence set_ge_flag_stmt
  (Ssequence (set_ge_copy_stmt _x) (Ssequence (set_ge_copy_stmt _y) set_ge_tail_stmt)).
Proof. reflexivity. Qed.
Lemma eval_set_ge_point_field le m br fid delta : In (fid,delta) [(_x,0);(_y,40);(_z,80)] ->
  le!_r=Some (Vptr br Ptrofs.zero) ->
  eval_lvalue secp_ge empty_env le m (double_point_field _r fid curve_fe_type) br (Ptrofs.repr delta) Full.
Proof.
  intros HH HR.
  assert (HF : In (fid,delta) [(_x,0);(_y,40);(_z,80);(_infinity,120)]).
  { destruct HH as [HH|[HH|[HH|HH]]];[left|right;left|right;right;left|contradiction];exact HH. }
  destruct (gej_infinity_field_layout fid delta HF) as (co & HC & HO).
  unfold double_point_field;rewrite <- (Ptrofs.add_zero_l (Ptrofs.repr delta)).
  eapply eval_Efield_struct with (co:=co) (delta:=delta).
  - eapply eval_Elvalue;[apply eval_Ederef;apply eval_Etempvar;exact HR|apply deref_loc_copy;reflexivity].
  - reflexivity.
  - exact HC.
  - exact HO.
Qed.
Lemma exec_set_ge_flag le m mi ba br flag :
  le!_a=Some (Vptr ba Ptrofs.zero) -> le!_r=Some (Vptr br Ptrofs.zero) ->
  Mem.load Mint32 m ba 80=Some (Vint flag) -> Mem.store Mint32 m br 120 (Vint flag)=Some mi ->
  Clight2.exec_stmt secp_ge empty_env le m set_ge_flag_stmt E0 (PTree.set _t'2 (Vint flag) le) mi Out_normal.
Proof.
  intros HA HR HL HS;unfold set_ge_flag_stmt.
  eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=PTree.set _t'2 (Vint flag) le).
  - apply exec_Sset;eapply eval_Elvalue.
    + apply eval_curve_field;[cbn [In];tauto|exact HA].
    + eapply deref_loc_value with (chunk:=Mint32);[reflexivity|].
      change (Mem.load Mint32 m ba 80=Some (Vint flag));exact HL.
  - eapply exec_Sassign with (loc:=br) (ofs:=Ptrofs.repr 120) (bf:=Full) (v2:=Vint flag) (v:=Vint flag).
    + apply eval_double_flag_field;rewrite PTree.gso by discriminate;exact HR.
    + apply eval_Etempvar;apply PTree.gss.
    + reflexivity.
    + eapply assign_loc_value with (chunk:=Mint32);[reflexivity|].
      change (Mem.store Mint32 m br 120 (Vint flag)=Some mi);exact HS.
Qed.
Lemma exec_set_ge_tail le m mf br flag :
  le!_r=Some (Vptr br Ptrofs.zero) -> Mem.load Mint32 m br 120=Some (Vint flag) ->
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_set_int)
    [Vptr br (Ptrofs.repr 80);Vint (if Int.eq flag Int.zero then Int.one else Int.zero)] E0 mf Vundef ->
  Clight2.exec_stmt secp_ge empty_env le m set_ge_tail_stmt E0 (PTree.set _t'1 (Vint flag) le) mf Out_normal.
Proof.
  intros HR HL HC;unfold set_ge_tail_stmt.
  eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=PTree.set _t'1 (Vint flag) le).
  - apply exec_Sset;eapply eval_Elvalue.
    + apply eval_double_flag_field;exact HR.
    + eapply deref_loc_value with (chunk:=Mint32);[reflexivity|].
      change (Mem.load Mint32 m br 120=Some (Vint flag));exact HL.
  - eapply exec_curve_call with (vargs:=[Vptr br (Ptrofs.repr 80);Vint (if Int.eq flag Int.zero then Int.one else Int.zero)]) (v:=Vundef).
    + unfold secp_pure;repeat (first [left;reflexivity|right]).
    + reflexivity.
    + eapply eval_Econs.
      * apply eval_double_point_address;[cbn [In];tauto|rewrite PTree.gso by discriminate;exact HR].
      * reflexivity.
      * eapply eval_Econs.
        -- eapply eval_Eunop with (v1:=Vint flag)
             (v:=Vint (if Int.eq flag Int.zero then Int.one else Int.zero)).
           ++ apply eval_Etempvar;apply PTree.gss.
           ++ change (option_map (fun b => Val.of_bool (negb b))
                (Some (negb (Int.eq flag Int.zero))) =
                Some (Vint (if Int.eq flag Int.zero then Int.one else Int.zero))).
              destruct (Int.eq flag Int.zero);reflexivity.
        -- reflexivity.
        -- constructor.
    + exact HC.
Qed.

Definition set_ge_entry_temps br ba := PTree.set _a (Vptr ba Ptrofs.zero)
  (PTree.set _r (Vptr br Ptrofs.zero) (create_undef_temps (fn_temps f_secp256k1_gej_set_ge))).
Lemma set_ge_ok : fn_okb f_secp256k1_gej_set_ge=true.
Proof. reflexivity. Qed.
Lemma set_ge_entry m br ba : function_entry2 secp_ge f_secp256k1_gej_set_ge
  [Vptr br Ptrofs.zero;Vptr ba Ptrofs.zero] m empty_env (set_ge_entry_temps br ba) m.
Proof.
  destruct (fn_okb_true _ set_ge_ok) as (HN1 & HN2 & HD).
  constructor;[exact HN1|exact HN2|exact HD|constructor|reflexivity].
Qed.

Theorem eval_gej_set_ge_owned m br ba x y flag :
  br<>ba -> Mem.range_perm m br 0 128 Cur Freeable ->
  fe_at m ba 0 (words5 x) -> fe_at m ba 40 (words5 y) -> Mem.load Mint32 m ba 80=Some (Vint flag) ->
  exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_gej_set_ge)
    [Vptr br Ptrofs.zero;Vptr ba Ptrofs.zero] E0 mf Vundef /\
  fe_at mf br 0 (words5 x) /\ fe_at mf br 40 (words5 y) /\
  fe_at mf br 80 (words5 (point_set_bit_words (Int.eq flag Int.zero))) /\
  Mem.load Mint32 mf br 120=Some (Vint flag) /\ Mem.range_perm mf br 0 128 Cur Freeable /\
  lframe (fun b _ => b<>br) m mf.
Proof.
  intros HSep HF HX HY HFlag.
  assert (HW : Mem.valid_access m Mint32 br 120 Writable).
  { split.
    - intros pos HP;eapply Mem.perm_implies;[apply HF;change (120<=pos<124) in HP;lia|constructor].
    - exists 30;reflexivity. }
  destruct (Mem.valid_access_store m Mint32 br 120 (Vint flag) HW) as (mi & HS).
  assert (HIFrame : lframe (fun b _ => b<>br) m mi).
  { apply lframe_unchanged;eapply Mem.store_unchanged_on;[exact HS|];intros pos HP HO;contradiction. }
  assert (HFi : Mem.range_perm mi br 0 128 Cur Freeable).
  { intros pos HP;eapply Mem.perm_store_1;[exact HS|apply HF;exact HP]. }
  pose proof (field_at_lframe m mi ba 0 _ _ HX HIFrame ltac:(intros;congruence)) as HXi.
  pose proof (field_at_lframe m mi ba 40 _ _ HY HIFrame ltac:(intros;congruence)) as HYi.
  set (le:=set_ge_entry_temps br ba).
  set (li:=PTree.set _t'2 (Vint flag) le).
  assert (HA : li!_a=Some (Vptr ba Ptrofs.zero)) by reflexivity.
  assert (HR : li!_r=Some (Vptr br Ptrofs.zero)) by reflexivity.
  destruct (exec_field_copy_owned empty_env li mi (curve_affine_field _x curve_fe_type)
    (double_point_field _r _x curve_fe_type) ba 0 br 0 x eq_refl eq_refl
    ltac:(eapply eval_Elvalue;[apply eval_curve_field;[cbn [In];tauto|exact HA]|apply deref_loc_copy;reflexivity])
    (eval_set_ge_point_field li mi br _x 0 ltac:(cbn [In];tauto) HR)
    (not_eq_sym HSep) HXi ltac:(lia) ltac:(exists 0;reflexivity)
    ltac:(change (40<=18446744073709551615);lia) ltac:(intros pos HP;apply HFi;lia))
    as (mx & CX & XX & PX & FX).
  assert (HYx : fe_at mx ba 40 (words5 y)).
  { eapply curve_keep_field_range;[reflexivity|exact HYi|exact FX|];intros;left;congruence. }
  destruct (exec_field_copy_owned empty_env li mx (curve_affine_field _y curve_fe_type)
    (double_point_field _r _y curve_fe_type) ba 40 br 40 y eq_refl eq_refl
    ltac:(eapply eval_Elvalue;[apply eval_curve_field;[cbn [In];tauto|exact HA]|apply deref_loc_copy;reflexivity])
    (eval_set_ge_point_field li mx br _y 40 ltac:(cbn [In];tauto) HR)
    (not_eq_sym HSep) HYx ltac:(lia) ltac:(exists 5;reflexivity)
    ltac:(change (80<=18446744073709551615);lia)
    ltac:(intros pos HP;apply (proj2 (PX br pos Cur Freeable));apply HFi;lia))
    as (my & CY & YY & PY & FY).
  assert (HFy : Mem.range_perm my br 0 128 Cur Freeable).
  { intros pos HP;apply (proj2 (PY br pos Cur Freeable));apply (proj2 (PX br pos Cur Freeable));apply HFi;exact HP. }
  assert (HFlagy : Mem.load Mint32 my br 120=Some (Vint flag)).
  { rewrite (proj1 FY Mint32 br 120), (proj1 FX Mint32 br 120).
    - exact (Mem.load_store_same _ _ _ _ _ _ HS).
    - eapply Mem.perm_valid_block;apply (HFi 0);lia.
    - intros pos HP;right;right;change (120<=pos<124) in HP;lia.
    - eapply Mem.perm_valid_block;apply (proj2 (PX br 0 Cur Freeable));apply (HFi 0);lia.
    - intros pos HP;right;right;change (120<=pos<124) in HP;lia. }
  destruct (eval_point_set_bit PointZ (Int.eq flag Int.zero) my br HFy)
    as (mf & CZ & ZZ & FF & FZ).
  assert (XY : fe_at my br 0 (words5 x)).
  { eapply curve_keep_field_range;[reflexivity|exact XX|exact FY|];intros pos HP;right;left;lia. }
  assert (XF : fe_at mf br 0 (words5 x)).
  { eapply curve_keep_field_range;[reflexivity|exact XY|exact FZ|];intros pos HP;right;left;change (pos<80);lia. }
  assert (YF : fe_at mf br 40 (words5 y)).
  { eapply curve_keep_field_range;[reflexivity|exact YY|exact FZ|];intros pos HP;right;left;change (pos<80);lia. }
  exists mf;split.
  - eapply eval_funcall_internal with (e:=empty_env) (le1:=le) (le2:=PTree.set _t'1 (Vint flag) li)
      (m1:=m) (m2:=mf) (out:=Out_normal).
    + exact (set_ge_entry m br ba).
    + rewrite set_ge_source.
      eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mi) (le1:=li).
      * eapply exec_set_ge_flag with (ba:=ba) (br:=br);[reflexivity|reflexivity|exact HFlag|exact HS].
      * eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mx) (le1:=li);[exact CX|].
        eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=my) (le1:=li);[exact CY|].
        apply exec_set_ge_tail with (br:=br);assumption.
    + reflexivity.
    + reflexivity.
  - split;[exact XF|];split;[exact YF|];split;[exact ZZ|];split.
    + rewrite (proj1 FZ Mint32 br 120);[exact HFlagy|eapply Mem.perm_valid_block;apply (HFy 0);lia|].
      intros pos HP;right;right;change (120<=pos<124) in HP;change (120<=pos);lia.
    + split;[exact FF|].
      eapply lframe_trans;[exact HIFrame|].
      eapply lframe_trans.
      * eapply lframe_implies;[exact FX|];intros b pos HO HV;left;exact HO.
      * eapply lframe_trans.
        -- eapply lframe_implies;[exact FY|];intros b pos HO HV;left;exact HO.
        -- eapply lframe_implies;[exact FZ|];intros b pos HO HV;left;exact HO.
Qed.
