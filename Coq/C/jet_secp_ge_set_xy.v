(** The original affine coordinate constructor: flag store and two actual
    Clight struct assignments, with no external memcpy premise. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_exec C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv.
Require Import C.jet_secp_affine_fields C.jet_secp_curve_statements C.jet_secp_curve_frame.
Require Import C.jet_secp_field_copy_owned C.jet_secp_local_regions C.jet_secp_multiply_normalize_bridge.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition ge_set_xy_temps bd bp :=
  PTree.set _y (Vptr bp (Ptrofs.repr 40))
    (PTree.set _x (Vptr bp Ptrofs.zero)
      (PTree.set _r (Vptr bd Ptrofs.zero) (create_undef_temps (fn_temps f_secp256k1_ge_set_xy)))).
Definition ge_set_xy_field fid ty :=
  Efield (Ederef (Etempvar _r (tptr curve_ge_type)) curve_ge_type) fid ty.
Definition ge_set_xy_input pid := Ederef (Etempvar pid (tptr curve_fe_type)) curve_fe_type.
Lemma ge_set_xy_entry m bd bp :
  function_entry2 secp_ge f_secp256k1_ge_set_xy
    [Vptr bd Ptrofs.zero;Vptr bp Ptrofs.zero;Vptr bp (Ptrofs.repr 40)] m
    empty_env (ge_set_xy_temps bd bp) m.
Proof.
  assert (Ok : fn_okb f_secp256k1_ge_set_xy=true) by reflexivity.
  destruct (fn_okb_true _ Ok) as (HN1 & HN2 & HD).
  constructor;[exact HN1|exact HN2|exact HD|constructor|reflexivity].
Qed.
Lemma eval_ge_set_xy_field le m bd fid delta ty :
  In (fid,delta) [(_x,0);(_y,40);(_infinity,80)] ->
  le!_r=Some(Vptr bd Ptrofs.zero) ->
  eval_lvalue secp_ge empty_env le m (ge_set_xy_field fid ty) bd (Ptrofs.repr delta) Full.
Proof.
  intros InField Temp.
  exact (eval_affine_pointer_field le m bd 0 _r fid delta ty InField ltac:(lia)
    ltac:(change (88<=18446744073709551615);lia) Temp).
Qed.

Theorem eval_ge_set_xy_owned x y m bd bp : bd<>bp ->
  fe_at m bp 0 (words5 x) -> fe_at m bp 40 (words5 y) ->
  Mem.range_perm m bd 0 88 Cur Freeable -> exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ge_set_xy)
    [Vptr bd Ptrofs.zero;Vptr bp Ptrofs.zero;Vptr bp (Ptrofs.repr 40)] E0 mf Vundef /\
  fe_at mf bd 0 (words5 x) /\ fe_at mf bd 40 (words5 y) /\
  Mem.load Mint32 mf bd 80=Some(Vint Int.zero) /\ Mem.range_perm mf bd 0 88 Cur Freeable /\
  (forall b pos k p,Mem.perm mf b pos k p <-> Mem.perm m b pos k p) /\
  lframe (fun b _=>b<>bd) m mf.
Proof.
  intros Sep X Y Free.
  set (le:=ge_set_xy_temps bd bp).
  assert (R : le!_r=Some(Vptr bd Ptrofs.zero)) by reflexivity.
  assert (TX : le!_x=Some(Vptr bp Ptrofs.zero)) by reflexivity.
  assert (TY : le!_y=Some(Vptr bp (Ptrofs.repr 40))) by reflexivity.
  assert (Access : Mem.valid_access m Mint32 bd 80 Writable).
  { split.
    - intros pos HP;change (80<=pos<84) in HP.
      eapply Mem.perm_implies;[apply Free;lia|constructor].
    - exists 20;reflexivity. }
  destruct (Mem.valid_access_store m Mint32 bd 80 (Vint Int.zero) Access) as (m1 & Store).
  assert (F1 : Mem.range_perm m1 bd 0 88 Cur Freeable).
  { intros pos HP;eapply Mem.perm_store_1;[exact Store|apply Free;exact HP]. }
  assert (L1 : lframe (fun b pos=>b<>bd \/ pos<80 \/ 84<=pos) m m1).
  { apply lframe_unchanged;eapply Mem.store_unchanged_on;[exact Store|].
    intros pos HP;change (80<=pos<84) in HP;intros [NE|[Lo|Hi]];[contradiction|lia|lia]. }
  assert (X1 : fe_at m1 bp 0 (words5 x)).
  { eapply curve_keep_field_range;[reflexivity|exact X|exact L1|];intros;left;congruence. }
  assert (Y1 : fe_at m1 bp 40 (words5 y)).
  { eapply curve_keep_field_range;[reflexivity|exact Y|exact L1|];intros;left;congruence. }
  destruct (exec_field_copy_owned empty_env le m1 (ge_set_xy_input _x) (ge_set_xy_field _x curve_fe_type)
    bp 0 bd 0 x eq_refl eq_refl
    ltac:(eapply eval_Elvalue;[apply eval_Ederef;apply eval_Etempvar;exact TX|apply deref_loc_copy;reflexivity])
    ltac:(apply eval_ge_set_xy_field;[cbn [In];tauto|exact R])
    ltac:(congruence) X1 ltac:(lia) ltac:(exists 0;reflexivity)
    ltac:(change (40<=18446744073709551615);lia)
    ltac:(intros pos HP;apply F1;lia)) as (m2 & CopyX & XO & PermX & LX).
  assert (Y2 : fe_at m2 bp 40 (words5 y)).
  { eapply curve_keep_field_range;[reflexivity|exact Y1|exact LX|];intros;left;congruence. }
  assert (F2 : Mem.range_perm m2 bd 0 88 Cur Freeable).
  { intros pos HP;apply (proj2 (PermX bd pos Cur Freeable));apply F1;exact HP. }
  destruct (exec_field_copy_owned empty_env le m2 (ge_set_xy_input _y) (ge_set_xy_field _y curve_fe_type)
    bp 40 bd 40 y eq_refl eq_refl
    ltac:(eapply eval_Elvalue;[apply eval_Ederef;apply eval_Etempvar;exact TY|apply deref_loc_copy;reflexivity])
    ltac:(apply eval_ge_set_xy_field;[cbn [In];tauto|exact R])
    ltac:(congruence) Y2 ltac:(lia) ltac:(exists 5;reflexivity)
    ltac:(change (80<=18446744073709551615);lia)
    ltac:(intros pos HP;apply F2;lia)) as (mf & CopyY & YO & PermY & LY).
  assert (XF : fe_at mf bd 0 (words5 x)).
  { eapply curve_keep_field_range;[reflexivity|exact XO|exact LY|];intros pos HP;right;left;lia. }
  assert (FF : Mem.range_perm mf bd 0 88 Cur Freeable).
  { intros pos HP;apply (proj2 (PermY bd pos Cur Freeable));apply F2;exact HP. }
  assert (Valid1 : Mem.valid_block m1 bd) by (eapply Mem.perm_valid_block;apply (F1 0);lia).
  assert (Valid2 : Mem.valid_block m2 bd) by (eapply Mem.perm_valid_block;apply (F2 0);lia).
  assert (Flag : Mem.load Mint32 mf bd 80=Some(Vint Int.zero)).
  { rewrite (proj1 LY Mint32 bd 80 Valid2), (proj1 LX Mint32 bd 80 Valid1).
    - exact (Mem.load_store_same Mint32 m bd 80 (Vint Int.zero) m1 Store).
    - intros pos HP;change (80<=pos<84) in HP;right;right;lia.
    - intros pos HP;change (80<=pos<84) in HP;right;right;lia. }
  assert (Frame : lframe (fun b _=>b<>bd) m mf).
  { eapply lframe_trans.
    - eapply lframe_implies;[exact L1|];intros b pos Outside Valid;left;exact Outside.
    - eapply lframe_trans; eapply lframe_implies;[exact LX| |exact LY|];
        intros b pos Outside Valid;left;exact Outside. }
  assert (Body : Clight2.exec_stmt secp_ge empty_env le m (fn_body f_secp256k1_ge_set_xy) E0 le mf Out_normal).
  { eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m1) (le1:=le).
    - eapply exec_Sassign with (loc:=bd) (ofs:=Ptrofs.repr 80) (bf:=Full) (v2:=Vint Int.zero) (v:=Vint Int.zero).
      + apply eval_ge_set_xy_field;[cbn [In];tauto|exact R].
      + apply eval_Econst_int.
      + reflexivity.
      + eapply assign_loc_value with (chunk:=Mint32);[reflexivity|exact Store].
    - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m2) (le1:=le);[exact CopyX|exact CopyY]. }
  exists mf;split.
  - eapply eval_funcall_internal with (e:=empty_env) (le1:=le) (le2:=le) (m1:=m) (m2:=mf) (out:=Out_normal).
    + apply ge_set_xy_entry.
    + exact Body.
    + reflexivity.
    + reflexivity.
  - split;[exact XF|];split;[exact YO|];split;[exact Flag|];split;[exact FF|];split;[|exact Frame].
    intros b pos k p;rewrite (PermY b pos k p),(PermX b pos k p);split;intro HP;
      [eapply Mem.perm_store_2|eapply Mem.perm_store_1];eassumption.
Qed.
