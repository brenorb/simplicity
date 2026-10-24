(** The original affine constructor with independently stored X and Y,
    as used by SWU. Reuse the actual field-copy proof without repacking the
    caller's locals or introducing a libc premise. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_exec C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv
  C.jet_secp_curve_statements C.jet_secp_curve_frame C.jet_secp_ge_set_xy
  C.jet_secp_field_copy_owned C.jet_secp_multiply_normalize_bridge C.jet_secp_closed_helpers
  C.jet_clight_internal_frame C.jet_clight_internal_preserve.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition ge_set_xy_separate_temps bd bx by0 :=
  PTree.set _y (Vptr by0 Ptrofs.zero) (PTree.set _x (Vptr bx Ptrofs.zero)
    (PTree.set _r (Vptr bd Ptrofs.zero) (create_undef_temps (fn_temps f_secp256k1_ge_set_xy)))).
Lemma ge_set_xy_separate_entry m bd bx by0 :
  function_entry2 secp_ge f_secp256k1_ge_set_xy [Vptr bd Ptrofs.zero;Vptr bx Ptrofs.zero;Vptr by0 Ptrofs.zero]
    m empty_env (ge_set_xy_separate_temps bd bx by0) m.
Proof.
  assert (Ok:fn_okb f_secp256k1_ge_set_xy=true) by reflexivity.
  destruct (fn_okb_true _ Ok) as (HN1 & HN2 & HD).
  constructor;[exact HN1|exact HN2|exact HD|constructor|reflexivity].
Qed.
Theorem eval_ge_set_xy_separate x y m bd bx by0 : bd<>bx -> bd<>by0 ->
  fe_at m bx 0 (words5 x) -> fe_at m by0 0 (words5 y) ->
  Mem.range_perm m bd 0 88 Cur Freeable -> exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ge_set_xy)
    [Vptr bd Ptrofs.zero;Vptr bx Ptrofs.zero;Vptr by0 Ptrofs.zero] E0 mf Vundef /\
  fe_at mf bd 0 (words5 x) /\ fe_at mf bd 40 (words5 y) /\
  Mem.load Mint32 mf bd 80=Some (Vint Int.zero) /\ Mem.range_perm mf bd 0 88 Cur Freeable /\
  (forall b pos k p,Mem.perm mf b pos k p <-> Mem.perm m b pos k p) /\
  lframe (fun b _=>b<>bd) m mf /\ readonly_preserved m mf.
Proof.
  intros NeX NeY X Y Free;set (le:=ge_set_xy_separate_temps bd bx by0).
  assert (R:le!_r=Some (Vptr bd Ptrofs.zero)) by reflexivity.
  assert (TX:le!_x=Some (Vptr bx Ptrofs.zero)) by reflexivity.
  assert (TY:le!_y=Some (Vptr by0 Ptrofs.zero)) by reflexivity.
  assert (Access:Mem.valid_access m Mint32 bd 80 Writable).
  { split.
    - intros pos HP;change (80<=pos<84) in HP;eapply Mem.perm_implies;[apply Free;lia|constructor].
    - exists 20;reflexivity. }
  destruct (Mem.valid_access_store m Mint32 bd 80 (Vint Int.zero) Access) as (m1 & Store).
  assert (F1:Mem.range_perm m1 bd 0 88 Cur Freeable) by
    (intros pos HP;eapply Mem.perm_store_1;[exact Store|apply Free;exact HP]).
  assert (L1:lframe (fun b pos=>b<>bd \/ pos<80 \/ 84<=pos) m m1).
  { apply lframe_unchanged;eapply Mem.store_unchanged_on;[exact Store|].
    intros pos HP;change (80<=pos<84) in HP;intros [NE|[Lo|Hi]];[contradiction|lia|lia]. }
  assert (X1:fe_at m1 bx 0 (words5 x)) by
    (eapply curve_keep_field_range;[reflexivity|exact X|exact L1|];intros;left;congruence).
  assert (Y1:fe_at m1 by0 0 (words5 y)) by
    (eapply curve_keep_field_range;[reflexivity|exact Y|exact L1|];intros;left;congruence).
  destruct (exec_field_copy_owned empty_env le m1 (ge_set_xy_input _x) (ge_set_xy_field _x curve_fe_type)
    bx 0 bd 0 x eq_refl eq_refl
    ltac:(eapply eval_Elvalue;[apply eval_Ederef;apply eval_Etempvar;exact TX|apply deref_loc_copy;reflexivity])
    ltac:(apply eval_ge_set_xy_field;[left;reflexivity|exact R]) ltac:(congruence) X1
    ltac:(lia) ltac:(exists 0;reflexivity) ltac:(change (40<=18446744073709551615);lia)
    ltac:(intros pos HP;apply F1;lia)) as (m2 & CopyX & XO & PermX & LX).
  assert (Y2:fe_at m2 by0 0 (words5 y)) by
    (eapply curve_keep_field_range;[reflexivity|exact Y1|exact LX|];intros;left;congruence).
  assert (F2:Mem.range_perm m2 bd 0 88 Cur Freeable).
  { intros pos HP;apply (proj2 (PermX bd pos Cur Freeable));apply F1;exact HP. }
  destruct (exec_field_copy_owned empty_env le m2 (ge_set_xy_input _y) (ge_set_xy_field _y curve_fe_type)
    by0 0 bd 40 y eq_refl eq_refl
    ltac:(eapply eval_Elvalue;[apply eval_Ederef;apply eval_Etempvar;exact TY|apply deref_loc_copy;reflexivity])
    ltac:(apply eval_ge_set_xy_field;[right;left;reflexivity|exact R]) ltac:(congruence) Y2
    ltac:(lia) ltac:(exists 5;reflexivity) ltac:(change (80<=18446744073709551615);lia)
    ltac:(intros pos HP;apply F2;lia)) as (mf & CopyY & YO & PermY & LY).
  assert (XF:fe_at mf bd 0 (words5 x)) by
    (eapply curve_keep_field_range;[reflexivity|exact XO|exact LY|];intros pos HP;right;left;lia).
  assert (FF:Mem.range_perm mf bd 0 88 Cur Freeable).
  { intros pos HP;apply (proj2 (PermY bd pos Cur Freeable));apply F2;exact HP. }
  assert (Valid1:Mem.valid_block m1 bd) by (eapply Mem.perm_valid_block;apply (F1 0);lia).
  assert (Valid2:Mem.valid_block m2 bd) by (eapply Mem.perm_valid_block;apply (F2 0);lia).
  assert (Flag:Mem.load Mint32 mf bd 80=Some (Vint Int.zero)).
  { rewrite (proj1 LY Mint32 bd 80 Valid2),(proj1 LX Mint32 bd 80 Valid1).
    - exact (Mem.load_store_same Mint32 m bd 80 (Vint Int.zero) m1 Store).
    - intros pos HP;change (80<=pos<84) in HP;right;right;lia.
    - intros pos HP;change (80<=pos<84) in HP;right;right;lia. }
  assert (Frame:lframe (fun b _=>b<>bd) m mf).
  { eapply lframe_trans.
    - eapply lframe_implies;[exact L1|];intros b pos Outside Valid;left;exact Outside.
    - eapply lframe_trans;eapply lframe_implies;[exact LX| |exact LY|];
        intros b pos Outside Valid;left;exact Outside. }
  assert (Body:Clight2.exec_stmt secp_ge empty_env le m (fn_body f_secp256k1_ge_set_xy) E0 le mf Out_normal).
  { eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m1) (le1:=le).
    - eapply exec_Sassign with (loc:=bd) (ofs:=Ptrofs.repr 80) (bf:=Full) (v2:=Vint Int.zero) (v:=Vint Int.zero).
      + apply eval_ge_set_xy_field;[right;right;left;reflexivity|exact R].
      + apply eval_Econst_int.
      + reflexivity.
      + eapply assign_loc_value with (chunk:=Mint32);[reflexivity|exact Store].
    - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m2) (le1:=le);[exact CopyX|exact CopyY]. }
  assert (Call:Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ge_set_xy)
    [Vptr bd Ptrofs.zero;Vptr bx Ptrofs.zero;Vptr by0 Ptrofs.zero] E0 mf Vundef).
  { eapply eval_funcall_internal with (e:=empty_env) (le1:=le) (le2:=le) (m1:=m) (m2:=mf) (out:=Out_normal).
    - apply ge_set_xy_separate_entry.
    - exact Body.
    - reflexivity.
    - reflexivity. }
  exists mf;split;[exact Call|];split;[exact XF|];split;[exact YO|];split;[exact Flag|];
    split;[exact FF|];split.
  - intros b pos k p;rewrite (PermY b pos k p),(PermX b pos k p);split;intro HP;
      [eapply Mem.perm_store_2|eapply Mem.perm_store_1];eassumption.
  - split;[exact Frame|];eapply (secp_closed_function_preserved f_secp256k1_ge_set_xy);
      [reflexivity|reflexivity|exact Call].
Qed.
