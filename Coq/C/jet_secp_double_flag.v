(** Actual in-place flag copy at the start of gej_double, with storage and
    field preservation derived from the real Mint32 store. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_fe_nv C.jet_secp_linkage C.jets_secp
  C.jet_secp_double_statements C.jet_secp_gej_infinity_layout C.jet_secp_curve_frame
  C.jet_secp_local_regions C.jet_secp_multiply_normalize_bridge.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Lemma eval_double_flag_field e le m ba p : le!p=Some (Vptr ba Ptrofs.zero) ->
  eval_lvalue secp_ge e le m (double_point_field p _infinity tint) ba (Ptrofs.repr 120) Full.
Proof.
  intro HP.
  destruct (gej_infinity_field_layout _infinity 120 ltac:(cbn [In];tauto)) as (co & HC & HO).
  unfold double_point_field;rewrite <- (Ptrofs.add_zero_l (Ptrofs.repr 120)).
  eapply eval_Efield_struct with (co:=co) (delta:=120).
  - eapply eval_Elvalue.
    + apply eval_Ederef;apply eval_Etempvar;exact HP.
    + apply deref_loc_copy;reflexivity.
  - reflexivity.
  - exact HC.
  - exact HO.
Qed.

Lemma exec_double_flag_copy e le m mi ba flag :
  le!_a=Some (Vptr ba Ptrofs.zero) -> le!_r=Some (Vptr ba Ptrofs.zero) ->
  Mem.load Mint32 m ba 120=Some (Vint flag) ->
  Mem.store Mint32 m ba 120 (Vint flag)=Some mi ->
  Clight2.exec_stmt secp_ge e le m double_flag_stmt E0
    (PTree.set _t'1 (Vint flag) le) mi Out_normal.
Proof.
  intros HA HR HLoad HStore;unfold double_flag_stmt.
  eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m)
    (le1:=PTree.set _t'1 (Vint flag) le).
  - apply exec_Sset;eapply eval_Elvalue.
    + apply eval_double_flag_field;exact HA.
    + eapply deref_loc_value with (chunk:=Mint32);[reflexivity|].
      change (Mem.load Mint32 m ba 120=Some (Vint flag));exact HLoad.
  - eapply exec_Sassign with (loc:=ba) (ofs:=Ptrofs.repr 120) (bf:=Full)
      (v2:=Vint flag) (v:=Vint flag).
    + apply eval_double_flag_field;rewrite PTree.gso by discriminate;exact HR.
    + apply eval_Etempvar;apply PTree.gss.
    + reflexivity.
    + eapply assign_loc_value with (chunk:=Mint32);[reflexivity|].
      change (Mem.store Mint32 m ba 120 (Vint flag)=Some mi);exact HStore.
Qed.

Theorem double_flag_copy_owned e le x y z m ba flag :
  le!_a=Some (Vptr ba Ptrofs.zero) -> le!_r=Some (Vptr ba Ptrofs.zero) ->
  Mem.load Mint32 m ba 120=Some (Vint flag) ->
  fe_at m ba 0 (words5 x) -> fe_at m ba 40 (words5 y) -> fe_at m ba 80 (words5 z) ->
  Mem.range_perm m ba 0 128 Cur Freeable ->
  exists mi,
  Clight2.exec_stmt secp_ge e le m double_flag_stmt E0
    (PTree.set _t'1 (Vint flag) le) mi Out_normal /\
  fe_at mi ba 0 (words5 x) /\ fe_at mi ba 40 (words5 y) /\ fe_at mi ba 80 (words5 z) /\
  Mem.range_perm mi ba 0 128 Cur Freeable /\
  lframe (fun b pos => b<>ba \/ pos<120 \/ 124<=pos) m mi.
Proof.
  intros HA HR HLoad HX HY HZ HF.
  assert (HW : Mem.range_perm m ba 0 128 Cur Writable) by (apply freeable_range_writable;exact HF).
  assert (HV : Mem.valid_access m Mint32 ba 120 Writable).
  { split.
    - intros pos HP;apply HW;change (120<=pos<124) in HP;lia.
    - exists 30;reflexivity. }
  destruct (Mem.valid_access_store m Mint32 ba 120 (Vint flag) HV) as (mi & HStore).
  assert (HL : lframe (fun b pos => b<>ba \/ pos<120 \/ 124<=pos) m mi).
  { apply lframe_unchanged;eapply Mem.store_unchanged_on;[exact HStore|].
    intros pos HP;change (120<=pos<124) in HP;intros [HE|[HE|HE]];[contradiction|lia|lia]. }
  exists mi;split;[exact (exec_double_flag_copy e le m mi ba flag HA HR HLoad HStore)|].
  split.
  - eapply curve_keep_field_range;[reflexivity|exact HX|exact HL|].
    intros pos HP;right;left;lia.
  - split.
    + eapply curve_keep_field_range;[reflexivity|exact HY|exact HL|].
      intros pos HP;right;left;lia.
    + split.
      * eapply curve_keep_field_range;[reflexivity|exact HZ|exact HL|].
        intros pos HP;right;left;lia.
      * split;[|exact HL]. intros pos HP;eapply Mem.perm_store_1;[exact HStore|apply HF;exact HP].
Qed.
