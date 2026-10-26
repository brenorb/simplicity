(** Original affine infinity setter: actual flag store and both previously
    checked fe_clear calls, from ownership alone. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_exec C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fns
  C.jet_secp_fe_nv C.jet_secp_fe_clear_memory C.jet_secp_affine_fields
  C.jet_secp_curve_statements C.jet_secp_local_regions C.jet_secp_closed_helpers
  C.jet_clight_internal_preserve.
Import ListNotations Ctypes Values Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition affine_infinity_store := match fn_body f_secp256k1_ge_set_infinity with
  | Ssequence flag _=>flag | _=>Sskip end.
Definition affine_infinity_clear (second:bool) := curve_call _secp256k1_fe_clear f_secp256k1_fe_clear None
  [Eaddrof (Efield (Ederef (Etempvar _r (tptr (Tstruct __6121 noattr)))
    (Tstruct __6121 noattr)) (if second then _y else _x) (Tstruct __5467 noattr))
    (tptr (Tstruct __5467 noattr))].
Lemma affine_infinity_setter_source : fn_body f_secp256k1_ge_set_infinity=
  Ssequence affine_infinity_store (Ssequence (affine_infinity_clear false) (affine_infinity_clear true)).
Proof. reflexivity. Qed.

Lemma exec_affine_infinity_flag le m mf b : le!_r=Some (Vptr b Ptrofs.zero) ->
  Mem.store Mint32 m b 80 (Vint Int.one)=Some mf ->
  Clight2.exec_stmt secp_ge empty_env le m affine_infinity_store E0 le mf Out_normal.
Proof.
  intros R Store;unfold affine_infinity_store;cbn [fn_body].
  eapply exec_Sassign with (loc:=b) (ofs:=Ptrofs.repr 80) (bf:=Full)
    (v2:=Vint Int.one) (v:=Vint Int.one).
  - exact (eval_affine_pointer_field le m b 0 _r _infinity 80 tint
      ltac:(cbn;tauto) ltac:(lia) ltac:(change (88<=18446744073709551615);lia) R).
  - constructor.
  - reflexivity.
  - eapply assign_loc_value with (chunk:=Mint32);[reflexivity|exact Store].
Qed.
Lemma exec_affine_infinity_clear le m mf b (second:bool) : le!_r=Some (Vptr b Ptrofs.zero) ->
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_clear)
    [Vptr b (Ptrofs.repr (if second then 40 else 0))] E0 mf Vundef ->
  Clight2.exec_stmt secp_ge empty_env le m (affine_infinity_clear second) E0 le mf Out_normal.
Proof.
  intros R Call;unfold affine_infinity_clear;eapply exec_curve_call with
    (vargs:=[Vptr b (Ptrofs.repr (if second then 40 else 0))]) (v:=Vundef).
  - unfold secp_pure;repeat (first [left;reflexivity|right]).
  - reflexivity.
  - eapply eval_Econs.
    + apply (eval_affine_field_address le m b 0 _r (if second then _y else _x) (if second then 40 else 0));
        [destruct second;cbn;tauto|lia|change (88<=18446744073709551615);lia|exact R].
    + reflexivity.
    + constructor.
  - exact Call.
Qed.

Theorem eval_affine_set_infinity_owned m b : Mem.range_perm m b 0 88 Cur Freeable -> exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ge_set_infinity) [Vptr b Ptrofs.zero] E0 mf Vundef /\
  fe_at mf b 0 (repeat Int64.zero 5) /\ fe_at mf b 40 (repeat Int64.zero 5) /\
  Mem.load Mint32 mf b 80=Some (Vint Int.one) /\ Mem.range_perm mf b 0 88 Cur Freeable /\
  lframe (fun bx _=>bx<>b) m mf /\ readonly_preserved m mf.
Proof.
  intro Free.
  assert (Access:Mem.valid_access m Mint32 b 80 Writable).
  { split;[intros pos Range;eapply Mem.perm_implies;[apply Free;change (size_chunk Mint32) with 4 in Range;lia|constructor]
      |exists 20;reflexivity]. }
  destruct (Mem.valid_access_store m Mint32 b 80 (Vint Int.one) Access) as (m1 & Store).
  assert (Free1:Mem.range_perm m1 b 0 88 Cur Freeable) by
    (intros pos Range;eapply Mem.perm_store_1;[exact Store|apply Free;exact Range]).
  destruct (eval_fe_clear_owned m1 b 0 ltac:(lia) ltac:(exists 0;reflexivity)
    ltac:(change (40<=18446744073709551615);lia)
    ltac:(intros pos Range;eapply Mem.perm_implies;[apply Free1;lia|constructor]))
    as (mx & ClearX & X & LoadsX & PermX & ValidX).
  destruct (eval_fe_clear_owned mx b 40 ltac:(lia) ltac:(exists 5;reflexivity)
    ltac:(change (80<=18446744073709551615);lia)
    ltac:(intros pos Range;apply (proj2 (PermX b pos Cur Writable));
      eapply Mem.perm_implies;[apply Free1;lia|constructor]))
    as (mf & ClearY & Y & LoadsY & PermY & ValidY).
  assert (XF:fe_at mf b 0 (repeat Int64.zero 5)).
  { destruct X as (Base & Align & Max & Perm & Loads).
    split;[exact Base|];split;[exact Align|];split;[exact Max|];split.
    - intros pos Range;apply (proj2 (PermY b pos Cur Writable));apply Perm;exact Range.
    - intros i value Nth.
      assert (Index:(i<5)%nat) by
        (rewrite <-(repeat_length Int64.zero 5);apply nth_error_Some;rewrite Nth;discriminate).
      rewrite LoadsY by (right;left;change (size_chunk Mint64) with 8;lia);apply Loads;exact Nth. }
  assert (Flag:Mem.load Mint32 mf b 80=Some (Vint Int.one)).
  { rewrite LoadsY by (right;right;lia);rewrite LoadsX by (right;right;lia).
    exact (Mem.load_store_same _ _ _ _ _ _ Store). }
  assert (FreeF:Mem.range_perm mf b 0 88 Cur Freeable).
  { intros pos Range;apply (proj2 (PermY b pos Cur Freeable)),(proj2 (PermX b pos Cur Freeable)),Free1;exact Range. }
  assert (Frame:lframe (fun bx _=>bx<>b) m mf).
  { split.
    - intros chunk bx ofs Valid Outside.
      assert (Other:bx<>b) by (apply (Outside ofs);pose proof (size_chunk_pos chunk);lia).
      rewrite LoadsY,LoadsX by (left;exact Other);eapply Mem.load_store_other;[exact Store|left;exact Other].
    - split.
      + intros bx pos k p Valid Outside Perm.
        apply (proj2 (PermY bx pos k p)),(proj2 (PermX bx pos k p));eapply Mem.perm_store_1;eassumption.
      + intros bx Valid;apply ValidY,ValidX;eapply Mem.store_valid_block_1;eassumption. }
  set (le:=PTree.set _r (Vptr b Ptrofs.zero) (create_undef_temps (fn_temps f_secp256k1_ge_set_infinity))).
  assert (Entry:function_entry2 secp_ge f_secp256k1_ge_set_infinity [Vptr b Ptrofs.zero] m empty_env le m).
  { assert (Ok:fn_okb f_secp256k1_ge_set_infinity=true) by reflexivity.
    destruct (fn_okb_true _ Ok) as (N1 & N2 & Disjoint);constructor;[exact N1|exact N2|exact Disjoint|constructor|reflexivity]. }
  assert (Call:Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ge_set_infinity) [Vptr b Ptrofs.zero] E0 mf Vundef).
  { eapply eval_funcall_internal with (e:=empty_env) (le1:=le) (le2:=le) (m1:=m) (m2:=mf) (out:=Out_normal).
    - exact Entry.
    - rewrite affine_infinity_setter_source;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m1) (le1:=le).
      + apply (exec_affine_infinity_flag le m m1 b);[reflexivity|exact Store].
      + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mx) (le1:=le).
        * apply (exec_affine_infinity_clear le m1 mx b false);[reflexivity|exact ClearX].
        * apply (exec_affine_infinity_clear le mx mf b true);[reflexivity|exact ClearY].
    - reflexivity.
    - reflexivity. }
  exists mf;split;[exact Call|];split;[exact XF|];split;[exact Y|];split;[exact Flag|];
    split;[exact FreeF|];split;[exact Frame|].
  eapply (secp_closed_function_preserved f_secp256k1_ge_set_infinity);[vm_compute;reflexivity|reflexivity|exact Call].
Qed.
