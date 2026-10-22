(** Actual field copies into the fresh point used by gej_eq_ge_var.
    Reuse the shared verified struct-copy contract, without a libc premise. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Events Values.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_sx_mem
 C.jet_secp_gej_negate_fields C.jet_secp_field_copy_owned C.jet_secp_multiply_normalize_bridge
 C.jet_secp_curve_frame.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Theorem exec_gej_negate_separate_field le m bs bd fid delta w :
 In (fid,delta) [(_x,0);(_y,40);(_z,80)] -> bs<>bd ->
 le!_a=Some (Vptr bs Ptrofs.zero) -> le!_r=Some (Vptr bd Ptrofs.zero) ->
 fe_at m bs delta (words5 w) -> Mem.range_perm m bd 0 128 Cur Freeable -> exists mf,
 Clight2.exec_stmt secp_ge empty_env le m (gej_negate_field_copy_stmt fid) E0 le mf Out_normal /\
 fe_at mf bd delta (words5 w) /\
 (forall b pos k p,Mem.perm mf b pos k p <-> Mem.perm m b pos k p) /\
 lframe (fun b pos=>b<>bd \/ pos<delta \/ delta+40<=pos) m mf.
Proof.
 intros HF NE Source Dest Field Free.
 assert (Bounds : 0<=delta /\ delta+40<=128 /\ (8|delta)).
 { destruct HF as [HE|[HE|[HE|HE]]];[| | |contradiction];inversion HE;subst;
   repeat split;try lia;[exists 0|exists 5|exists 10];reflexivity. }
 destruct Bounds as (Low & High & Align).
 assert (HAll : In (fid,delta) [(_x,0);(_y,40);(_z,80);(_infinity,120)]).
 { destruct HF as [HE|[HE|[HE|HE]]];[left|right;left|right;right;left|contradiction];exact HE. }
 assert (Max : 128<=Ptrofs.max_unsigned) by (change (128<=18446744073709551615);lia).
 assert (SrcL : eval_lvalue secp_ge empty_env le m
  (Efield (Ederef (Etempvar _a (tptr (Tstruct __6123 noattr))) (Tstruct __6123 noattr))
   fid (Tstruct __5467 noattr)) bs (Ptrofs.repr delta) Full).
 { exact (eval_gej_pointer_field le m bs 0 _a fid delta (Tstruct __5467 noattr) HAll ltac:(lia) Max Source). }
 assert (DstL : eval_lvalue secp_ge empty_env le m
  (Efield (Ederef (Etempvar _r (tptr (Tstruct __6123 noattr))) (Tstruct __6123 noattr))
   fid (Tstruct __5467 noattr)) bd (Ptrofs.repr delta) Full).
 { exact (eval_gej_pointer_field le m bd 0 _r fid delta (Tstruct __5467 noattr) HAll ltac:(lia) Max Dest). }
 unfold gej_negate_field_copy_stmt.
 eapply exec_field_copy_owned;[reflexivity|reflexivity| |exact DstL|exact NE|exact Field|exact Low|exact Align|lia|].
 - eapply eval_Elvalue;[exact SrcL|apply deref_loc_copy;reflexivity].
 - intros pos HP;apply Free;lia.
Qed.

Theorem exec_gej_negate_separate_three_copies le m bs bd x y z :
 bs<>bd -> le!_a=Some (Vptr bs Ptrofs.zero) -> le!_r=Some (Vptr bd Ptrofs.zero) ->
 fe_at m bs 0 (words5 x) -> fe_at m bs 40 (words5 y) -> fe_at m bs 80 (words5 z) ->
 Mem.range_perm m bd 0 128 Cur Freeable -> exists mx my mz,
 Clight2.exec_stmt secp_ge empty_env le m (gej_negate_field_copy_stmt _x) E0 le mx Out_normal /\
 Clight2.exec_stmt secp_ge empty_env le mx (gej_negate_field_copy_stmt _y) E0 le my Out_normal /\
 Clight2.exec_stmt secp_ge empty_env le my (gej_negate_field_copy_stmt _z) E0 le mz Out_normal /\
 fe_at mz bd 0 (words5 x) /\ fe_at mz bd 40 (words5 y) /\ fe_at mz bd 80 (words5 z) /\
 Mem.range_perm mz bd 0 128 Cur Freeable /\ lframe (fun b pos=>b<>bd \/ 120<=pos) m mz.
Proof.
 intros NE Src Dst X Y Z Free.
 destruct (exec_gej_negate_separate_field le m bs bd _x 0 x ltac:(left;reflexivity) NE Src Dst X Free)
  as (mx & CopyX & XX & PermX & FrameX).
 assert (YX : fe_at mx bs 40 (words5 y)).
 { eapply curve_keep_field_range;[reflexivity|exact Y|exact FrameX|];intros;left;exact NE. }
 assert (ZX : fe_at mx bs 80 (words5 z)).
 { eapply curve_keep_field_range;[reflexivity|exact Z|exact FrameX|];intros;left;exact NE. }
 assert (FreeX : Mem.range_perm mx bd 0 128 Cur Freeable).
 { intros pos HP;apply (proj2 (PermX bd pos Cur Freeable));apply Free;exact HP. }
 destruct (exec_gej_negate_separate_field le mx bs bd _y 40 y ltac:(right;left;reflexivity) NE Src Dst YX FreeX)
  as (my & CopyY & YY & PermY & FrameY).
 assert (XY : fe_at my bd 0 (words5 x)).
 { eapply curve_keep_field_range;[reflexivity|exact XX|exact FrameY|];intros;right;left;lia. }
 assert (ZY : fe_at my bs 80 (words5 z)).
 { eapply curve_keep_field_range;[reflexivity|exact ZX|exact FrameY|];intros;left;exact NE. }
 assert (FreeY : Mem.range_perm my bd 0 128 Cur Freeable).
 { intros pos HP;apply (proj2 (PermY bd pos Cur Freeable));apply FreeX;exact HP. }
 destruct (exec_gej_negate_separate_field le my bs bd _z 80 z ltac:(right;right;left;reflexivity) NE Src Dst ZY FreeY)
  as (mz & CopyZ & ZZ & PermZ & FrameZ).
 assert (XZ : fe_at mz bd 0 (words5 x)).
 { eapply curve_keep_field_range;[reflexivity|exact XY|exact FrameZ|];intros;right;left;lia. }
 assert (YZ : fe_at mz bd 40 (words5 y)).
 { eapply curve_keep_field_range;[reflexivity|exact YY|exact FrameZ|];intros;right;left;lia. }
 exists mx,my,mz;split;[exact CopyX|];split;[exact CopyY|];split;[exact CopyZ|].
 split;[exact XZ|];split;[exact YZ|];split;[exact ZZ|];split.
 - intros pos HP;apply (proj2 (PermZ bd pos Cur Freeable));apply FreeY;exact HP.
 - eapply lframe_trans.
   + eapply lframe_implies;[exact FrameX|];intros b pos [HN|HP] HV;[left;exact HN|right;right;lia].
   + eapply lframe_trans.
     * eapply lframe_implies;[exact FrameY|];intros b pos [HN|HP] HV;[left;exact HN|right;right;lia].
     * eapply lframe_implies;[exact FrameZ|];intros b pos [HN|HP] HV;[left;exact HN|right;right;lia].
Qed.
