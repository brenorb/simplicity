(** The exact field-negation statement shared by both signed lookup bodies. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv
 C.jet_secp_curve_statements C.jet_secp_affine_fields C.jet_secp_table_get_control
 C.jet_secp_affine_negate_words C.jet_secp_field_negate_separate C.jet_secp_multiply_normalize_bridge.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Lemma exec_table_get_negate le m bd y : le!_r=Some (Vptr bd Ptrofs.zero) ->
 fe_at m bd 40 (words5 y) -> Mem.range_perm m bd 0 88 Cur Freeable -> exists mf,
 Clight2.exec_stmt secp_ge empty_env le m table_get_negate E0 le mf Out_normal /\
 fe_at mf bd 40 (words5 (negate_sep_words y)) /\ Mem.range_perm mf bd 0 88 Cur Freeable /\
 lframe (fun b pos=>b<>bd \/ pos<40 \/ 80<=pos) m mf.
Proof.
 intros R Y Free;destruct (eval_affine_y_negate_words y m bd Y Free) as (mf & Call & YF & FreeF & Frame).
 exists mf;split;[|split;[exact YF|];split;assumption].
 unfold table_get_negate;eapply exec_curve_call with
 (vargs:=[Vptr bd (Ptrofs.repr 40);Vptr bd (Ptrofs.repr 40);Vint Int.one]) (v:=Vundef).
 - unfold C.jet_secp_fns.secp_pure;repeat (first [left;reflexivity|right]).
 - reflexivity.
 - eapply eval_Econs with (v1:=Vptr bd (Ptrofs.repr 40));[|reflexivity|].
   + apply (eval_affine_field_address le m bd 0 _r _y 40);
     [right;left;reflexivity|lia| |exact R];change (88<=18446744073709551615);lia.
   + eapply eval_Econs with (v1:=Vptr bd (Ptrofs.repr 40));[|reflexivity|].
     * apply (eval_affine_field_address le m bd 0 _r _y 40);
       [right;left;reflexivity|lia| |exact R];change (88<=18446744073709551615);lia.
     * eapply eval_Econs;[constructor|reflexivity|constructor].
 - exact Call.
Qed.
