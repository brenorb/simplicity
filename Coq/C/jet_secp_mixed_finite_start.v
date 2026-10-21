(** Actual finite mixed-addition prelude and first field operation.
    A prefix only: the remaining arithmetic and final function call are open. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_fns C.jet_secp_curve_statements
  C.jet_secp_double_statements C.jet_secp_mixed_head C.jet_secp_point_square_coordinate
  C.jet_secp_point_write_run C.jet_secp_gej_curve_coordinate C.jet_secp_fe_nv C.jet_sx_mem
  C.jet_secp_multiply_normalize_bridge C.jet_secp_square_columns C.jet_secp_multiply_finish_product
  C.jet_secp_square_numeric C.jet_secp_fe_math C.jet_secp_multiply_checkpoint_columns.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition mixed_b_field fid ty := Efield
  (Ederef (Etempvar _b (tptr curve_ge_type)) curve_ge_type) fid ty.
Definition mixed_b_head := match mixed_tail with | Ssequence h _ => h | _ => Sskip end.
Definition mixed_finite_rest := match mixed_tail with | Ssequence _ t => t | _ => Sskip end.
Definition mixed_square_stmt := curve_call _secp256k1_fe_sqr f_secp256k1_fe_sqr None
  [curve_local_address _z12;double_point_address _a _z].
Definition mixed_after_square := match mixed_finite_rest with | Ssequence _ t => t | _ => Sskip end.
Definition mixed_start_stmt := Ssequence mixed_head (Ssequence mixed_b_head mixed_square_stmt).
Lemma mixed_finite_source : fn_body f_secp256k1_gej_add_ge_var=
  Ssequence mixed_head (Ssequence mixed_b_head (Ssequence mixed_square_stmt mixed_after_square)).
Proof. reflexivity. Qed.

Lemma eval_mixed_b_field e le m bb fid delta ty :
  In (fid,delta) [(_x,0);(_y,40);(_infinity,80)] -> le!_b=Some (Vptr bb Ptrofs.zero) ->
  eval_lvalue secp_ge e le m (mixed_b_field fid ty) bb (Ptrofs.repr delta) Full.
Proof.
  intros HH HB;destruct (curve_affine_layout fid delta HH) as (co & HC & HO).
  unfold mixed_b_field;rewrite <- (Ptrofs.add_zero_l (Ptrofs.repr delta)).
  eapply eval_Efield_struct with (co:=co) (delta:=delta).
  - eapply eval_Elvalue;[apply eval_Ederef;apply eval_Etempvar;exact HB|apply deref_loc_copy;reflexivity].
  - reflexivity.
  - exact HC.
  - exact HO.
Qed.
Lemma exec_mixed_b_head_finite e le m bb :
  le!_b=Some (Vptr bb Ptrofs.zero) -> Mem.load Mint32 m bb 80=Some (Vint Int.zero) ->
  Clight2.exec_stmt secp_ge e le m mixed_b_head E0
    (PTree.set _t'3 (Vint Int.zero) le) m Out_normal.
Proof.
  intros HB HF;unfold mixed_b_head,mixed_tail.
  eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=PTree.set _t'3 (Vint Int.zero) le).
  - apply exec_Sset;eapply eval_Elvalue.
    + apply eval_mixed_b_field;[cbn [In];tauto|exact HB].
    + eapply deref_loc_value with (chunk:=Mint32);[reflexivity|].
      change (Mem.load Mint32 m bb 80=Some (Vint Int.zero));exact HF.
  - eapply exec_Sifthenelse with (v1:=Vint Int.zero) (b:=false).
    + apply eval_Etempvar;apply PTree.gss.
    + reflexivity.
    + apply exec_Sskip.
Qed.

Theorem exec_mixed_finite_start e le m ba bb bz z :
  le!_a=Some (Vptr ba Ptrofs.zero) -> le!_b=Some (Vptr bb Ptrofs.zero) ->
  e!_z12=Some (bz,curve_fe_type) -> e!_secp256k1_fe_sqr=None -> ba<>bz ->
  Mem.load Mint32 m ba 120=Some (Vint Int.zero) -> Mem.load Mint32 m bb 80=Some (Vint Int.zero) ->
  square_input_bounds z -> fe_at m ba 80 (words5 z) ->
  Mem.range_perm m ba 0 128 Cur Freeable -> Mem.range_perm m bz 0 40 Cur Freeable ->
  exists mf,
  Clight2.exec_stmt secp_ge e le m mixed_start_stmt E0
    (PTree.set _t'3 (Vint Int.zero) (PTree.set _t'4 (Vint Int.zero) le)) mf Out_normal /\
  fe_at mf bz 0 (words5 (square_words z)) /\ Mem.range_perm mf bz 0 40 Cur Freeable /\
  fe_at mf ba 80 (words5 z) /\ Mem.range_perm mf ba 0 128 Cur Freeable /\
  radix_value (square_words z) mod field_prime=(radix_value z*radix_value z) mod field_prime /\
  square_input_bounds (square_words z) /\ lframe (point_square_coordinate_frame PointZ bz ba) m mf.
Proof.
  intros HA HB HE HS HSep HAF HBF BZ HZ HFA HFZ.
  destruct (eval_point_square_coordinate PointZ z m bz ba BZ HFZ HZ HFA (not_eq_sym HSep))
    as (mf & HC & ZO & ZF & ZI & AF & Val & Bounds & Tight & Frame).
  exists mf;split.
  - unfold mixed_start_stmt.
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=PTree.set _t'4 (Vint Int.zero) le).
    + apply exec_mixed_head_finite with (ba:=ba);assumption.
    + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m)
        (le1:=PTree.set _t'3 (Vint Int.zero) (PTree.set _t'4 (Vint Int.zero) le)).
      * apply exec_mixed_b_head_finite with (bb:=bb);[rewrite PTree.gso by discriminate;exact HB|exact HBF].
      * unfold mixed_square_stmt;eapply exec_curve_call with
          (vargs:=[Vptr bz Ptrofs.zero;Vptr ba (Ptrofs.repr 80)]) (v:=Vundef).
        -- unfold secp_pure;repeat (first [left;reflexivity|right]).
        -- exact HS.
        -- eapply eval_Econs;[apply eval_curve_local;exact HE|reflexivity|].
           eapply eval_Econs.
           ++ apply eval_double_point_address;[cbn [In];tauto|].
              rewrite !PTree.gso by discriminate;exact HA.
           ++ reflexivity.
           ++ constructor.
        -- exact HC.
  - split;[exact ZO|];split;[exact ZF|];split;[exact ZI|];split;[exact AF|].
    split;[exact Val|];split;assumption.
Qed.
