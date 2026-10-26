(** Exact original ge_set_gej_zinv statements and their argument lvalues. *)
From Coq Require Import ZArith List.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_curve_statements C.jet_secp_double_statements
 C.jet_secp_statement_prefix C.jet_secp_curve_square.
Import ListNotations Values Ctypes.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition ge_zinv_env b2 b3 := PTree.set _zi3 (b3,curve_fe_type)
 (PTree.set _zi2 (b2,curve_fe_type) empty_env).
Definition ge_zinv_result_field fid ty := Efield
 (Ederef (Etempvar _r (tptr curve_ge_type)) curve_ge_type) fid ty.
Definition ge_zinv_result_address fid := Eaddrof (ge_zinv_result_field fid curve_fe_type) (tptr curve_fe_type).
Definition ge_zinv_square_statement := curve_call _secp256k1_fe_sqr f_secp256k1_fe_sqr None
 [curve_local_address _zi2;Etempvar _zi (tptr curve_fe_type)].
Definition ge_zinv_cube_statement := curve_call _secp256k1_fe_mul f_secp256k1_fe_mul None
 [curve_local_address _zi3;curve_local_address _zi2;Etempvar _zi (tptr curve_fe_type)].
Definition ge_zinv_product_statement (y:bool) := curve_call _secp256k1_fe_mul f_secp256k1_fe_mul None
 [ge_zinv_result_address (if y then _y else _x);double_point_address _a (if y then _y else _x);
  curve_local_address (if y then _zi3 else _zi2)].
Definition ge_zinv_arithmetic := Ssequence ge_zinv_square_statement
 (Ssequence ge_zinv_cube_statement (Ssequence (ge_zinv_product_statement false)
  (Ssequence (ge_zinv_product_statement true) Sskip))).
Definition ge_zinv_flag_statement := Ssequence
 (Sset _t'1 (double_point_field _a _infinity tint))
 (Sassign (ge_zinv_result_field _infinity tint) (Etempvar _t'1 tint)).
Definition ge_zinv_statements := [ge_zinv_square_statement;ge_zinv_cube_statement;
 ge_zinv_product_statement false;ge_zinv_product_statement true].

Lemma ge_zinv_body_source : fn_body f_secp256k1_ge_set_gej_zinv=
 Ssequence (Sloop Sskip Sbreak)
  (C.jet_secp_statement_prefix.statement_sequence ge_zinv_statements ge_zinv_flag_statement).
Proof. reflexivity. Qed.

Lemma eval_ge_zinv_result_field e le m br fid delta ty :
 In (fid,delta) [(_x,0);(_y,40);(_infinity,80)] -> le!_r=Some (Vptr br Ptrofs.zero) ->
 eval_lvalue secp_ge e le m (ge_zinv_result_field fid ty) br (Ptrofs.repr delta) Full.
Proof.
 intros Field R;destruct (curve_affine_layout fid delta Field) as (co & Lookup & Offset).
 unfold ge_zinv_result_field;rewrite <- (Ptrofs.add_zero_l (Ptrofs.repr delta)).
 eapply eval_Efield_struct with (co:=co) (delta:=delta).
 - eapply eval_Elvalue;[apply eval_Ederef;apply eval_Etempvar;exact R|apply deref_loc_copy;reflexivity].
 - reflexivity.
 - exact Lookup.
 - exact Offset.
Qed.

Lemma eval_ge_zinv_result_address e le m br (y:bool) : le!_r=Some (Vptr br Ptrofs.zero) ->
 eval_expr secp_ge e le m (ge_zinv_result_address (if y then _y else _x))
  (Vptr br (Ptrofs.repr (C.jet_secp_curve_square.curve_square_offset y))).
Proof.
 intro R;apply eval_Eaddrof;apply eval_ge_zinv_result_field;
  [destruct y;cbn [C.jet_secp_curve_square.curve_square_offset In];tauto|exact R].
Qed.
