(** Exact original ge_set_xo_var statement tree and its actual argument
    addresses. Execution and public jet correctness are separate obligations. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Cop Clight Clightdefs ClightBigstep Maps Memory Values Events Errors.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_curve_statements C.jet_secp_statement_prefix.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition decompress_source := Etempvar _x (tptr curve_fe_type).
Definition decompress_point_field fid ty :=
 Efield (Ederef (Etempvar _r (tptr curve_ge_type)) curve_ge_type) fid ty.
Definition decompress_point_address fid := Eaddrof (decompress_point_field fid curve_fe_type) (tptr curve_fe_type).
Definition decompress_copy_stmt := Sassign (decompress_point_field _x curve_fe_type)
 (Ederef decompress_source curve_fe_type).
Definition decompress_square_stmt := curve_call _secp256k1_fe_sqr f_secp256k1_fe_sqr None
 [curve_local_address _x2;decompress_source].
Definition decompress_cube_stmt := curve_call _secp256k1_fe_mul f_secp256k1_fe_mul None
 [curve_local_address _x3;decompress_source;curve_local_address _x2].
Definition decompress_finite_stmt := Sassign (decompress_point_field _infinity tint) (Econst_int Int.zero tint).
Definition decompress_add_stmt := curve_call _secp256k1_fe_add_int f_secp256k1_fe_add_int None
 [curve_local_address _x3;Econst_int (Int.repr 7) tint].
Definition decompress_root_call := curve_call _secp256k1_fe_sqrt_var f_secp256k1_fe_sqrt_var (Some _t'1)
 [decompress_point_address _y;curve_local_address _x3].
Definition decompress_root_test := Ssequence decompress_root_call
 (Sifthenelse (Eunop Onotbool (Etempvar _t'1 tint) tint)
  (Sreturn (Some (Econst_int Int.zero tint))) Sskip).
Definition decompress_normalize_stmt := curve_call _secp256k1_fe_normalize_var f_secp256k1_fe_normalize_var None
 [decompress_point_address _y].
Definition decompress_odd_call := curve_call _secp256k1_fe_is_odd f_secp256k1_fe_is_odd (Some _t'2)
 [decompress_point_address _y].
Definition decompress_negate_stmt := curve_call _secp256k1_fe_negate f_secp256k1_fe_negate None
 [decompress_point_address _y;decompress_point_address _y;Econst_int Int.one tint].
Definition decompress_odd_test := Ssequence decompress_odd_call
 (Sifthenelse (Ebinop One (Etempvar _t'2 tint) (Etempvar _odd tint) tint) decompress_negate_stmt Sskip).
Definition decompress_rest := Ssequence decompress_root_test
 (Ssequence decompress_normalize_stmt (Ssequence decompress_odd_test (Sreturn (Some (Econst_int Int.one tint))))).
Definition decompress_prefix := [decompress_copy_stmt;decompress_square_stmt;decompress_cube_stmt;
 decompress_finite_stmt;decompress_add_stmt].

Lemma decompress_helper_body_source : fn_body f_secp256k1_ge_set_xo_var=
 statement_sequence decompress_prefix decompress_rest.
Proof. reflexivity. Qed.

Lemma eval_decompress_field e le m br fid delta ty :
 In (fid,delta) [(_x,0);(_y,40);(_infinity,80)] -> le!_r=Some (Vptr br Ptrofs.zero) ->
 eval_lvalue secp_ge e le m (decompress_point_field fid ty) br (Ptrofs.repr delta) Full.
Proof.
 intros Field R;destruct (curve_affine_layout fid delta Field) as (co & Composite & Offset).
 unfold decompress_point_field;rewrite <-(Ptrofs.add_zero_l (Ptrofs.repr delta)).
 eapply eval_Efield_struct with (co:=co) (delta:=delta).
 - eapply eval_Elvalue;[apply eval_Ederef;apply eval_Etempvar;exact R|apply deref_loc_copy;reflexivity].
 - reflexivity.
 - exact Composite.
 - exact Offset.
Qed.
Lemma eval_decompress_field_address e le m br fid delta :
 In (fid,delta) [(_x,0);(_y,40)] -> le!_r=Some (Vptr br Ptrofs.zero) ->
 eval_expr secp_ge e le m (decompress_point_address fid) (Vptr br (Ptrofs.repr delta)).
Proof.
 intros Field R;apply eval_Eaddrof;apply eval_decompress_field;[|exact R].
 destruct Field as [Field|[Field|Field]];[left|right;left|contradiction];exact Field.
Qed.
