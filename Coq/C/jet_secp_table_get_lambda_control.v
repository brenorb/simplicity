(** Original lambda-table lookup, reusing the signed window-5 index. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_exec C.jet_secp_linkage C.jets_secp C.jet_secp_curve_statements
 C.jet_secp_affine_fields C.jet_secp_table_get_control.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition table_get_lambda_x negative := Ebinop Oadd (Etempvar _x (tptr curve_fe_type))
 (table_get_index negative) (tptr curve_fe_type).
Definition table_get_lambda_y negative := Eaddrof (Efield (table_get_source negative) _y curve_fe_type)
 (tptr curve_fe_type).
Definition table_get_lambda_construct negative := curve_call _secp256k1_ge_set_xy f_secp256k1_ge_set_xy None
 [Etempvar _r (tptr curve_ge_type);table_get_lambda_x negative;table_get_lambda_y negative].
Definition table_get_lambda_choice := Sifthenelse table_get_guard
 (table_get_lambda_construct false) (Ssequence (table_get_lambda_construct true) table_get_negate).
Definition table_get_lambda_temps bd bt bx negative j := PTree.set _w (Vint (Int.repr 5))
 (PTree.set _n (Vint (Int.repr (table_get_digit negative j))) (PTree.set _x (Vptr bx Ptrofs.zero)
 (PTree.set _pre (Vptr bt Ptrofs.zero) (PTree.set _r (Vptr bd Ptrofs.zero)
 (create_undef_temps (fn_temps f_secp256k1_ecmult_table_get_ge_lambda)))))).

Lemma table_get_lambda_body_source : fn_body f_secp256k1_ecmult_table_get_ge_lambda=
 Ssequence (Sloop Sskip Sbreak) (Ssequence (Sloop Sskip Sbreak)
 (Ssequence (Sloop Sskip Sbreak) table_get_lambda_choice)).
Proof. reflexivity. Qed.
Lemma table_get_lambda_entry m bd bt bx negative j :
 function_entry2 secp_ge f_secp256k1_ecmult_table_get_ge_lambda
 [Vptr bd Ptrofs.zero;Vptr bt Ptrofs.zero;Vptr bx Ptrofs.zero;
  Vint (Int.repr (table_get_digit negative j));Vint (Int.repr 5)] m empty_env
 (table_get_lambda_temps bd bt bx negative j) m.
Proof.
 assert (OK:fn_okb f_secp256k1_ecmult_table_get_ge_lambda=true) by reflexivity.
 destruct (fn_okb_true _ OK) as (Vars & Params & Disjoint).
 constructor;[exact Vars|exact Params|exact Disjoint|constructor|reflexivity].
Qed.

Lemma eval_table_get_lambda_x e le m bx negative j : 0<=j<8 ->
 le!_x=Some (Vptr bx Ptrofs.zero) -> le!_n=Some (Vint (Int.repr (table_get_digit negative j))) ->
 eval_expr secp_ge e le m (table_get_lambda_x negative) (Vptr bx (Ptrofs.repr (40*j))).
Proof.
 intros Range X N;unfold table_get_lambda_x.
 eapply eval_Ebinop with (v1:=Vptr bx Ptrofs.zero) (v2:=Vint (Int.repr j)).
 - apply eval_Etempvar;exact X.
 - exact (eval_table_get_index e le m negative j Range N).
 - change (Some (Vptr bx (Ptrofs.add Ptrofs.zero
    (Ptrofs.mul (Ptrofs.repr 40) (Ptrofs.repr (Int.signed (Int.repr j))))))=
    Some (Vptr bx (Ptrofs.repr (40*j)))).
   rewrite Int.signed_repr by (change Int.min_signed with (-2147483648);change Int.max_signed with 2147483647;lia).
   rewrite Ptrofs.add_zero_l;unfold Ptrofs.mul.
   rewrite !Ptrofs.unsigned_repr by (change Ptrofs.max_unsigned with 18446744073709551615;lia);reflexivity.
Qed.

Lemma eval_table_get_lambda_y e le m bt negative j : 0<=j<8 ->
 le!_pre=Some (Vptr bt Ptrofs.zero) -> le!_n=Some (Vint (Int.repr (table_get_digit negative j))) ->
 eval_expr secp_ge e le m (table_get_lambda_y negative) (Vptr bt (Ptrofs.repr (88*j+40))).
Proof.
 intros Range Pre N;unfold table_get_lambda_y;apply eval_Eaddrof.
 destruct (affine_field_layout _y 40 ltac:(right;left;reflexivity)) as (co & Lookup & Offset).
 replace (Ptrofs.repr (88*j+40)) with (Ptrofs.add (Ptrofs.repr (88*j)) (Ptrofs.repr 40)).
 - eapply eval_Efield_struct with (co:=co) (delta:=40).
   + unfold table_get_source;eapply eval_Elvalue.
     * apply eval_Ederef;exact (eval_table_get_address e le m bt negative j Range Pre N).
     * apply deref_loc_copy;reflexivity.
   + reflexivity.
   + exact Lookup.
   + exact Offset.
 - unfold Ptrofs.add;rewrite !Ptrofs.unsigned_repr by
    (change Ptrofs.max_unsigned with 18446744073709551615;lia);reflexivity.
Qed.
