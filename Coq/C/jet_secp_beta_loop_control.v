(** Actual auxiliary-array statements and their argument evaluation for the
    single-point Strauss caller. The index ranges include the exit test. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_curve_statements C.jet_secp_affine_fields
 C.jet_secp_generator_globalz_call C.jet_secp_beta_global.
Import ListNotations Values Ctypes.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge beta_block.

Definition beta_aux_width := Ebinop Oshl (Econst_long Int64.one tlong)
 (Ebinop Osub (Econst_int (Int.repr 5) tint) (Econst_int (Int.repr 2) tint) tint) tlong.
Definition beta_aux_index := Ebinop Oadd
 (Ebinop Omul (Etempvar _np tulong) beta_aux_width tulong) (Etempvar _i tint) tulong.
Definition beta_aux_out := Ebinop Oadd (Etempvar _t'30 (tptr curve_fe_type)) beta_aux_index (tptr curve_fe_type).
Definition beta_aux_table := Ebinop Oadd (Etempvar _t'31 (tptr curve_ge_type)) beta_aux_index (tptr curve_ge_type).
Definition beta_aux_in := Eaddrof (Efield (Ederef beta_aux_table curve_ge_type) _x curve_fe_type) (tptr curve_fe_type).
Definition beta_aux_constant := Eaddrof (Evar _secp256k1_const_beta curve_fe_type) (tptr curve_fe_type).
Definition beta_aux_call := curve_call _secp256k1_fe_mul f_secp256k1_fe_mul None
 [beta_aux_out;beta_aux_in;beta_aux_constant].
Definition beta_aux_inner := match generator_auxiliary_body with Ssequence _ s=>s|_=>Sskip end.
Definition beta_aux_iteration := match beta_aux_inner with Sloop (Ssequence _ s) _=>s|_=>Sskip end.
Definition beta_aux_guard := Ebinop Olt (Etempvar _i tint) beta_aux_width tint.
Definition beta_aux_step := Sset _i (Ebinop Oadd (Etempvar _i tint) (Econst_int Int.one tint) tint).
Definition beta_aux_temps (le:temp_env) bx bt :=
 PTree.set _t'31 (Vptr bt Ptrofs.zero) (PTree.set _t'30 (Vptr bx Ptrofs.zero) le).

Lemma beta_aux_iteration_source : beta_aux_iteration=
 Ssequence (Sset _t'30 (generator_state_pointer _aux curve_fe_type))
 (Ssequence (Sset _t'31 (generator_state_pointer _pre_a curve_ge_type)) beta_aux_call).
Proof. reflexivity. Qed.
Lemma beta_aux_inner_source : beta_aux_inner=
 Sloop (Ssequence (Sifthenelse beta_aux_guard Sskip Sbreak) beta_aux_iteration) beta_aux_step.
Proof. reflexivity. Qed.
Lemma beta_aux_body_source : generator_auxiliary_body=
 Ssequence (Sset _i (Econst_int Int.zero tint)) beta_aux_inner.
Proof. reflexivity. Qed.

Lemma eval_beta_aux_width e le m : eval_expr secp_ge e le m beta_aux_width (Vlong (Int64.repr 8)).
Proof.
 unfold beta_aux_width;eapply eval_Ebinop with (v1:=Vlong Int64.one) (v2:=Vint (Int.repr 3));
 [constructor|eapply eval_Ebinop;[constructor|constructor|reflexivity]|reflexivity].
Qed.
Lemma eval_beta_aux_index e le m i : 0<=i<=8 ->
 le!_np=Some (Vlong Int64.zero) -> le!_i=Some (Vint (Int.repr i)) ->
 eval_expr secp_ge e le m beta_aux_index (Vlong (Int64.repr i)).
Proof.
 intros Range NP I;unfold beta_aux_index.
 eapply eval_Ebinop with (v1:=Vlong Int64.zero) (v2:=Vint (Int.repr i)).
 - eapply eval_Ebinop with (v1:=Vlong Int64.zero) (v2:=Vlong (Int64.repr 8));
   [apply eval_Etempvar;exact NP|apply eval_beta_aux_width|reflexivity].
 - apply eval_Etempvar;exact I.
 - change (Some (Vlong (Int64.add Int64.zero (Int64.repr (Int.signed (Int.repr i)))))=
   Some (Vlong (Int64.repr i))).
   rewrite Int.signed_repr by (change Int.min_signed with (-2147483648);change Int.max_signed with 2147483647;lia).
   rewrite Int64.add_zero_l;reflexivity.
Qed.

Lemma eval_beta_aux_out e le m bx i : 0<=i<8 ->
 le!_np=Some (Vlong Int64.zero) -> le!_i=Some (Vint (Int.repr i)) ->
 le!_t'30=Some (Vptr bx Ptrofs.zero) ->
 eval_expr secp_ge e le m beta_aux_out (Vptr bx (Ptrofs.repr (40*i))).
Proof.
 intros Range NP I X;unfold beta_aux_out.
 eapply eval_Ebinop with (v1:=Vptr bx Ptrofs.zero) (v2:=Vlong (Int64.repr i)).
 - apply eval_Etempvar;exact X.
 - apply eval_beta_aux_index;[lia|exact NP|exact I].
 - change (Some (Vptr bx (Ptrofs.add Ptrofs.zero (Ptrofs.mul (Ptrofs.repr 40)
    (Ptrofs.repr (Int64.unsigned (Int64.repr i))))))=Some (Vptr bx (Ptrofs.repr (40*i)))).
   rewrite Int64.unsigned_repr by (change Int64.max_unsigned with 18446744073709551615;lia).
   rewrite Ptrofs.add_zero_l;unfold Ptrofs.mul.
   rewrite !Ptrofs.unsigned_repr by (change Ptrofs.max_unsigned with 18446744073709551615;lia);reflexivity.
Qed.
Lemma eval_beta_aux_table e le m bt i : 0<=i<8 ->
 le!_np=Some (Vlong Int64.zero) -> le!_i=Some (Vint (Int.repr i)) ->
 le!_t'31=Some (Vptr bt Ptrofs.zero) ->
 eval_expr secp_ge e le m beta_aux_table (Vptr bt (Ptrofs.repr (88*i))).
Proof.
 intros Range NP I Table;unfold beta_aux_table.
 eapply eval_Ebinop with (v1:=Vptr bt Ptrofs.zero) (v2:=Vlong (Int64.repr i)).
 - apply eval_Etempvar;exact Table.
 - apply eval_beta_aux_index;[lia|exact NP|exact I].
 - change (Some (Vptr bt (Ptrofs.add Ptrofs.zero (Ptrofs.mul (Ptrofs.repr 88)
    (Ptrofs.repr (Int64.unsigned (Int64.repr i))))))=Some (Vptr bt (Ptrofs.repr (88*i)))).
   rewrite Int64.unsigned_repr by (change Int64.max_unsigned with 18446744073709551615;lia).
   rewrite Ptrofs.add_zero_l;unfold Ptrofs.mul.
   rewrite !Ptrofs.unsigned_repr by (change Ptrofs.max_unsigned with 18446744073709551615;lia);reflexivity.
Qed.
Lemma eval_beta_aux_in e le m bt i : 0<=i<8 ->
 le!_np=Some (Vlong Int64.zero) -> le!_i=Some (Vint (Int.repr i)) ->
 le!_t'31=Some (Vptr bt Ptrofs.zero) ->
 eval_expr secp_ge e le m beta_aux_in (Vptr bt (Ptrofs.repr (88*i))).
Proof.
 intros Range NP I Table;unfold beta_aux_in;apply eval_Eaddrof.
 destruct (affine_field_layout _x 0 ltac:(left;reflexivity)) as (co & Lookup & Offset).
 rewrite <- (Ptrofs.add_zero (Ptrofs.repr (88*i))).
 eapply eval_Efield_struct with (co:=co) (delta:=0).
 - eapply eval_Elvalue;
   [apply eval_Ederef;exact (eval_beta_aux_table e le m bt i Range NP I Table)|apply deref_loc_copy;reflexivity].
 - reflexivity.
 - exact Lookup.
 - exact Offset.
Qed.
Lemma eval_beta_aux_constant e le m : e!_secp256k1_const_beta=None ->
 eval_expr secp_ge e le m beta_aux_constant (Vptr beta_block Ptrofs.zero).
Proof.
 intro Local;unfold beta_aux_constant;apply eval_Eaddrof;apply eval_Evar_global;[exact Local|exact beta_symbol].
Qed.

Lemma eval_beta_aux_guard e le m i : 0<=i<=8 -> le!_i=Some (Vint (Int.repr i)) ->
 eval_expr secp_ge e le m beta_aux_guard (Vint (if Z.ltb i 8 then Int.one else Int.zero)).
Proof.
 intros Range I;unfold beta_aux_guard.
 eapply eval_Ebinop with (v1:=Vint (Int.repr i)) (v2:=Vlong (Int64.repr 8));
 [apply eval_Etempvar;exact I|apply eval_beta_aux_width|].
 change (Some (Val.of_bool (Int64.lt (Int64.repr (Int.signed (Int.repr i))) (Int64.repr 8)))=
  Some (Vint (if Z.ltb i 8 then Int.one else Int.zero))).
 rewrite Int.signed_repr by (change Int.min_signed with (-2147483648);change Int.max_signed with 2147483647;lia).
 unfold Int64.lt;rewrite !Int64.signed_repr by
  (change Int64.min_signed with (-9223372036854775808);change Int64.max_signed with 9223372036854775807;lia).
 destruct (zlt i 8), (Z.ltb_spec i 8);first [reflexivity|lia].
Qed.

Lemma exec_beta_aux_step e le m i : 0<=i<8 -> le!_i=Some (Vint (Int.repr i)) ->
 Clight2.exec_stmt secp_ge e le m beta_aux_step E0 (PTree.set _i (Vint (Int.repr (i+1))) le) m Out_normal.
Proof.
 intros Range I;unfold beta_aux_step;apply exec_Sset.
 eapply eval_Ebinop with (v1:=Vint (Int.repr i)) (v2:=Vint Int.one);
 [apply eval_Etempvar;exact I|constructor|].
 change (Some (Vint (Int.add (Int.repr i) Int.one))=Some (Vint (Int.repr (i+1)))).
 unfold Int.add;rewrite Int.unsigned_repr by (change Int.max_unsigned with 4294967295;lia);reflexivity.
Qed.

Lemma beta_aux_temps_other le bx bt id : id<>_t'30 -> id<>_t'31 ->
 (beta_aux_temps le bx bt)!id=le!id.
Proof. intros A B;unfold beta_aux_temps;rewrite !PTree.gso by congruence;reflexivity. Qed.

Definition beta_aux_outer := match generator_auxiliary_statement with Ssequence _ s=>s|_=>Sskip end.
Definition beta_aux_outer_guard := Ebinop Olt (Etempvar _np tulong) (Etempvar _no tulong) tint.
Definition beta_aux_outer_step := Sset _np
 (Ebinop Oadd (Etempvar _np tulong) (Econst_int Int.one tint) tulong).

Lemma beta_aux_outer_source : beta_aux_outer=
 Sloop (Ssequence (Sifthenelse beta_aux_outer_guard Sskip Sbreak) generator_auxiliary_body) beta_aux_outer_step.
Proof. reflexivity. Qed.
Lemma beta_aux_statement_source : generator_auxiliary_statement=
 Ssequence (Sset _np (Ecast (Econst_int Int.zero tint) tulong)) beta_aux_outer.
Proof. reflexivity. Qed.

Lemma eval_beta_aux_outer_guard e le m (done:bool) :
 le!_np=Some (Vlong (if done then Int64.one else Int64.zero)) -> le!_no=Some (Vlong Int64.one) ->
 eval_expr secp_ge e le m beta_aux_outer_guard (Vint (if done then Int.zero else Int.one)).
Proof.
 intros NP No;unfold beta_aux_outer_guard.
 eapply eval_Ebinop;[apply eval_Etempvar;exact NP|apply eval_Etempvar;exact No|].
 destruct done;reflexivity.
Qed.

Lemma exec_beta_aux_outer_step e le m : le!_np=Some (Vlong Int64.zero) ->
 Clight2.exec_stmt secp_ge e le m beta_aux_outer_step E0 (PTree.set _np (Vlong Int64.one) le) m Out_normal.
Proof.
 intro NP;unfold beta_aux_outer_step;apply exec_Sset.
 eapply eval_Ebinop;[apply eval_Etempvar;exact NP|constructor|reflexivity].
Qed.
