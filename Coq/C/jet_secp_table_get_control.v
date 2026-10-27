(** Exact original window-5 table-lookup statements and argument evaluation. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_exec C.jet_secp_linkage C.jets_secp C.jet_secp_curve_statements.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition table_get_digit (negative:bool) j := if negative then -(2*j+1) else 2*j+1.
Definition table_get_magnitude (negative:bool) := if negative then Eunop Oneg (Etempvar _n tint) tint
 else Etempvar _n tint.
Definition table_get_index negative := Ebinop Odiv
 (Ebinop Osub (table_get_magnitude negative) (Econst_int Int.one tint) tint)
 (Econst_int (Int.repr 2) tint) tint.
Definition table_get_address negative := Ebinop Oadd (Etempvar _pre (tptr curve_ge_type))
 (table_get_index negative) (tptr curve_ge_type).
Definition table_get_source negative := Ederef (table_get_address negative) curve_ge_type.
Definition table_get_destination := Ederef (Etempvar _r (tptr curve_ge_type)) curve_ge_type.
Definition table_get_y_address := Eaddrof (Efield table_get_destination _y curve_fe_type) (tptr curve_fe_type).
Definition table_get_guard := Ebinop Ogt (Etempvar _n tint) (Econst_int Int.zero tint) tint.
Definition table_get_negate := curve_call _secp256k1_fe_negate f_secp256k1_fe_negate None
 [table_get_y_address;table_get_y_address;Econst_int Int.one tint].
Definition table_get_choice := Sifthenelse table_get_guard
 (Sassign table_get_destination (table_get_source false))
 (Ssequence (Sassign table_get_destination (table_get_source true)) table_get_negate).
Definition table_get_temps bd bt negative j := PTree.set _w (Vint (Int.repr 5))
 (PTree.set _n (Vint (Int.repr (table_get_digit negative j)))
 (PTree.set _pre (Vptr bt Ptrofs.zero) (PTree.set _r (Vptr bd Ptrofs.zero)
 (create_undef_temps (fn_temps f_secp256k1_ecmult_table_get_ge))))).

Lemma table_get_magnitude_type negative : typeof (table_get_magnitude negative)=tint.
Proof. destruct negative;reflexivity. Qed.

Lemma table_get_body_source : fn_body f_secp256k1_ecmult_table_get_ge=
 Ssequence (Sloop Sskip Sbreak) (Ssequence (Sloop Sskip Sbreak)
 (Ssequence (Sloop Sskip Sbreak) table_get_choice)).
Proof. reflexivity. Qed.

Lemma table_get_entry m bd bt negative j : function_entry2 secp_ge f_secp256k1_ecmult_table_get_ge
 [Vptr bd Ptrofs.zero;Vptr bt Ptrofs.zero;Vint (Int.repr (table_get_digit negative j));Vint (Int.repr 5)]
 m empty_env (table_get_temps bd bt negative j) m.
Proof.
 assert (OK:fn_okb f_secp256k1_ecmult_table_get_ge=true) by reflexivity.
 destruct (fn_okb_true _ OK) as (Vars & Params & Disjoint).
 constructor;[exact Vars|exact Params|exact Disjoint|constructor|reflexivity].
Qed.

Lemma eval_table_get_magnitude e le m negative j :
 le!_n=Some (Vint (Int.repr (table_get_digit negative j))) ->
 eval_expr secp_ge e le m (table_get_magnitude negative) (Vint (Int.repr (2*j+1))).
Proof.
 intro N;destruct negative;cbn [table_get_magnitude table_get_digit] in *.
 - eapply eval_Eunop;[apply eval_Etempvar;exact N|].
   change (Some (Vint (Int.neg (Int.repr (-(2*j+1))))) = Some (Vint (Int.repr (2*j+1)))).
   rewrite Int.neg_repr;f_equal;f_equal;f_equal;lia.
 - apply eval_Etempvar;exact N.
Qed.

Lemma table_get_index_machine j : 0<=j<8 ->
 Int.sub (Int.repr (2*j+1)) Int.one=Int.repr (2*j) /\
 Int.divs (Int.repr (2*j)) (Int.repr 2)=Int.repr j.
Proof.
 intro Range;split.
 - rewrite Int.sub_signed,!Int.signed_repr by
   (change Int.min_signed with (-2147483648);change Int.max_signed with 2147483647;lia).
   change (Int.signed Int.one) with 1;f_equal;lia.
 - unfold Int.divs;rewrite !Int.signed_repr by
   (change Int.min_signed with (-2147483648);change Int.max_signed with 2147483647;lia).
   rewrite Z.quot_div_nonneg by lia;replace (2*j) with (j*2) by ring.
   rewrite Z.div_mul by lia;reflexivity.
Qed.

Lemma eval_table_get_index e le m negative j : 0<=j<8 ->
 le!_n=Some (Vint (Int.repr (table_get_digit negative j))) ->
 eval_expr secp_ge e le m (table_get_index negative) (Vint (Int.repr j)).
Proof.
 intros Range N;destruct (table_get_index_machine j Range) as [Sub Div].
 unfold table_get_index;eapply eval_Ebinop with (v1:=Vint (Int.repr (2*j))) (v2:=Vint (Int.repr 2)).
 - eapply eval_Ebinop with (v1:=Vint (Int.repr (2*j+1))) (v2:=Vint Int.one).
   + apply eval_table_get_magnitude;exact N.
   + constructor.
   + rewrite table_get_magnitude_type.
     change (Some (Vint (Int.sub (Int.repr (2*j+1)) Int.one))=Some (Vint (Int.repr (2*j))));rewrite Sub;reflexivity.
 - constructor.
 - change ((if Int.eq (Int.repr 2) Int.zero ||
    Int.eq (Int.repr (2*j)) (Int.repr Int.min_signed) && Int.eq (Int.repr 2) Int.mone
    then None else Some (Vint (Int.divs (Int.repr (2*j)) (Int.repr 2))))=Some (Vint (Int.repr j))).
   change (Int.eq (Int.repr 2) Int.zero) with false.
   change (Int.eq (Int.repr 2) Int.mone) with false.
   rewrite Bool.andb_false_r;change (Some (Vint (Int.divs (Int.repr (2*j)) (Int.repr 2)))=Some (Vint (Int.repr j))).
   rewrite Div;reflexivity.
Qed.

Lemma eval_table_get_address e le m bt negative j : 0<=j<8 ->
 le!_pre=Some (Vptr bt Ptrofs.zero) ->
 le!_n=Some (Vint (Int.repr (table_get_digit negative j))) ->
 eval_expr secp_ge e le m (table_get_address negative) (Vptr bt (Ptrofs.repr (88*j))).
Proof.
 intros Range Pre N;unfold table_get_address.
 eapply eval_Ebinop with (v1:=Vptr bt Ptrofs.zero) (v2:=Vint (Int.repr j)).
 - apply eval_Etempvar;exact Pre.
 - apply eval_table_get_index;assumption.
 - change (Some (Vptr bt (Ptrofs.add Ptrofs.zero
    (Ptrofs.mul (Ptrofs.repr 88) (Ptrofs.repr (Int.signed (Int.repr j))))))=
    Some (Vptr bt (Ptrofs.repr (88*j)))).
   rewrite Int.signed_repr by (change Int.min_signed with (-2147483648);change Int.max_signed with 2147483647;lia).
   rewrite Ptrofs.add_zero_l;unfold Ptrofs.mul.
   rewrite !Ptrofs.unsigned_repr by (change Ptrofs.max_unsigned with 18446744073709551615;lia);reflexivity.
Qed.

Lemma eval_table_get_guard e le m negative j : 0<=j<8 ->
 le!_n=Some (Vint (Int.repr (table_get_digit negative j))) ->
 eval_expr secp_ge e le m table_get_guard (Vint (if negative then Int.zero else Int.one)).
Proof.
 intros Range N;unfold table_get_guard;eapply eval_Ebinop;
 [apply eval_Etempvar;exact N|constructor|].
 change (Some (Val.of_bool (Int.lt Int.zero (Int.repr (table_get_digit negative j))))=
  Some (Vint (if negative then Int.zero else Int.one))).
 unfold Int.lt;change (Int.signed Int.zero) with 0;rewrite Int.signed_repr by
  (destruct negative;cbn [table_get_digit];change Int.min_signed with (-2147483648);change Int.max_signed with 2147483647;lia).
 destruct negative;cbn [table_get_digit];destruct (zlt 0 _);first [reflexivity|lia].
Qed.
