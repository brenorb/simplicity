(** Exact original descending-loop arithmetic shape and its skipped
    non-generator loop when no points were admitted. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Cop Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_curve_statements C.jet_secp_statement_prefix
 C.jet_secp_generator_digit_add.
Require Import C.jet_secp_generator_digit_control.
Import ListNotations Values Ctypes.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition generator_descending_loop := match
 nth 10 (fst (split_statement_last (fn_body f_secp256k1_ecmult_strauss_wnaf))) Sskip with
 | Ssequence _ loop=>loop | _=>Sskip end.
Definition generator_loop_arithmetic := match generator_descending_loop with
 | Sloop (Ssequence _ body) _=>body | _=>Sskip end.
Definition generator_nongenerator_statement := match generator_loop_arithmetic with
 | Ssequence _ (Ssequence inner _)=>inner | _=>Sskip end.
Definition generator_double_statement := curve_call _secp256k1_gej_double_var f_secp256k1_gej_double_var None
 [Etempvar _r (tptr (Tstruct __6123 noattr));Etempvar _r (tptr (Tstruct __6123 noattr));
  Ecast (Econst_int Int.zero tint) (tptr tvoid)].

Lemma generator_loop_arithmetic_source : generator_loop_arithmetic=
 Ssequence generator_double_statement (Ssequence generator_nongenerator_statement
   (Ssequence (generator_digit_dispatch false) (generator_digit_dispatch true))).
Proof. reflexivity. Qed.

Theorem exec_generator_nongenerator_empty e le m : le!_no=Some (Vlong Int64.zero) ->
 Clight2.exec_stmt secp_ge e le m generator_nongenerator_statement E0
   (PTree.set _np (Vlong Int64.zero) le) m Out_normal.
Proof.
 intro No.
 unfold generator_nongenerator_statement,generator_loop_arithmetic,generator_descending_loop.
 eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=PTree.set _np (Vlong Int64.zero) le).
 - apply exec_Sset;eapply eval_Ecast;[constructor|reflexivity].
 - eapply exec_Sloop_stop1 with (out':=Out_break);[|constructor].
   eapply exec_Sseq_2;[|discriminate].
   eapply exec_Sifthenelse with (v1:=Vint Int.zero) (b:=false);[|reflexivity|constructor].
   eapply eval_Ebinop.
   + apply eval_Etempvar;apply PTree.gss.
   + apply eval_Etempvar;rewrite PTree.gso by discriminate;exact No.
   + reflexivity.
Qed.

Lemma generator_descending_loop_source : generator_descending_loop=
 Sloop (Ssequence
   (Sifthenelse (Ebinop Oge (Etempvar _i tint) (Econst_int Int.zero tint) tint) Sskip Sbreak)
   generator_loop_arithmetic)
   (Sset _i (Ebinop Osub (Etempvar _i tint) (Econst_int Int.one tint) tint)).
Proof. reflexivity. Qed.

Lemma eval_generator_loop_guard e le m i : -1<=i<129 -> le!_i=Some (Vint (Int.repr i)) ->
 eval_expr secp_ge e le m
   (Ebinop Oge (Etempvar _i tint) (Econst_int Int.zero tint) tint)
   (Vint (if 0<=?i then Int.one else Int.zero)).
Proof.
 intros Index PI;eapply eval_Ebinop;[apply eval_Etempvar;exact PI|constructor|].
 change (Some (Val.of_bool (negb (Int.lt (Int.repr i) Int.zero)))=
   Some (Vint (if 0<=?i then Int.one else Int.zero))).
 unfold Int.lt;rewrite Int.signed_repr by
   (change Int.min_signed with (-2147483648);change Int.max_signed with 2147483647;lia).
 change (Some (Val.of_bool (negb (if Coqlib.zlt i 0 then true else false)))=
   Some (Vint (if 0<=?i then Int.one else Int.zero))).
 destruct (Coqlib.zlt i 0),(Z.leb_spec 0 i);try lia;reflexivity.
Qed.

Theorem exec_generator_loop_done e le m : le!_i=Some (Vint (Int.repr (-1))) ->
 Clight2.exec_stmt secp_ge e le m generator_descending_loop E0 le m Out_normal.
Proof.
 intro PI;rewrite generator_descending_loop_source.
 eapply exec_Sloop_stop1 with (out':=Out_break);[|constructor].
 eapply exec_Sseq_2;[|discriminate].
 eapply exec_Sifthenelse with (v1:=Vint Int.zero) (b:=false);[|reflexivity|constructor].
 exact (eval_generator_loop_guard e le m (-1) ltac:(lia) PI).
Qed.

Lemma exec_generator_loop_join e le m i lei mi lef mf :
 0<=i<129 -> le!_i=Some (Vint (Int.repr i)) -> lei!_i=Some (Vint (Int.repr i)) ->
 Clight2.exec_stmt secp_ge e le m generator_loop_arithmetic E0 lei mi Out_normal ->
 Clight2.exec_stmt secp_ge e (PTree.set _i (Vint (Int.repr (i-1))) lei) mi
   generator_descending_loop E0 lef mf Out_normal ->
 Clight2.exec_stmt secp_ge e le m generator_descending_loop E0 lef mf Out_normal.
Proof.
 intros Index PI PII Body Rest;rewrite generator_descending_loop_source in Rest|-*.
 eapply exec_Sloop_loop with (t1:=E0) (t2:=E0) (t3:=E0) (le1:=lei) (m1:=mi)
   (out1:=Out_normal) (le2:=PTree.set _i (Vint (Int.repr (i-1))) lei) (m2:=mi).
 - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le) (m1:=m).
   + eapply exec_Sifthenelse with (v1:=Vint Int.one) (b:=true);[|reflexivity|constructor].
     pose proof (eval_generator_loop_guard e le m i ltac:(lia) PI) as Guard.
     rewrite (proj2 (Z.leb_le 0 i) ltac:(lia)) in Guard;exact Guard.
   + exact Body.
 - constructor.
 - apply exec_Sset;eapply eval_Ebinop;[apply eval_Etempvar;exact PII|constructor|].
   change (Some (Vint (Int.sub (Int.repr i) Int.one))=Some (Vint (Int.repr (i-1)))).
   change Int.one with (Int.repr 1);rewrite Int.sub_signed,!Int.signed_repr by
     (change Int.min_signed with (-2147483648);change Int.max_signed with 2147483647;lia);reflexivity.
 - exact Rest.
Qed.
