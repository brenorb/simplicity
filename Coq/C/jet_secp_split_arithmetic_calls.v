(** Exact original Scalls after the rounding prefix. These adapters check
    linkage, local/global addresses, casts and unchanged temporary environments.
    Their execution premises are discharged by the composed suffix theorem. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_fns C.jet_secp_curve_statements
 C.jet_secp_statement_prefix C.jet_secp_split_rounding_calls C.jet_secp_split_constants
 C.jet_secp_scalar_lambda_global.
Import ListNotations Values Ctypes.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge split_basis_block scalar_lambda_block.

Definition split_scalar_address id := Eaddrof (Evar id (Tstruct __5826 noattr)) (tptr (Tstruct __5826 noattr)).
Definition split_scalar_parameter id := Etempvar id (tptr (Tstruct __5826 noattr)).
Definition split_product_statement (first:bool) := nth (if first then 5 else 6)%nat (fst split_parts) Sskip.
Definition split_second_statement := nth 7 (fst split_parts) Sskip.
Definition split_lambda_statement := nth 8 (fst split_parts) Sskip.
Definition split_negate_statement := nth 9 (fst split_parts) Sskip.
Definition split_last_statement := snd split_parts.
Definition split_arithmetic_suffix := statement_sequence (skipn 5 (fst split_parts)) (snd split_parts).

Lemma split_product_source first : split_product_statement first=
 curve_call _secp256k1_scalar_mul f_secp256k1_scalar_mul None
 [split_scalar_address (split_local_id first);split_scalar_address (split_local_id first);
  split_scalar_address (split_basis_id first)].
Proof. destruct first;reflexivity. Qed.
Lemma split_second_source : split_second_statement=
 curve_call _secp256k1_scalar_add f_secp256k1_scalar_add None
 [split_scalar_parameter _r2;split_scalar_address _c1;split_scalar_address _c2].
Proof. reflexivity. Qed.
Lemma split_lambda_source : split_lambda_statement=
 curve_call _secp256k1_scalar_mul f_secp256k1_scalar_mul None
 [split_scalar_parameter _r1;split_scalar_parameter _r2;split_scalar_address _secp256k1_const_lambda].
Proof. reflexivity. Qed.
Lemma split_negate_source : split_negate_statement=
 curve_call _secp256k1_scalar_negate f_secp256k1_scalar_negate None
 [split_scalar_parameter _r1;split_scalar_parameter _r1].
Proof. reflexivity. Qed.
Lemma split_last_source : split_last_statement=
 curve_call _secp256k1_scalar_add f_secp256k1_scalar_add None
 [split_scalar_parameter _r1;split_scalar_parameter _r1;split_scalar_parameter _k].
Proof. reflexivity. Qed.
Lemma split_arithmetic_source : split_arithmetic_suffix=
 Ssequence (split_product_statement true) (Ssequence (split_product_statement false)
 (Ssequence split_second_statement (Ssequence split_lambda_statement
 (Ssequence split_negate_statement split_last_statement)))).
Proof. reflexivity. Qed.
Lemma split_whole_source : fn_body f_secp256k1_scalar_split_lambda=
 statement_sequence (firstn 5 (fst split_parts)) split_arithmetic_suffix.
Proof. reflexivity. Qed.

Local Ltac split_linked := unfold secp_pure;repeat (first [left;reflexivity|right]).
Local Ltac split_args := first [apply eval_Enil|
 lazymatch goal with
 | |- eval_exprlist _ _ _ _ _ _ (Vptr ?b ?ofs :: _) =>
   eapply eval_Econs with (v1:=Vptr b ofs);
   [first [apply eval_Etempvar;assumption|
           apply eval_Eaddrof;apply eval_Evar_local;reflexivity|
           apply eval_Eaddrof;apply eval_Evar_global;[reflexivity|apply scalar_lambda_global_symbol]]|
    reflexivity|split_args]
 end].

Lemma exec_split_product (first:bool) bc1 bc2 le m mf :
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_scalar_mul)
 [Vptr (if first then bc1 else bc2) Ptrofs.zero;Vptr (if first then bc1 else bc2) Ptrofs.zero;
  Vptr (split_basis_block first) Ptrofs.zero] E0 mf Vundef ->
 Clight2.exec_stmt secp_ge (split_local_env bc1 bc2) le m (split_product_statement first) E0 le mf Out_normal.
Proof.
 intro Call;rewrite split_product_source.
 eapply (exec_curve_call _secp256k1_scalar_mul f_secp256k1_scalar_mul None _
  [Vptr (if first then bc1 else bc2) Ptrofs.zero;Vptr (if first then bc1 else bc2) Ptrofs.zero;
   Vptr (split_basis_block first) Ptrofs.zero] Vundef);[split_linked|reflexivity| |exact Call].
 eapply eval_Econs with (v1:=Vptr (if first then bc1 else bc2) Ptrofs.zero);
 [apply eval_Eaddrof;apply eval_Evar_local;destruct first;reflexivity|reflexivity|].
 eapply eval_Econs with (v1:=Vptr (if first then bc1 else bc2) Ptrofs.zero);
 [apply eval_Eaddrof;apply eval_Evar_local;destruct first;reflexivity|reflexivity|].
 eapply eval_Econs with (v1:=Vptr (split_basis_block first) Ptrofs.zero);
 [apply eval_Eaddrof;apply eval_Evar_global;[destruct first;reflexivity|apply split_basis_symbol]|
  reflexivity|constructor].
Qed.

Lemma exec_split_second bc1 bc2 le m mf br ret : le!_r2=Some (Vptr br Ptrofs.zero) ->
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_scalar_add)
 [Vptr br Ptrofs.zero;Vptr bc1 Ptrofs.zero;Vptr bc2 Ptrofs.zero] E0 mf (Vint ret) ->
 Clight2.exec_stmt secp_ge (split_local_env bc1 bc2) le m split_second_statement E0 le mf Out_normal.
Proof.
 intros R Call;rewrite split_second_source.
 eapply (exec_curve_call _secp256k1_scalar_add f_secp256k1_scalar_add None _
  [Vptr br Ptrofs.zero;Vptr bc1 Ptrofs.zero;Vptr bc2 Ptrofs.zero] (Vint ret));
 [split_linked|reflexivity|split_args|exact Call].
Qed.
Lemma exec_split_lambda bc1 bc2 le m mf br1 br2 :
 le!_r1=Some (Vptr br1 Ptrofs.zero) -> le!_r2=Some (Vptr br2 Ptrofs.zero) ->
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_scalar_mul)
 [Vptr br1 Ptrofs.zero;Vptr br2 Ptrofs.zero;Vptr scalar_lambda_block Ptrofs.zero] E0 mf Vundef ->
 Clight2.exec_stmt secp_ge (split_local_env bc1 bc2) le m split_lambda_statement E0 le mf Out_normal.
Proof.
 intros R1 R2 Call;rewrite split_lambda_source.
 eapply (exec_curve_call _secp256k1_scalar_mul f_secp256k1_scalar_mul None _
  [Vptr br1 Ptrofs.zero;Vptr br2 Ptrofs.zero;Vptr scalar_lambda_block Ptrofs.zero] Vundef);
 [split_linked|reflexivity|split_args|exact Call].
Qed.
Lemma exec_split_negate bc1 bc2 le m mf br : le!_r1=Some (Vptr br Ptrofs.zero) ->
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_scalar_negate)
 [Vptr br Ptrofs.zero;Vptr br Ptrofs.zero] E0 mf Vundef ->
 Clight2.exec_stmt secp_ge (split_local_env bc1 bc2) le m split_negate_statement E0 le mf Out_normal.
Proof.
 intros R Call;rewrite split_negate_source.
 eapply (exec_curve_call _secp256k1_scalar_negate f_secp256k1_scalar_negate None _
  [Vptr br Ptrofs.zero;Vptr br Ptrofs.zero] Vundef);
 [split_linked|reflexivity|split_args|exact Call].
Qed.
Lemma exec_split_last bc1 bc2 le m mf br bk ret :
 le!_r1=Some (Vptr br Ptrofs.zero) -> le!_k=Some (Vptr bk Ptrofs.zero) ->
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_scalar_add)
 [Vptr br Ptrofs.zero;Vptr br Ptrofs.zero;Vptr bk Ptrofs.zero] E0 mf (Vint ret) ->
 Clight2.exec_stmt secp_ge (split_local_env bc1 bc2) le m split_last_statement E0 le mf Out_normal.
Proof.
 intros R K Call;rewrite split_last_source.
 eapply (exec_curve_call _secp256k1_scalar_add f_secp256k1_scalar_add None _
  [Vptr br Ptrofs.zero;Vptr br Ptrofs.zero;Vptr bk Ptrofs.zero] (Vint ret));
 [split_linked|reflexivity|split_args|exact Call].
Qed.
