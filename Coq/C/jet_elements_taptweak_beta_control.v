(** Actual auxiliary-array statements and their argument evaluation for the
    single-point Strauss caller. The index ranges include the exit test. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_curve_statements C.jet_secp_affine_fields
 C.jet_secp_generator_globalz_call C.jet_secp_beta_global.
Import ListNotations Values Ctypes.
Local Open Scope Z_scope.
Set Default Timeout 10.
Require Import C.jet_secp_beta_loop_control C.jet_elements_taptweak_pure
 C.jet_elements_taptweak_beta C.jet_transport.
Definition elements_taptweak_beta_expressions:=
 [beta_aux_width;beta_aux_index;beta_aux_out;beta_aux_table;beta_aux_in;beta_aux_guard;beta_aux_outer_guard].
Lemma elements_taptweak_beta_expressions_checked:
 forallb(expr_okb secp_ge elements_taptweak_ge)elements_taptweak_beta_expressions=true.
Proof. vm_compute;reflexivity. Qed.
Lemma elements_taptweak_state_pointer_checked field delta ty:
 In(field,delta)[(_pre_a,8);(_aux,0)] ->
 expr_okb secp_ge elements_taptweak_ge(generator_state_pointer field ty)=true.
Proof.
 intros[Same|[Same|[]]];injection Same as <- <-;vm_compute;reflexivity.
Qed.
Local Opaque secp_ge elements_taptweak_ge elements_taptweak_beta_block.
Lemma elements_taptweak_beta_expression expression e le m v:
 In expression elements_taptweak_beta_expressions ->eval_expr secp_ge e le m expression v ->
 eval_expr elements_taptweak_ge e le m expression v.
Proof.
 intros Member Run;apply(proj1(eval_expr_transport secp_ge elements_taptweak_ge e le m));[exact Run|].
 pose proof elements_taptweak_beta_expressions_checked as Checked.
 rewrite forallb_forall in Checked;exact(Checked expression Member).
Qed.
Lemma eval_elements_taptweak_state_pointer e le m b base field delta ty v:
 In(field,delta)[(_pre_a,8);(_aux,0)] ->
 le!_state=Some(Vptr b(Ptrofs.repr base)) ->0<=base ->base+24<=Ptrofs.max_unsigned ->
 Mem.load Mptr m b(base+delta)=Some v ->
 eval_expr elements_taptweak_ge e le m(generator_state_pointer field ty)v.
Proof.
 intros Field State Base Hi Load.
 apply(proj1(eval_expr_transport secp_ge elements_taptweak_ge e le m)).
 - eapply eval_generator_state_pointer;[exact Field|exact State|exact Base|exact Hi|exact Load].
 - apply(elements_taptweak_state_pointer_checked field delta ty);exact Field.
Qed.
Lemma eval_elements_taptweak_beta_aux_width e le m : eval_expr elements_taptweak_ge e le m beta_aux_width (Vlong (Int64.repr 8)).
Proof.
 intros;eapply elements_taptweak_beta_expression.
 - left;reflexivity.
 - eapply eval_beta_aux_width;eassumption.
Qed.
Lemma eval_elements_taptweak_beta_aux_index e le m i : 0<=i<=8 ->
 le!_np=Some (Vlong Int64.zero) -> le!_i=Some (Vint (Int.repr i)) ->
 eval_expr elements_taptweak_ge e le m beta_aux_index (Vlong (Int64.repr i)).
Proof.
 intros;eapply elements_taptweak_beta_expression.
 - right;left;reflexivity.
 - eapply eval_beta_aux_index;eassumption.
Qed.
Lemma eval_elements_taptweak_beta_aux_out e le m bx i : 0<=i<8 ->
 le!_np=Some (Vlong Int64.zero) -> le!_i=Some (Vint (Int.repr i)) ->
 le!_t'30=Some (Vptr bx Ptrofs.zero) ->
 eval_expr elements_taptweak_ge e le m beta_aux_out (Vptr bx (Ptrofs.repr (40*i))).
Proof.
 intros;eapply elements_taptweak_beta_expression.
 - right;right;left;reflexivity.
 - eapply eval_beta_aux_out;eassumption.
Qed.
Lemma eval_elements_taptweak_beta_aux_table e le m bt i : 0<=i<8 ->
 le!_np=Some (Vlong Int64.zero) -> le!_i=Some (Vint (Int.repr i)) ->
 le!_t'31=Some (Vptr bt Ptrofs.zero) ->
 eval_expr elements_taptweak_ge e le m beta_aux_table (Vptr bt (Ptrofs.repr (88*i))).
Proof.
 intros;eapply elements_taptweak_beta_expression.
 - right;right;right;left;reflexivity.
 - eapply eval_beta_aux_table;eassumption.
Qed.
Lemma eval_elements_taptweak_beta_aux_in e le m bt i : 0<=i<8 ->
 le!_np=Some (Vlong Int64.zero) -> le!_i=Some (Vint (Int.repr i)) ->
 le!_t'31=Some (Vptr bt Ptrofs.zero) ->
 eval_expr elements_taptweak_ge e le m beta_aux_in (Vptr bt (Ptrofs.repr (88*i))).
Proof.
 intros;eapply elements_taptweak_beta_expression.
 - right;right;right;right;left;reflexivity.
 - eapply eval_beta_aux_in;eassumption.
Qed.
Lemma eval_elements_taptweak_beta_aux_guard e le m i : 0<=i<=8 -> le!_i=Some (Vint (Int.repr i)) ->
 eval_expr elements_taptweak_ge e le m beta_aux_guard (Vint (if Z.ltb i 8 then Int.one else Int.zero)).
Proof.
 intros;eapply elements_taptweak_beta_expression.
 - right;right;right;right;right;left;reflexivity.
 - eapply eval_beta_aux_guard;eassumption.
Qed.
Lemma eval_elements_taptweak_beta_aux_outer_guard e le m (done:bool) :
 le!_np=Some (Vlong (if done then Int64.one else Int64.zero)) -> le!_no=Some (Vlong Int64.one) ->
 eval_expr elements_taptweak_ge e le m beta_aux_outer_guard (Vint (if done then Int.zero else Int.one)).
Proof.
 intros;eapply elements_taptweak_beta_expression.
 - right;right;right;right;right;right;left;reflexivity.
 - eapply eval_beta_aux_outer_guard;eassumption.
Qed.
Lemma exec_elements_taptweak_beta_aux_step e le m i : 0<=i<8 -> le!_i=Some (Vint (Int.repr i)) ->
 Clight2.exec_stmt elements_taptweak_ge e le m beta_aux_step E0 (PTree.set _i (Vint (Int.repr (i+1))) le) m Out_normal.
Proof.
 intros Range I;unfold beta_aux_step;apply exec_Sset.
 eapply eval_Ebinop with (v1:=Vint (Int.repr i)) (v2:=Vint Int.one);
 [apply eval_Etempvar;exact I|constructor|].
 change (Some (Vint (Int.add (Int.repr i) Int.one))=Some (Vint (Int.repr (i+1)))).
 unfold Int.add;rewrite Int.unsigned_repr by (change Int.max_unsigned with 4294967295;lia);reflexivity.
Qed.
Lemma exec_elements_taptweak_beta_aux_outer_step e le m : le!_np=Some (Vlong Int64.zero) ->
 Clight2.exec_stmt elements_taptweak_ge e le m beta_aux_outer_step E0 (PTree.set _np (Vlong Int64.one) le) m Out_normal.
Proof.
 intro NP;unfold beta_aux_outer_step;apply exec_Sset.
 eapply eval_Ebinop;[apply eval_Etempvar;exact NP|constructor|reflexivity].
Qed.
Lemma eval_elements_taptweak_beta_aux_constant e le m:e!_secp256k1_const_beta=None ->
 eval_expr elements_taptweak_ge e le m beta_aux_constant(Vptr elements_taptweak_beta_block Ptrofs.zero).
Proof.
 intro Local;unfold beta_aux_constant;apply eval_Eaddrof;apply eval_Evar_global;
 [exact Local|exact elements_taptweak_beta_symbol].
Qed.
