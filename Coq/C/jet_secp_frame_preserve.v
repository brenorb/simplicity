(** Readonly preservation through the original frame helpers, including
    their syntactically present but disabled assertion prefixes. *)
From Coq Require Import ZArith List Bool Lia.
From compcert Require Import Coqlib AST Ctypes Cop Clight Clightdefs ClightBigstep Integers Values Memory Events Globalenvs Maps.
Require Import C.jets C.jet_secp_linkage C.jet_secp_field_io_preserve
 C.jet_clight_internal_frame C.jet_clight_internal_preserve C.jet_clight_determinism C.jet_sx_mem.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition disabled_assert_prefix dead :=
 Sloop(Sifthenelse(Eunop Onotbool(Econst_int Int.one tint)tint)dead Sskip)Sbreak.

Lemma exec_disabled_guard ge e le m dead t lef mf out :
 Clight2.exec_stmt ge e le m
  (Sifthenelse(Eunop Onotbool(Econst_int Int.one tint)tint)dead Sskip)t lef mf out ->
 mf=m /\ out=Out_normal.
Proof.
 intro Run;inversion Run;subst.
 assert(Value:v1=Vint Int.zero).
 { eapply eval_expr_determ;[eassumption|].
   eapply eval_Eunop;[constructor|reflexivity]. }
 subst v1.
 match goal with H:bool_val (Vint Int.zero) _ _=Some ?b |- _ =>
  change(Some false=Some b) in H;injection H as <- end.
 match goal with H:exec_stmt function_entry2 _ _ _ _ Sskip _ _ _ _ |- _=>inversion H;subst end.
 split;reflexivity.
Qed.

Lemma exec_disabled_assert ge e le m dead t lef mf out :
 Clight2.exec_stmt ge e le m(disabled_assert_prefix dead)t lef mf out -> mf=m.
Proof.
 intro Run;unfold disabled_assert_prefix in Run;inversion Run;subst.
 all:match goal with H:exec_stmt function_entry2 _ _ _ _ (Sifthenelse _ _ _) _ _ _ _ |- _=>
  destruct(exec_disabled_guard _ _ _ _ _ _ _ _ _ H) as[Same Normal];subst end.
 - match goal with H:out_break_or_return Out_normal _ |- _=>inversion H end.
 - match goal with H:exec_stmt function_entry2 _ _ _ _ Sbreak _ _ _ _ |- _=>inversion H;subst end;reflexivity.
 - match goal with H:exec_stmt function_entry2 _ _ _ _ Sbreak _ _ _ Out_normal |- _=>inversion H end.
Qed.

Lemma disabled_assert_function_preserved fd dead tail m args t mf result :
 fn_body fd=Ssequence(disabled_assert_prefix dead)tail ->
 closed_stmtb field_io_helpers tail=true ->
 forallb(fun it=>nonfunction_type(snd it))(fn_vars fd)=true ->
 Clight2.eval_funcall secp_ge m(Internal fd)args t mf result -> readonly_preserved m mf.
Proof.
 intros Body Closed Vars Run;inversion Run;subst.
 eapply preserved_trans;[eapply entry_preserved;eassumption|].
 eapply preserved_trans;[|eapply freelist_preserved;eassumption].
 match goal with H:exec_stmt function_entry2 _ _ _ _ (fn_body fd) _ _ _ _ |- _=>
  rewrite Body in H;inversion H;subst end.
 - match goal with H:exec_stmt function_entry2 _ _ _ _ (disabled_assert_prefix _) _ _ _ _ |- _=>
    pose proof(exec_disabled_assert _ _ _ _ _ _ _ _ _ H) as Same;subst end.
   eapply(proj1(internal_exec_preserved _ _ field_io_helpers_ok));
    [eassumption|eapply entry_plain;[eassumption|exact Vars]|exact Closed].
 - match goal with H:exec_stmt function_entry2 _ _ _ _ (disabled_assert_prefix _) _ _ _ _ |- _=>
    pose proof(exec_disabled_assert _ _ _ _ _ _ _ _ _ H) as Same;subst end.
   apply preserved_refl.
Qed.

Definition frame_assert_dead fd := match fn_body fd with
 | Ssequence(Sloop(Sifthenelse _ dead _)_)_=>dead | _=>Sskip end.
Definition frame_after_assert fd := match fn_body fd with
 | Ssequence _ tail=>tail | _=>Sskip end.

Lemma writeBit_disabled_prefix : fn_body f_writeBit=
 Ssequence(disabled_assert_prefix(frame_assert_dead f_writeBit))(frame_after_assert f_writeBit).
Proof. reflexivity. Qed.
Lemma skipBits_disabled_prefix : fn_body f_skipBits=
 Ssequence(disabled_assert_prefix(frame_assert_dead f_skipBits))(frame_after_assert f_skipBits).
Proof. reflexivity. Qed.
Lemma writeBit_tail_closed : closed_stmtb field_io_helpers(frame_after_assert f_writeBit)=true.
Proof. vm_compute;reflexivity. Qed.
Lemma skipBits_tail_closed : closed_stmtb field_io_helpers(frame_after_assert f_skipBits)=true.
Proof. vm_compute;reflexivity. Qed.

Theorem secp_writeBit_preserved m args t mf result :
 Clight2.eval_funcall secp_ge m(Internal f_writeBit)args t mf result -> readonly_preserved m mf.
Proof.
 apply(disabled_assert_function_preserved _ _ _ _ _ _ _ _
  writeBit_disabled_prefix writeBit_tail_closed eq_refl).
Qed.
Theorem secp_skipBits_preserved m args t mf result :
 Clight2.eval_funcall secp_ge m(Internal f_skipBits)args t mf result -> readonly_preserved m mf.
Proof.
 apply(disabled_assert_function_preserved _ _ _ _ _ _ _ _
  skipBits_disabled_prefix skipBits_tail_closed eq_refl).
Qed.

Lemma named_call_preserved (ge:genv)(e:env) id (fd:function) bf le m opt args t lef mf out :
 plain_env e -> Genv.find_symbol ge id=Some bf ->
 Genv.find_funct ge(Vptr bf Ptrofs.zero)=Some(Internal fd) ->
 (forall m args t mf result,Clight2.eval_funcall ge m(Internal fd)args t mf result -> readonly_preserved m mf) ->
 Clight2.exec_stmt ge e le m(Scall opt(Evar id(type_of_function fd))args)t lef mf out ->
 readonly_preserved m mf.
Proof.
 intros Plain Symbol Funct Preserve Run;inversion Run;subst.
 assert(NoLocal:e!id=None).
 { match goal with H:eval_expr _ _ _ _ (Evar _ _) _ |- _=>inversion H;subst end.
   match goal with H:eval_lvalue _ _ _ _ (Evar _ _) _ _ _ |- _=>inversion H;subst end.
   - match goal with H:e!id=Some(?b,?ty) |- _=>
      pose proof(Plain id b ty H) as Bad;discriminate Bad end.
   - assumption. }
 assert(VF:vf=Vptr bf Ptrofs.zero).
 { eapply eval_expr_determ;[eassumption|].
   eapply eval_Elvalue;[apply eval_Evar_global;[exact NoLocal|exact Symbol]|].
   apply deref_loc_reference;reflexivity. }
 subst vf.
 match goal with H:Genv.find_funct _ _=Some _ |- _=>rewrite Funct in H;injection H as <- end.
 eapply Preserve;eassumption.
Qed.

Lemma sequence_preserved ge e s1 s2 :
 (forall le m t lef mf out,Clight2.exec_stmt ge e le m s1 t lef mf out -> readonly_preserved m mf) ->
 (forall le m t lef mf out,Clight2.exec_stmt ge e le m s2 t lef mf out -> readonly_preserved m mf) ->
 forall le m t lef mf out,Clight2.exec_stmt ge e le m(Ssequence s1 s2)t lef mf out -> readonly_preserved m mf.
Proof. intros P1 P2 le m t lef mf out Run;inversion Run;subst;eauto using preserved_trans. Qed.

Lemma function_preserved_from_body ge fd :
 (forall e le m t lef mf out,Clight2.exec_stmt ge e le m(fn_body fd)t lef mf out ->
  plain_env e -> readonly_preserved m mf) ->
 forallb(fun it=>nonfunction_type(snd it))(fn_vars fd)=true ->
 forall m args t mf result,Clight2.eval_funcall ge m(Internal fd)args t mf result -> readonly_preserved m mf.
Proof.
 intros Body Vars m args t mf result Run;inversion Run;subst.
 eapply preserved_trans;[eapply entry_preserved;eassumption|].
 eapply preserved_trans;[|eapply freelist_preserved;eassumption].
 eapply Body;[eassumption|eapply entry_plain;eassumption].
Qed.
