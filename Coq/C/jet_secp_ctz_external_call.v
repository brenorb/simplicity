(** Actual production ctz64 call boundary, without postulating a counting
    model. An external-call premise here is an unresolved dependency, not a
    public jet theorem or a discharged library obligation. *)
From Coq Require Import String ZArith List Lia.
From compcert Require Import Coqlib Integers AST Builtins Ctypes Cop Clight Clightdefs
  ClightBigstep Maps Memory Values Events Globalenvs.
Require Import C.jet_sx_exec C.jet_secp_linkage C.jets_secp
  C.jet_secp_ctz_semantics_gap C.jet_clight_determinism.
Import ListNotations Ctypes Values.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition ctz_entry_temps x := PTree.set _x (Vlong x)
  (create_undef_temps (fn_temps f_secp256k1_ctz64_var)).
Definition ctz_builtin_call := Scall (Some _t'1)
  (Evar ___builtin_ctzl (Tfunction (Tcons tulong Tnil) tint cc_default))
  [Ecast (Etempvar _x tulong) tulong].
Definition ctz_then_body := Ssequence ctz_builtin_call (Sreturn (Some (Etempvar _t'1 tint))).
Definition ctz_after_noop := match fn_body f_secp256k1_ctz64_var with
  | Ssequence _ s=>s | _=>Sskip end.
Lemma ctz_body_source : fn_body f_secp256k1_ctz64_var=
  Ssequence (Sloop Sskip Sbreak) ctz_after_noop.
Proof. reflexivity. Qed.
Lemma ctz_after_noop_source : ctz_after_noop=
  Ssequence (Sifthenelse production_ctz_guard ctz_then_body Sskip)
    (Ssequence
      (Scall (Some _t'2) (Evar ___builtin_ctzll (Tfunction (Tcons tulong Tnil) tint cc_default))
        [Etempvar _x tulong])
      (Sreturn (Some (Etempvar _t'2 tint)))).
Proof. reflexivity. Qed.

Lemma ctz_builtin_linked : exists b,
  Genv.find_symbol secp_ge ___builtin_ctzl=Some b /\
  Genv.find_funct_ptr secp_ge b=Some
    (External (EF_builtin "__builtin_ctzl" ctz64_signature) (Tcons tulong Tnil) tint cc_default).
Proof. exists (secp_symbol_block ___builtin_ctzl);split;reflexivity. Qed.
Local Opaque secp_ge.

Lemma ctz_function_entry m x :
  function_entry2 secp_ge f_secp256k1_ctz64_var [Vlong x] m empty_env (ctz_entry_temps x) m.
Proof.
  assert (OK : fn_okb f_secp256k1_ctz64_var=true) by reflexivity.
  destruct (fn_okb_true _ OK) as (HN1 & HN2 & HD).
  constructor;[exact HN1|exact HN2|exact HD|constructor|reflexivity].
Qed.

Lemma ctz_noop_loop_inv e le m t le' m' out :
  Clight2.exec_stmt secp_ge e le m (Sloop Sskip Sbreak) t le' m' out ->
  t=E0 /\ le'=le /\ m'=m /\ out=Out_normal.
Proof.
  intro Run;inversion Run;subst;
    repeat match goal with
    | H : exec_stmt _ _ _ _ _ Sskip _ _ _ _ |- _ => inversion H;subst;clear H
    | H : exec_stmt _ _ _ _ _ Sbreak _ _ _ _ |- _ => inversion H;subst;clear H
    end;
    repeat match goal with H : out_break_or_return _ _ |- _ => inversion H;subst;clear H end;
    repeat split;reflexivity.
Qed.

Lemma exec_ctz_after_noop e le m s t le' m' out :
  Clight2.exec_stmt secp_ge e le m (Ssequence (Sloop Sskip Sbreak) s) t le' m' out ->
  Clight2.exec_stmt secp_ge e le m s t le' m' out.
Proof.
  intro Run;inversion Run;subst.
  - match goal with H : exec_stmt _ _ _ _ _ (Sloop Sskip Sbreak) _ _ _ _ |- _ =>
      destruct (ctz_noop_loop_inv _ _ _ _ _ _ _ H) as (-> & -> & -> & _) end.
    assumption.
  - match goal with H : exec_stmt _ _ _ _ _ (Sloop Sskip Sbreak) _ _ _ _ |- _ =>
      destruct (ctz_noop_loop_inv _ _ _ _ _ _ _ H) as (_ & _ & _ & ->) end;contradiction.
Qed.

Lemma ctz_argument_eval e le m x : le!_x=Some (Vlong x) ->
  eval_exprlist secp_ge e le m [Ecast (Etempvar _x tulong) tulong] (Tcons tulong Tnil) [Vlong x].
Proof.
  intro HX;eapply eval_Econs.
  - eapply eval_Ecast;[apply eval_Etempvar;exact HX|reflexivity].
  - reflexivity.
  - constructor.
Qed.

Lemma exec_ctz_builtin_from_external le m mf x n : le!_x=Some (Vlong x) ->
  external_functions_sem "__builtin_ctzl" ctz64_signature secp_ge [Vlong x] m E0 (Vint n) mf ->
  Clight2.exec_stmt secp_ge empty_env le m ctz_builtin_call E0
    (PTree.set _t'1 (Vint n) le) mf Out_normal.
Proof.
  intros HX Ext;destruct ctz_builtin_linked as (bf & HS & HF).
  unfold ctz_builtin_call;eapply exec_Scall with (vf:=Vptr bf Ptrofs.zero)
    (vargs:=[Vlong x])
    (f:=External (EF_builtin "__builtin_ctzl" ctz64_signature) (Tcons tulong Tnil) tint cc_default)
    (vres:=Vint n).
  - reflexivity.
  - eapply eval_Elvalue;[eapply eval_Evar_global;[reflexivity|exact HS]|apply deref_loc_reference;reflexivity].
  - apply ctz_argument_eval;exact HX.
  - exact HF.
  - reflexivity.
  - apply eval_funcall_external.
    change (builtin_or_external_sem "__builtin_ctzl" ctz64_signature secp_ge [Vlong x] m E0 (Vint n) mf).
    rewrite production_ctzl_is_abstract_external;exact Ext.
Qed.

Theorem eval_ctz64_from_external x n m mf :
  external_functions_sem "__builtin_ctzl" ctz64_signature secp_ge [Vlong x] m E0 (Vint n) mf ->
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ctz64_var) [Vlong x] E0 mf (Vint n).
Proof.
  intro Ext.
  eapply eval_funcall_internal with (e:=empty_env) (le1:=ctz_entry_temps x)
    (le2:=PTree.set _t'1 (Vint n) (ctz_entry_temps x)) (m1:=m) (m2:=mf)
    (out:=Out_return (Some (Vint n,tint))).
  - apply ctz_function_entry.
  - rewrite ctz_body_source;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=ctz_entry_temps x).
    + eapply exec_Sloop_stop2 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=ctz_entry_temps x)
        (out1:=Out_normal) (out2:=Out_break);constructor.
    + rewrite ctz_after_noop_source;eapply exec_Sseq_2;[|discriminate].
      eapply exec_Sifthenelse with (v1:=Vint Int.one) (b:=true).
      * apply production_ctz_guard_true.
      * reflexivity.
      * unfold ctz_then_body;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mf)
          (le1:=PTree.set _t'1 (Vint n) (ctz_entry_temps x)).
        -- eapply exec_ctz_builtin_from_external;[reflexivity|exact Ext].
        -- apply exec_Sreturn_some;apply eval_Etempvar;apply PTree.gss.
  - split;[discriminate|reflexivity].
  - reflexivity.
Qed.

Lemma exec_ctz_builtin_requires_external le m t le' mf out x :
  le!_x=Some (Vlong x) ->
  Clight2.exec_stmt secp_ge empty_env le m ctz_builtin_call t le' mf out ->
  exists r, external_functions_sem "__builtin_ctzl" ctz64_signature secp_ge [Vlong x] m t r mf.
Proof.
  intros HX Run;unfold ctz_builtin_call in Run;inversion Run;subst.
  match goal with H : classify_fun _= _ |- _ => inversion H;subst;clear H end.
  destruct ctz_builtin_linked as (bf & HS & HF).
  assert (FunExpr : eval_expr secp_ge empty_env le m
    (Evar ___builtin_ctzl (Tfunction (Tcons tulong Tnil) tint cc_default)) (Vptr bf Ptrofs.zero)).
  { eapply eval_Elvalue;[eapply eval_Evar_global;[reflexivity|exact HS]|apply deref_loc_reference;reflexivity]. }
  pose proof (ctz_argument_eval empty_env le m x HX) as ArgExpr.
  match goal with H : eval_expr _ _ _ _ _ ?vf |- _ =>
    is_var vf;assert (EV : vf=Vptr bf Ptrofs.zero) by
      (eapply eval_expr_determ;[exact H|exact FunExpr]);subst vf end.
  match goal with H : eval_exprlist _ _ _ _ _ _ ?vargs |- _ =>
    is_var vargs;assert (EA : vargs=[Vlong x]) by
      (eapply eval_exprlist_determ;[exact H|exact ArgExpr]);subst vargs end.
  rewrite Genv.find_funct_find_funct_ptr,HF in H8.
  injection H8 as EF;subst f.
  match goal with H : eval_funcall _ _ _ (External _ _ _ _) _ _ _ _ |- _ => inversion H;subst;clear H end.
  match goal with H : external_call _ _ _ _ _ ?r _ |- _ =>
    exists r;change (builtin_or_external_sem "__builtin_ctzl" ctz64_signature secp_ge [Vlong x] m t r mf) in H;
    rewrite production_ctzl_is_abstract_external in H;exact H end.
Qed.

Lemma ctz_sequence_has_head e le m first second t le' mf out :
  Clight2.exec_stmt secp_ge e le m (Ssequence first second) t le' mf out ->
  exists th lh mh oh,Clight2.exec_stmt secp_ge e le m first th lh mh oh.
Proof. intro Run;inversion Run;subst;eauto 6. Qed.

Lemma ctz_selected_branch e le m t le' mf out :
  Clight2.exec_stmt secp_ge e le m (Sifthenelse production_ctz_guard ctz_then_body Sskip) t le' mf out ->
  Clight2.exec_stmt secp_ge e le m ctz_then_body t le' mf out.
Proof.
  intro Run;inversion Run;subst.
  match goal with H : eval_expr _ _ _ _ production_ctz_guard ?v |- _ =>
    assert (EV : v=Vint Int.one) by
      (eapply eval_expr_determ;[exact H|apply production_ctz_guard_true]);subst v end.
  match goal with H : bool_val (Vint Int.one) _ _=Some ?b |- _ =>
    change (Some true=Some b) in H;injection H as E;subst b end.
  assumption.
Qed.

Theorem eval_ctz64_requires_external x m t mf result :
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ctz64_var) [Vlong x] t mf result ->
  exists tc mc rc,
    external_functions_sem "__builtin_ctzl" ctz64_signature secp_ge [Vlong x] m tc rc mc.
Proof.
  intro Run;inversion Run;subst.
  match goal with H : function_entry2 secp_ge f_secp256k1_ctz64_var [Vlong x] m ?e ?le ?mi |- _ =>
    destruct (function_entry2_determ secp_ge f_secp256k1_ctz64_var [Vlong x] m
      empty_env (ctz_entry_temps x) m e le mi (ctz_function_entry m x) H) as (EE & EL & EM);
    subst e le mi end.
  match goal with H : exec_stmt _ _ _ _ _ (fn_body f_secp256k1_ctz64_var) _ _ _ _ |- _ =>
    rewrite ctz_body_source in H;
    pose proof (exec_ctz_after_noop _ _ _ _ _ _ _ _ H) as After end.
  rewrite ctz_after_noop_source in After.
  destruct (ctz_sequence_has_head _ _ _ _ _ _ _ _ _ After) as (ti & li & mi & oi & If).
  pose proof (ctz_selected_branch _ _ _ _ _ _ _ If) as Then.
  unfold ctz_then_body in Then.
  destruct (ctz_sequence_has_head _ _ _ _ _ _ _ _ _ Then) as (tc & lc & mc & oc & Call).
  destruct (exec_ctz_builtin_requires_external (ctz_entry_temps x) m tc lc mc oc x eq_refl Call)
    as (rc & External).
  exists tc,mc,rc;exact External.
Qed.
