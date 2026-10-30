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

Require Import C.jet_secp_ctz_external_call C.jet_ctz_model C.jet_transport C.extraMath
 C.jet_elements_taptweak_program C.jet_elements_taptweak_pure C.jet_elements_taptweak_globals.
Require Import String.
Lemma elements_taptweak_ctz_builtin_linked:exists b,
 Genv.find_symbol elements_taptweak_ge ___builtin_ctzl=Some b /\
 Genv.find_funct_ptr elements_taptweak_ge b=Some
 (External(EF_builtin "__builtin_ctzl" ctz64_signature)(Tcons tulong Tnil)tint cc_default).
Proof. exists(elements_taptweak_symbol_block ___builtin_ctzl);split;vm_compute;reflexivity. Qed.
Lemma elements_taptweak_ctz_guard_checked:
 expr_okb secp_ge elements_taptweak_ge production_ctz_guard=true.
Proof. vm_compute;reflexivity. Qed.
Local Opaque secp_ge elements_taptweak_ge.
Lemma elements_taptweak_ctz_guard_true e le m:
 eval_expr elements_taptweak_ge e le m production_ctz_guard(Vint Int.one).
Proof.
 apply(proj1(eval_expr_transport secp_ge elements_taptweak_ge e le m));
 [apply production_ctz_guard_true|exact elements_taptweak_ctz_guard_checked].
Qed.
Lemma elements_taptweak_ctz_function_entry m x :
  function_entry2 elements_taptweak_ge f_secp256k1_ctz64_var [Vlong x] m empty_env (ctz_entry_temps x) m.
Proof.
  assert (OK : fn_okb f_secp256k1_ctz64_var=true) by reflexivity.
  destruct (fn_okb_true _ OK) as (HN1 & HN2 & HD).
  constructor;[exact HN1|exact HN2|exact HD|constructor|reflexivity].
Qed.

Lemma elements_taptweak_ctz_argument_eval e le m x : le!_x=Some (Vlong x) ->
  eval_exprlist elements_taptweak_ge e le m [Ecast (Etempvar _x tulong) tulong] (Tcons tulong Tnil) [Vlong x].
Proof.
  intro HX;eapply eval_Econs.
  - eapply eval_Ecast;[apply eval_Etempvar;exact HX|reflexivity].
  - reflexivity.
  - constructor.
Qed.

Lemma elements_taptweak_exec_ctz_builtin_from_external le m mf x n : le!_x=Some (Vlong x) ->
  external_functions_sem "__builtin_ctzl" ctz64_signature elements_taptweak_ge [Vlong x] m E0 (Vint n) mf ->
  Clight2.exec_stmt elements_taptweak_ge empty_env le m ctz_builtin_call E0
    (PTree.set _t'1 (Vint n) le) mf Out_normal.
Proof.
  intros HX Ext;destruct elements_taptweak_ctz_builtin_linked as (bf & HS & HF).
  unfold ctz_builtin_call;eapply exec_Scall with (vf:=Vptr bf Ptrofs.zero)
    (vargs:=[Vlong x])
    (f:=External (EF_builtin "__builtin_ctzl" ctz64_signature) (Tcons tulong Tnil) tint cc_default)
    (vres:=Vint n).
  - reflexivity.
  - eapply eval_Elvalue;[eapply eval_Evar_global;[reflexivity|exact HS]|apply deref_loc_reference;reflexivity].
  - apply elements_taptweak_ctz_argument_eval;exact HX.
  - exact HF.
  - reflexivity.
  - apply eval_funcall_external.
    change (builtin_or_external_sem "__builtin_ctzl" ctz64_signature elements_taptweak_ge [Vlong x] m E0 (Vint n) mf).
    rewrite production_ctzl_is_abstract_external;exact Ext.
Qed.

Theorem elements_taptweak_eval_ctz64_from_external x n m mf :
  external_functions_sem "__builtin_ctzl" ctz64_signature elements_taptweak_ge [Vlong x] m E0 (Vint n) mf ->
  Clight2.eval_funcall elements_taptweak_ge m (Internal f_secp256k1_ctz64_var) [Vlong x] E0 mf (Vint n).
Proof.
  intro Ext.
  eapply eval_funcall_internal with (e:=empty_env) (le1:=ctz_entry_temps x)
    (le2:=PTree.set _t'1 (Vint n) (ctz_entry_temps x)) (m1:=m) (m2:=mf)
    (out:=Out_return (Some (Vint n,tint))).
  - apply elements_taptweak_ctz_function_entry.
  - rewrite ctz_body_source;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=ctz_entry_temps x).
    + eapply exec_Sloop_stop2 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=ctz_entry_temps x)
        (out1:=Out_normal) (out2:=Out_break);constructor.
    + rewrite ctz_after_noop_source;eapply exec_Sseq_2;[|discriminate].
      eapply exec_Sifthenelse with (v1:=Vint Int.one) (b:=true).
      * apply elements_taptweak_ctz_guard_true.
      * reflexivity.
      * unfold ctz_then_body;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mf)
          (le1:=PTree.set _t'1 (Vint n) (ctz_entry_temps x)).
        -- eapply elements_taptweak_exec_ctz_builtin_from_external;[reflexivity|exact Ext].
        -- apply exec_Sreturn_some;apply eval_Etempvar;apply PTree.gss.
  - split;[discriminate|reflexivity].
  - reflexivity.
Qed.

Theorem eval_elements_taptweak_ctz64(Model:ctz_model)m x:
 Int64.unsigned x<>0 ->
 Clight2.eval_funcall elements_taptweak_ge m(Internal f_secp256k1_ctz64_var)[Vlong x]E0 m
 (Vint(Int.repr(Z_ctz(Int64.unsigned x)))).
Proof. intro Nonzero;apply elements_taptweak_eval_ctz64_from_external;exact(Model _ m x Nonzero). Qed.
