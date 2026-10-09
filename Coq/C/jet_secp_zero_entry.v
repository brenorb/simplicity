(** Original predicate entry: same declarations, different actual C body. *)
From Coq Require Import ZArith.
From compcert Require Import AST Clight Memory Values ClightBigstep.
Require Import C.jets_secp C.jet_secp_linkage.
Require Import C.jet_secp_predicate_entry C.jet_secp_public_copy.
Local Open Scope Z_scope.
Set Default Timeout 10.
Lemma function_entry2_same_declarations ge f g args m e le mf :
  fn_vars f = fn_vars g -> fn_params f = fn_params g -> fn_temps f = fn_temps g ->
  function_entry2 ge f args m e le mf -> function_entry2 ge g args m e le mf.
Proof.
  intros HVars HParams HTemps HEntry; inversion HEntry; subst.
  constructor; rewrite <- ?HVars, <- ?HParams, <- ?HTemps; assumption.
Qed.
Lemma secp_fe_zero_entry v_env m ma mb bl ba bd dbase bs sbase :
  Mem.alloc m 0 16 = (ma, bl) -> Mem.alloc ma 0 40 = (mb, ba) ->
  function_entry2 secp_ge f_simplicity_fe_is_zero
    (Vptr bd (Integers.Ptrofs.repr dbase) :: Vptr bs (Integers.Ptrofs.repr sbase) :: v_env :: nil) m
    (secp_public_env bl ba) (secp_odd_temps v_env bd dbase bs sbase) mb.
Proof.
  intros HA HB.
  eapply function_entry2_same_declarations with (f := f_simplicity_fe_is_odd).
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - eapply secp_fe_odd_entry; eassumption.
Qed.
