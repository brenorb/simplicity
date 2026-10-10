(** Actual predicate entry, retaining its generated undefined flag temporary. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib AST Ctypes Clight ClightBigstep Integers Values Memory Events Maps.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_gej_public_entry.
Import ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition gej_predicate_temps (v_env : val) bd dbase bs sbase : temp_env :=
  PTree.set _env v_env
    (PTree.set _src (Vptr bs (Ptrofs.repr sbase))
      (PTree.set _dst (Vptr bd (Ptrofs.repr dbase))
        (create_undef_temps (fn_temps f_simplicity_gej_is_infinity)))).
Lemma gej_predicate_public_entry v_env m ma mb bl ba bd dbase bs sbase :
  Mem.alloc m 0 16 = (ma,bl) -> Mem.alloc ma 0 128 = (mb,ba) ->
  function_entry2 secp_ge f_simplicity_gej_is_infinity
    [Vptr bd (Ptrofs.repr dbase);Vptr bs (Ptrofs.repr sbase);v_env] m
    (gej_public_env bl ba) (gej_predicate_temps v_env bd dbase bs sbase) mb.
Proof.
  intros HA HB; constructor.
  - cbn; repeat constructor; cbn; intuition discriminate.
  - cbn; repeat constructor; cbn; intuition discriminate.
  - intros x y HX HY HE; cbn in HX, HY.
    repeat match goal with H : _ \/ _ |- _ => destruct H end; subst;
      first [contradiction|vm_compute in HE;discriminate|congruence].
  - eapply alloc_variables_cons with (m1 := ma) (b1 := bl).
    + change (Mem.alloc m 0 16 = (ma,bl)); exact HA.
    + eapply alloc_variables_cons with (m1 := mb) (b1 := ba).
      * change (Mem.alloc ma 0 128 = (mb,ba)); exact HB.
      * constructor.
  - reflexivity.
Qed.
Lemma gej_predicate_src_temp v_env bd dbase bs sbase :
  (gej_predicate_temps v_env bd dbase bs sbase)!_src =
    Some (Vptr bs (Ptrofs.repr sbase)).
Proof.
  unfold gej_predicate_temps; rewrite PTree.gso by discriminate; apply PTree.gss.
Qed.
Lemma gej_predicate_dst_temp v_env bd dbase bs sbase :
  (gej_predicate_temps v_env bd dbase bs sbase)!_dst =
    Some (Vptr bd (Ptrofs.repr dbase)).
Proof.
  unfold gej_predicate_temps; rewrite !PTree.gso by discriminate; apply PTree.gss.
Qed.
Print Assumptions gej_predicate_public_entry.
