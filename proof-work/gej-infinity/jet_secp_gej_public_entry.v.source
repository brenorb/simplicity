(** Actual public point-infinity entry: a frame local and one point local. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib AST Ctypes Clight ClightBigstep Integers Values Memory Events Maps.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_public_copy.
Import ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition gej_public_env (bl ba : block) : env :=
  PTree.set _a (ba, Tstruct __6123 noattr)
    (PTree.set _src (bl, Tstruct _frameItem noattr) empty_env).

Lemma gej_infinity_public_entry v_env m ma mb bl ba bd dbase bs sbase :
  Mem.alloc m 0 16 = (ma, bl) -> Mem.alloc ma 0 128 = (mb, ba) ->
  function_entry2 secp_ge f_simplicity_gej_infinity
    [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); v_env] m
    (gej_public_env bl ba) (secp_public_temps v_env bd dbase bs sbase) mb.
Proof.
  intros HA HB; constructor.
  - cbn; repeat constructor; cbn; intuition discriminate.
  - cbn; repeat constructor; cbn; intuition discriminate.
  - intros x y HX HY Hxy; cbn in HX, HY.
    repeat match goal with H : _ \/ _ |- _ => destruct H end; subst;
      first [contradiction|vm_compute in Hxy; discriminate|congruence].
  - eapply alloc_variables_cons with (m1 := ma) (b1 := bl).
    + change (Mem.alloc m 0 16 = (ma, bl)); exact HA.
    + eapply alloc_variables_cons with (m1 := mb) (b1 := ba).
      * change (Mem.alloc ma 0 128 = (mb, ba)); exact HB.
      * constructor.
  - reflexivity.
Qed.
Print Assumptions gej_infinity_public_entry.
