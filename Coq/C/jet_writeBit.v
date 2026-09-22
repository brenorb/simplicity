(** Direct Clight execution lemmas for [f_writeBit]. *)

From Coq Require Import ZArith List PArith.BinPos.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.

Require Import C.jet_exec.
Require Import jets.

Import Clightdefs Clightdefs.ClightNotations.
Import Values Mem Ctypes.
Import Events.

Local Open Scope Z_scope.
Local Open Scope clight_scope.

Lemma exec_writeBit_debug_loop : forall (ge : genv) (e : env)
    (le : temp_env) (m : mem),
  ClightBigstep.Clight2.exec_stmt ge e le m
    (Sloop
      (Sifthenelse
        (Eunop Onotbool (Econst_int (Int.repr 0) tint) tint)
        Sskip Sskip)
      Sbreak)
    E0 le m Out_normal.
Proof.
  intros ge e le m.
  eapply ClightBigstep.exec_Sloop_stop2
    with (t1 := E0) (le1 := le) (m1 := m) (out1 := Out_normal)
         (t2 := E0) (le2 := le) (m2 := m) (out2 := Out_break).
  - eapply ClightBigstep.exec_Sifthenelse
      with (v1 := Vint Int.one) (b := true).
    + eapply eval_Eunop.
      * apply eval_Econst_int.
      * cbn; reflexivity.
    + reflexivity.
    + apply ClightBigstep.exec_Sskip.
  - constructor.
  - apply ClightBigstep.exec_Sbreak.
  - constructor.
Qed.
