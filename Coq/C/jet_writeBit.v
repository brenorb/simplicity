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

Definition le_writeBit0 (bf : block) : temp_env :=
  PTree.set _bit (Vint Int.zero)
    (PTree.set _frame (Vptr bf Ptrofs.zero)
      (create_undef_temps f_writeBit.(fn_temps))).

Lemma entry_writeBit0 : forall (m : mem) (bf : block),
  function_entry2 ge0 f_writeBit
    (Vptr bf Ptrofs.zero :: Vint Int.zero :: nil) m
    empty_env (le_writeBit0 bf) m.
Proof.
  intros m bf.
  constructor.
  - constructor.
  - constructor.
    + simpl; intro H; destruct H as [H | H].
      * vm_compute in H; congruence.
      * contradiction.
    + constructor.
      * simpl; intro H; contradiction.
      * constructor.
  - intros id1 id2 H1 H2 Heq.
    simpl in H1, H2.
    subst id2.
    repeat match goal with
    | H : _ \/ _ |- _ => destruct H
    end.
    all: vm_compute in *; congruence.
  - constructor.
  - reflexivity.
Qed.

Definition le_writeBit_offset (bf : block) : temp_env :=
  PTree.set _t'8 (Vlong (Int64.repr 9)) (le_writeBit0 bf).

Definition le_writeBit_edge (bf bw : block) : temp_env :=
  PTree.set _t'6 (Vptr bw Ptrofs.zero) (le_writeBit_offset bf).

Definition le_writeBit_t7 (bf bw : block) : temp_env :=
  PTree.set _t'7 (Vlong (Int64.repr 8)) (le_writeBit_edge bf bw).

Definition le_writeBit_ptr (bf bw : block) : temp_env :=
  PTree.set _dst_ptr (Vptr bw Ptrofs.zero) (le_writeBit_t7 bf bw).

Definition le_writeBit_t2 (bf bw : block) : temp_env :=
  PTree.set _t'2 (Vlong Int64.zero) (le_writeBit_ptr bf bw).

Definition le_writeBit_t3 (bf bw : block) : temp_env :=
  PTree.set _t'3 (Vlong (Int64.repr 8)) (le_writeBit_t2 bf bw).

Definition le_writeBit_t1 (bf bw : block) : temp_env :=
  PTree.set _t'1 (Vlong Int64.zero) (le_writeBit_t3 bf bw).

Definition le_LSBclear9 (w : int64) : temp_env :=
  PTree.set _n (Vlong (Int64.repr 9))
    (PTree.set _x (Vlong w) (PTree.empty val)).

Lemma entry_LSBclear9_value : forall (m : mem) (w : int64),
  function_entry2 ge0 f_LSBclear
    (Vlong w :: Vlong (Int64.repr 9) :: nil) m
    empty_env (le_LSBclear9 w) m.
Proof.
  intros m w.
  constructor.
  - constructor.
  - constructor.
    + simpl; intro H; destruct H as [H | H].
      * vm_compute in H; congruence.
      * contradiction.
    + constructor.
      * simpl; intro H; contradiction.
      * constructor.
  - intros id1 id2 H1 H2 Heq; simpl in H1, H2; tauto.
  - constructor.
  - reflexivity.
Qed.

Lemma eval_LSBclear9_n_minus_one : forall (m : mem) (w : int64),
  eval_expr ge0 empty_env (le_LSBclear9 w) m
    (Ebinop Osub (Etempvar _n tulong)
      (Econst_int (Int.repr 1) tint) tulong)
    (Vlong (Int64.repr 8)).
Proof.
  intros m w.
  eapply eval_Ebinop.
  - eapply eval_Etempvar.
    simpl [le_LSBclear9]. reflexivity.
  - apply eval_Econst_int.
  - cbn; vm_compute; reflexivity.
Qed.

Ltac eval_LSBclear9_value :=
  first [ eapply eval_Ecast; [ eval_LSBclear9_value | cbn; reflexivity ]
        | eapply eval_Ebinop;
            [ eval_LSBclear9_value | eval_LSBclear9_value | cbn; reflexivity ]
        | eapply eval_Etempvar; simpl [le_LSBclear9]; reflexivity
        | (cbn; vm_compute; reflexivity) ].

Lemma eval_LSBclear9_zero : forall (m : mem),
  ClightBigstep.Clight2.eval_funcall ge0 m (Internal f_LSBclear)
    (Vlong Int64.zero :: Vlong (Int64.repr 9) :: nil) E0 m
    (Vlong Int64.zero).
Proof.
  intros m.
  eapply ClightBigstep.eval_funcall_internal
    with (e := empty_env) (le1 := le_LSBclear9 Int64.zero) (m1 := m)
         (le2 := le_LSBclear9 Int64.zero) (m2 := m).
  - apply entry_LSBclear9_value.
  - simpl [f_LSBclear].
    apply ClightBigstep.exec_Sreturn_some.
    pose proof (eval_LSBclear9_n_minus_one m Int64.zero) as Hn.
    eapply eval_Ecast.
    + eapply eval_Ebinop.
      * eapply eval_Ebinop.
        -- eapply eval_Ebinop.
           ++ eapply eval_Ebinop.
              --- eapply eval_Etempvar.
                  simpl [le_LSBclear9]. reflexivity.
              --- apply eval_Econst_int.
              --- cbn; reflexivity.
           ++ exact Hn.
           ++ cbn; reflexivity.
      -- apply eval_Econst_int.
      -- cbn; reflexivity.
      * exact Hn.
      * cbn; reflexivity.
    + cbn; reflexivity.
  - cbn; split; [discriminate | reflexivity].
  - simpl; reflexivity.
Qed.
