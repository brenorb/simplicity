(** Execution of the generated counted loop [for (i = 0; i < c; ++i) body]
    with an invariant over the iterations; the loop body must not modify the
    temporaries. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps Errors.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jets C.jet_exec.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Opaque ge0.
Local Transparent Archi.ptr64.
Set Default Timeout 30.

Lemma core_lt_int a b m : -1000 <= a <= 1000 -> -1000 <= b <= 1000 ->
  sem_binary_operation ge0 Olt (Vint (Int.repr a)) tint (Vint (Int.repr b)) tint m =
  Some (Val.of_bool (if zlt a b then true else false)).
Proof.
  intros Ha Hb. simpl. unfold sem_cmp. simpl. unfold sem_binarith, sem_cast. simpl.
  unfold Int.lt. rewrite !Int.signed_repr by (change Int.min_signed with (-2147483648); change Int.max_signed with 2147483647; lia).
  destruct (zlt a b); reflexivity.
Qed.

Lemma core_add1_int a m :
  sem_binary_operation ge0 Oadd (Vint (Int.repr a)) tint (Vint (Int.repr 1)) tint m =
  Some (Vint (Int.repr (a + 1))).
Proof.
  simpl. unfold sem_add, sem_binarith, sem_cast. simpl.
  f_equal. f_equal. rewrite Int.add_unsigned. apply Int.eqm_samerepr.
  apply Int.eqm_add; apply Int.eqm_sym; apply Int.eqm_unsigned_repr.
Qed.

Definition core_for_loop (cnt : expr) (body : statement) : statement :=
  Ssequence (Sset _i (Econst_int (Int.repr 0) tint))
    (Sloop
      (Ssequence (Sifthenelse (Ebinop Olt (Etempvar _i tint) cnt tint) Sskip Sbreak) body)
      (Sset _i (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint))).

Definition le_at (le : temp_env) (k : Z) : temp_env := PTree.set _i (Vint (Int.repr k)) le.

Lemma exec_for_loop_iter e le cnt body (c : Z) (Q : Z -> mem -> Prop) (Hty : typeof cnt = tint) :
  (forall m' k, 0 <= k <= c -> eval_expr ge0 e (le_at le k) m' cnt (Vint (Int.repr c))) ->
  0 <= c <= 1000 ->
  (forall k m, 0 <= k < c -> Q k m ->
    exists m', Clight2.exec_stmt ge0 e (le_at le k) m body E0 (le_at le k) m' Out_normal /\ Q (k + 1) m') ->
  forall n k m, k + Z.of_nat n = c -> 0 <= k -> Q k m ->
    exists m', Clight2.exec_stmt ge0 e (le_at le k) m
      (Sloop (Ssequence (Sifthenelse (Ebinop Olt (Etempvar _i tint) cnt tint) Sskip Sbreak) body)
        (Sset _i (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint)))
      E0 (le_at le c) m' Out_normal /\ Q c m'.
Proof.
  intros Hcnt Hc Hstep n. induction n as [|n IH]; intros k m Hk Hk0 HQ.
  - assert (kc : k = c) by lia. subst k. exists m. split; [|exact HQ].
    eapply exec_Sloop_stop1 with (out' := Out_break); [|constructor].
    apply exec_Sseq_2; [|discriminate].
    eapply exec_Sifthenelse with (v1 := Vint Int.zero) (b := Datatypes.false).
    + eapply eval_Ebinop with (v1 := Vint (Int.repr c)) (v2 := Vint (Int.repr c)).
      * apply eval_Etempvar. unfold le_at. apply PTree.gss.
      * exact (Hcnt m c ltac:(lia)).
      * change (typeof (Etempvar _i tint)) with tint. rewrite Hty.
        rewrite core_lt_int by lia. rewrite zlt_false by lia. reflexivity.
    + reflexivity.
    + apply exec_Sbreak.
  - destruct (Hstep k m ltac:(lia) HQ) as (m1 & Hbody & HQ1).
    destruct (IH (k + 1) m1 ltac:(lia) ltac:(lia) HQ1) as (m2 & Hrest & HQ2).
    exists m2. split; [|exact HQ2].
    eapply exec_Sloop_loop with (t1 := E0) (t2 := E0) (t3 := E0) (le1 := le_at le k) (m1 := m1) (le2 := le_at le (k + 1)) (m2 := m1).
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m).
      * eapply exec_Sifthenelse with (v1 := Vint Int.one) (b := Datatypes.true).
        -- eapply eval_Ebinop with (v1 := Vint (Int.repr k)) (v2 := Vint (Int.repr c)).
           ++ apply eval_Etempvar. unfold le_at. apply PTree.gss.
           ++ exact (Hcnt m k ltac:(lia)).
           ++ change (typeof (Etempvar _i tint)) with tint. rewrite Hty.
              rewrite core_lt_int by lia. rewrite zlt_true by lia. reflexivity.
        -- reflexivity.
        -- apply exec_Sskip.
      * exact Hbody.
    + constructor.
    + assert (Hl : le_at le (k + 1) = PTree.set _i (Vint (Int.repr (k + 1))) (le_at le k)).
      { unfold le_at. rewrite PTree.set2. reflexivity. }
      rewrite Hl. apply exec_set.
      eapply eval_Ebinop with (v1 := Vint (Int.repr k)) (v2 := Vint (Int.repr 1)).
      * apply eval_Etempvar. unfold le_at. apply PTree.gss.
      * apply eval_Econst_int.
      * apply core_add1_int.
    + exact Hrest.
Qed.

Lemma exec_for_loop e le cnt body (c : Z) (Q : Z -> mem -> Prop) m0 (Hty : typeof cnt = tint) :
  (forall m' k, 0 <= k <= c -> eval_expr ge0 e (le_at le k) m' cnt (Vint (Int.repr c))) ->
  0 <= c <= 1000 -> Q 0 m0 ->
  (forall k m, 0 <= k < c -> Q k m ->
    exists m', Clight2.exec_stmt ge0 e (le_at le k) m body E0 (le_at le k) m' Out_normal /\ Q (k + 1) m') ->
  exists m', Clight2.exec_stmt ge0 e le m0 (core_for_loop cnt body) E0 (le_at le c) m' Out_normal /\ Q c m'.
Proof.
  intros Hcnt Hc HQ Hstep.
  destruct (exec_for_loop_iter e le cnt body c Q Hty Hcnt Hc Hstep (Z.to_nat c) 0 m0
    ltac:(rewrite Z2Nat.id by lia; lia) ltac:(lia) HQ) as (m' & Hloop & HQc).
  exists m'. split; [|exact HQc].
  unfold core_for_loop.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m0) (le1 := le_at le 0).
  - apply exec_set. apply eval_Econst_int.
  - exact Hloop.
Qed.
