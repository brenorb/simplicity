(** Actual LSBkeep execution at any defined word width. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events.
Require Import C.jet_exec C.jet_word_bits C.jet_frame_arith
  C.jet_frame_constants C.jet_LSBclear_width C.jets.
Import Values Mem Ctypes ListNotations Clightdefs Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.

Lemma keep_mask n w : 1 <= n <= 64 ->
  Int64.and w (Int64.shru Int64.mone (Int64.repr (64 - n))) =
  Int64.zero_ext n w.
Proof.
  intros HN. apply Int64.same_bits_eq. intros i HI.
  change (0 <= i < 64) in HI.
  rewrite Int64.bits_and, Int64.bits_shru by exact HI.
  rewrite cursor_unsigned by lia.
  rewrite Int64.bits_zero_ext by lia.
  destruct (zlt i n) as [HL|HG].
  - rewrite zlt_true by (change (i + (64 - n) < 64); lia).
    rewrite Int64.bits_mone by (change (0 <= i + (64 - n) < 64); lia).
    apply andb_true_r.
  - rewrite zlt_false by (change (i + (64 - n) >= 64); lia).
    apply andb_false_r.
Qed.

Lemma eval_keep_width_ge (ge : Clight.genv) m w n : 1 <= n <= 64 ->
  ClightBigstep.Clight2.eval_funcall ge m (Internal f_LSBkeep)
    [Vlong w; Vlong (Int64.repr n)] E0 m (Vlong (Int64.zero_ext n w)).
Proof.
  intros HN. rewrite <- keep_mask by exact HN.
  assert (HS : Int64.ltu (Int64.repr (64 - n)) Int64.iwordsize = true).
  { unfold Int64.ltu. change Int64.iwordsize with (Int64.repr 64).
    rewrite !cursor_unsigned by lia. rewrite zlt_true by lia. reflexivity. }
  eapply ClightBigstep.eval_funcall_internal
    with (e := empty_env) (le1 := le_clear_width w n) (m1 := m)
      (le2 := le_clear_width w n) (m2 := m).
  - constructor.
    + constructor.
    + repeat constructor; simpl; intuition discriminate.
    + intros id1 id2 H1 H2 Heq; simpl in H1, H2; tauto.
    + constructor.
    + reflexivity.
  - apply ClightBigstep.exec_Sreturn_some.
    eapply eval_Ecast.
    + eapply eval_Ebinop.
      * eapply eval_Etempvar; reflexivity.
      * eapply eval_Ebinop.
        -- eapply eval_Ecast.
           ++ eapply eval_Eunop; [apply eval_Econst_int | reflexivity].
           ++ reflexivity.
        -- eapply eval_Ebinop.
           ++ apply eval_generated_uword_bits.
           ++ eapply eval_Etempvar; reflexivity.
           ++ cbn -[Int64.sub Int64.repr Int64.unsigned].
              rewrite cursor_sub by lia. reflexivity.
        -- cbn -[Int64.ltu Int64.shru Int64.repr Z.sub Z.add]. rewrite HS. reflexivity.
      * reflexivity.
    + reflexivity.
  - cbn; split; [discriminate | reflexivity].
  - reflexivity.
Qed.

Lemma eval_keep_width m w n : 1 <= n <= 64 ->
  ClightBigstep.Clight2.eval_funcall ge0 m (Internal f_LSBkeep)
    [Vlong w; Vlong (Int64.repr n)] E0 m (Vlong (Int64.zero_ext n w)).
Proof. apply eval_keep_width_ge. Qed.
