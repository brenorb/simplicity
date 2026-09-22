(** The actual LSBclear helper for any defined width. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jet_exec C.jet_word_bits C.jet_frame_arith C.jets.
Import Values Mem Ctypes ListNotations Clightdefs Clightdefs.ClightNotations.
Local Open Scope Z_scope.

Definition le_clear_width w n : temp_env :=
  PTree.set _n (Vlong (Int64.repr n)) (PTree.set _x (Vlong w) (PTree.empty val)).

Lemma entry_clear_width m w n :
  function_entry2 ge0 f_LSBclear [Vlong w; Vlong (Int64.repr n)] m
    empty_env (le_clear_width w n) m.
Proof.
  constructor.
  - constructor.
  - repeat constructor; simpl; intuition discriminate.
  - intros id1 id2 H1 H2 Heq; simpl in H1, H2; tauto.
  - constructor.
  - reflexivity.
Qed.

Lemma eval_clear_width m w n : 1 <= n <= 64 ->
  ClightBigstep.Clight2.eval_funcall ge0 m (Internal f_LSBclear)
    [Vlong w; Vlong (Int64.repr n)] E0 m (Vlong (clear_low n w)).
Proof.
  intros Hn.
  assert (HS : Int64.ltu (Int64.repr (n - 1)) Int64.iwordsize = true).
  { unfold Int64.ltu. rewrite cursor_unsigned by lia.
    change ((if zlt (n - 1) 64 then true else false) = true).
    rewrite zlt_true by lia. reflexivity. }
  assert (HN : eval_expr ge0 empty_env (le_clear_width w n) m
      (Ebinop Osub (Etempvar _n tulong) (Econst_int (Int.repr 1) tint) tulong)
      (Vlong (Int64.repr (n - 1)))).
  { eapply eval_Ebinop.
    - eapply eval_Etempvar; reflexivity.
    - apply eval_Econst_int.
    - change (Some (Vlong (Int64.sub (Int64.repr n) (Int64.repr 1))) =
        Some (Vlong (Int64.repr (n - 1)))).
      rewrite cursor_sub by lia. reflexivity. }
  eapply ClightBigstep.eval_funcall_internal
    with (e := empty_env) (le1 := le_clear_width w n) (m1 := m)
      (le2 := le_clear_width w n) (m2 := m)
      (out := Out_return (Some (Vlong (clear_low n w), tulong))).
  - apply entry_clear_width.
  - apply ClightBigstep.exec_Sreturn_some.
    eapply eval_Ecast.
    + eapply eval_Ebinop.
      * eapply eval_Ebinop.
        -- eapply eval_Ebinop.
           ++ eapply eval_Ebinop.
              ** eapply eval_Etempvar; reflexivity.
              ** apply eval_Econst_int.
              ** reflexivity.
           ++ exact HN.
           ++ cbn -[Int64.ltu Int64.shru Int64.repr]. rewrite HS. reflexivity.
        -- apply eval_Econst_int.
        -- reflexivity.
      * exact HN.
      * cbn -[Int64.ltu Int64.shl Int64.repr]. rewrite HS. reflexivity.
    + reflexivity.
  - cbn; split; [discriminate | reflexivity].
  - reflexivity.
Qed.
