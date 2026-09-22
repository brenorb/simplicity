(** Actual carry-bit helper calls, without a zero-initialization premise. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import C.jet_exec C.jet_writeBit C.jet_word_bits C.jets.
Import Values Mem ListNotations Clightdefs Clightdefs.ClightNotations.
Local Open Scope Z_scope.

Lemma eval_writeBit_false_word m m1 m2 bf bw w :
  Mem.load Mptr m bf 0 = Some (Vptr bw Ptrofs.zero) ->
  Mem.load Mint64 m bf 8 = Some (Vlong (Int64.repr 9)) ->
  Mem.load Mint64 m bw 0 = Some (Vlong w) ->
  Mem.store Mint64 m bf 8 (Vlong (Int64.repr 8)) = Some m1 ->
  Mem.store Mint64 m1 bw 0 (Vlong (clear_low 9 w)) = Some m2 ->
  bf <> bw ->
  ClightBigstep.Clight2.eval_funcall ge0 m (Internal f_writeBit)
    [Vptr bf Ptrofs.zero; Vint Int.zero] E0 m2 (Vint Int.zero).
Proof.
  intros HE HO HW SO SW Hneq.
  eapply ClightBigstep.eval_funcall_internal
    with (e := empty_env) (le1 := le_writeBit0 bf) (m1 := m)
      (le2 := le_writeBit_t1 w (clear_low 9 w) bf bw) (m2 := m2)
      (out := Out_return (Some (Vint Int.zero, tbool))) (vres := Vint Int.zero).
  - apply entry_writeBit0.
  - eapply eval_writeBit_zero.
    + exact HE.
    + exact HO.
    + exact SO.
    + rewrite <- HE. eapply Mem.load_store_other;
        [exact SO | right; left; change (0 + 8 <= 8); lia].
    + exact (Mem.load_store_same _ _ _ _ _ _ SO).
    + rewrite <- HW. eapply Mem.load_store_other; [exact SO | auto].
    + exact SW.
    + apply symbol_LSBclear.
    + apply funct_LSBclear.
    + apply eval_LSBclear9_word.
  - cbn; split; [discriminate | reflexivity].
  - reflexivity.
Qed.

Lemma eval_writeBit_true_word m m1 m2 bf bw w :
  Mem.load Mptr m bf 0 = Some (Vptr bw Ptrofs.zero) ->
  Mem.load Mint64 m bf 8 = Some (Vlong (Int64.repr 9)) ->
  Mem.load Mint64 m bw 0 = Some (Vlong w) ->
  Mem.store Mint64 m bf 8 (Vlong (Int64.repr 8)) = Some m1 ->
  Mem.store Mint64 m1 bw 0 (Vlong (Int64.or w (Int64.repr 256))) = Some m2 ->
  bf <> bw ->
  ClightBigstep.Clight2.eval_funcall ge0 m (Internal f_writeBit)
    [Vptr bf Ptrofs.zero; Vint Int.one] E0 m2 (Vint Int.one).
Proof.
  intros HE HO HW SO SW Hneq.
  eapply ClightBigstep.eval_funcall_internal
    with (e := empty_env) (le1 := le_writeBit1 bf) (m1 := m)
      (le2 := le_writeBit1_t5 w bf bw) (m2 := m2)
      (out := Out_return (Some (Vint Int.one, tbool))) (vres := Vint Int.one).
  - apply entry_writeBit1.
  - eapply eval_writeBit_one.
    + exact HE.
    + exact HO.
    + exact SO.
    + rewrite <- HE. eapply Mem.load_store_other;
        [exact SO | right; left; change (0 + 8 <= 8); lia].
    + exact (Mem.load_store_same _ _ _ _ _ _ SO).
    + rewrite <- HW. eapply Mem.load_store_other; [exact SO | auto].
    + exact SW.
  - cbn; split; [discriminate | reflexivity].
  - reflexivity.
Qed.
