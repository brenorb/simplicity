(** Complete generated write8 call for an arbitrary initialized backing word. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import C.jet_exec C.jet_write8 C.jet_word_bits C.jets.
Import Values Mem ListNotations.
Local Open Scope Z_scope.

Lemma eval_write8_put m mw mf bd bw old x :
  Mem.load Mptr m bd 0 = Some (Vptr bw Ptrofs.zero) ->
  Mem.load Mint64 m bd 8 = Some (Vlong (Int64.repr 8)) ->
  Mem.load Mint64 m bw 0 = Some (Vlong old) ->
  Mem.store Mint64 m bw 0
    (Vlong (put_low 8 old (Int64.repr (Int.unsigned x)))) = Some mw ->
  Mem.store Mint64 mw bd 8 (Vlong Int64.zero) = Some mf ->
  bd <> bw ->
  ClightBigstep.Clight2.eval_funcall ge0 m (Internal f_simplicity_write8)
    [Vptr bd Ptrofs.zero; Vint x] E0 mf Vundef.
Proof.
  intros HE HO HW SW SF Hneq.
  eapply eval_write8_x with (w := old) (c := clear_low 8 old)
    (k := Int64.zero_ext 8 (Int64.repr (Int.unsigned x))) (m1 := mw).
  - exact HE.
  - exact HO.
  - exact HW.
  - exact SW.
  - rewrite <- HO. eapply Mem.load_store_other; [exact SW | auto].
  - exact SF.
  - change (put_low 8 old (Int64.repr (Int.unsigned x)) =
      Int64.or (clear_low 8 old)
        (Int64.shl (Int64.zero_ext 8 (Int64.repr (Int.unsigned x))) Int64.zero)).
    rewrite Int64.shl_zero. reflexivity.
  - apply symbol_LSBclear.
  - apply funct_LSBclear.
  - apply symbol_LSBkeep.
  - apply funct_LSBkeep.
  - apply eval_LSBclear8_value.
  - rewrite Int64.zero_ext_and by lia. apply eval_LSBkeep8_value.
Qed.
