(** Literal fill-input canonical 32-bit shifts. The complement normal form is
    a bridge for the C helper's two XOR toggles, not a substituted spec. *)
From Coq Require Import ZArith List Lia Bool.
Require Import Simplicity.Word Simplicity.Bit.
Require Import C.jet_shift_spec C.jet_shift32_spec C.jet_complement_spec C.jet_shift8_with_spec.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition shift32_with_spec right {term : Alg.Core.Algebra} := @shift_with_word_spec 3 5 right term.

Lemma shift32_with_spec_parametric right : Alg.Core.Parametric (@shift32_with_spec right).
Proof. apply shift_with_word_spec_parametric. Qed.

Lemma shift32_with_complement_normalform right fill amount (x : Ty.tySem (Word 5)) :
  @shift32_with_spec right Alg.CoreFunSem (Bit.fromBool fill,(amount,x)) =
    if fill then @complement_spec 5 Alg.CoreFunSem
      (@shift32_plain_spec right Alg.CoreFunSem (amount, @complement_spec 5 Alg.CoreFunSem x))
    else @shift32_plain_spec right Alg.CoreFunSem (amount,x).
Proof.
  destruct x as [[[[[x0 x1] [x2 x3]] [[x4 x5] [x6 x7]]] [[[x8 x9] [x10 x11]] [[x12 x13] [x14 x15]]]] [[[[x16 x17] [x18 x19]] [[x20 x21] [x22 x23]]] [[[x24 x25] [x26 x27]] [[x28 x29] [x30 x31]]]]].
  destruct fill, right; destruct amount as [[[a b] [c d]] [[e f] [g h]]];
    destruct a as [[]|[]], b as [[]|[]], c as [[]|[]], d as [[]|[]],
      e as [[]|[]], f as [[]|[]], g as [[]|[]], h as [[]|[]].
  (* Each command stays within the default tactic timeout. Only control/fill
     bits are split; all payload bits remain symbolic. *)
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-8: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  (* Kernel checking this finite control proof can exceed the 10-second tactic
     budget during a parallel rebuild. Keep tactic limits unchanged and bound Qed separately. *)
  Set Default Timeout 30.
Time Qed.
Set Default Timeout 10.
