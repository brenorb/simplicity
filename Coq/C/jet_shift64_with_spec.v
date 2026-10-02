(** Literal fill-input canonical 64-bit shifts. The complement normal form is
    a bridge for the C helper's two XOR toggles, not a substituted spec. *)
From Coq Require Import ZArith List Lia Bool.
Require Import Simplicity.Word Simplicity.Bit.
Require Import C.jet_shift_spec C.jet_shift64_spec C.jet_complement_spec C.jet_shift8_with_spec.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition shift64_with_spec right {term : Alg.Core.Algebra} := @shift_with_word_spec 3 6 right term.

Lemma shift64_with_spec_parametric right : Alg.Core.Parametric (@shift64_with_spec right).
Proof. apply shift_with_word_spec_parametric. Qed.

Lemma shift64_with_complement_one_right amount (x : Ty.tySem (Word 6)) :
  @shift64_with_spec Datatypes.true Alg.CoreFunSem (Bit.fromBool Datatypes.true,(amount,x)) =
    if Datatypes.true then @complement_spec 6 Alg.CoreFunSem
      (@shift64_plain_spec Datatypes.true Alg.CoreFunSem (amount, @complement_spec 6 Alg.CoreFunSem x))
    else @shift64_plain_spec Datatypes.true Alg.CoreFunSem (amount,x).
Proof.
  destruct x as [[[[[[x0 x1] [x2 x3]] [[x4 x5] [x6 x7]]] [[[x8 x9] [x10 x11]] [[x12 x13] [x14 x15]]]] [[[[x16 x17] [x18 x19]] [[x20 x21] [x22 x23]]] [[[x24 x25] [x26 x27]] [[x28 x29] [x30 x31]]]]] [[[[[x32 x33] [x34 x35]] [[x36 x37] [x38 x39]]] [[[x40 x41] [x42 x43]] [[x44 x45] [x46 x47]]]] [[[[x48 x49] [x50 x51]] [[x52 x53] [x54 x55]]] [[[x56 x57] [x58 x59]] [[x60 x61] [x62 x63]]]]]].
  destruct amount as [[[a b] [c d]] [[e f] [g h]]];
    destruct a as [[]|[]], b as [[]|[]], c as [[]|[]], d as [[]|[]],
      e as [[]|[]], f as [[]|[]], g as [[]|[]], h as [[]|[]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
Qed.

Lemma shift64_with_complement_one_left amount (x : Ty.tySem (Word 6)) :
  @shift64_with_spec Datatypes.false Alg.CoreFunSem (Bit.fromBool Datatypes.true,(amount,x)) =
    if Datatypes.true then @complement_spec 6 Alg.CoreFunSem
      (@shift64_plain_spec Datatypes.false Alg.CoreFunSem (amount, @complement_spec 6 Alg.CoreFunSem x))
    else @shift64_plain_spec Datatypes.false Alg.CoreFunSem (amount,x).
Proof.
  destruct x as [[[[[[x0 x1] [x2 x3]] [[x4 x5] [x6 x7]]] [[[x8 x9] [x10 x11]] [[x12 x13] [x14 x15]]]] [[[[x16 x17] [x18 x19]] [[x20 x21] [x22 x23]]] [[[x24 x25] [x26 x27]] [[x28 x29] [x30 x31]]]]] [[[[[x32 x33] [x34 x35]] [[x36 x37] [x38 x39]]] [[[x40 x41] [x42 x43]] [[x44 x45] [x46 x47]]]] [[[[x48 x49] [x50 x51]] [[x52 x53] [x54 x55]]] [[[x56 x57] [x58 x59]] [[x60 x61] [x62 x63]]]]]].
  destruct amount as [[[a b] [c d]] [[e f] [g h]]];
    destruct a as [[]|[]], b as [[]|[]], c as [[]|[]], d as [[]|[]],
      e as [[]|[]], f as [[]|[]], g as [[]|[]], h as [[]|[]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
Qed.

Lemma shift64_with_complement_zero_right amount (x : Ty.tySem (Word 6)) :
  @shift64_with_spec Datatypes.true Alg.CoreFunSem (Bit.fromBool Datatypes.false,(amount,x)) =
    if Datatypes.false then @complement_spec 6 Alg.CoreFunSem
      (@shift64_plain_spec Datatypes.true Alg.CoreFunSem (amount, @complement_spec 6 Alg.CoreFunSem x))
    else @shift64_plain_spec Datatypes.true Alg.CoreFunSem (amount,x).
Proof.
  destruct x as [[[[[[x0 x1] [x2 x3]] [[x4 x5] [x6 x7]]] [[[x8 x9] [x10 x11]] [[x12 x13] [x14 x15]]]] [[[[x16 x17] [x18 x19]] [[x20 x21] [x22 x23]]] [[[x24 x25] [x26 x27]] [[x28 x29] [x30 x31]]]]] [[[[[x32 x33] [x34 x35]] [[x36 x37] [x38 x39]]] [[[x40 x41] [x42 x43]] [[x44 x45] [x46 x47]]]] [[[[x48 x49] [x50 x51]] [[x52 x53] [x54 x55]]] [[[x56 x57] [x58 x59]] [[x60 x61] [x62 x63]]]]]].
  destruct amount as [[[a b] [c d]] [[e f] [g h]]];
    destruct a as [[]|[]], b as [[]|[]], c as [[]|[]], d as [[]|[]],
      e as [[]|[]], f as [[]|[]], g as [[]|[]], h as [[]|[]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
Qed.

Lemma shift64_with_complement_zero_left amount (x : Ty.tySem (Word 6)) :
  @shift64_with_spec Datatypes.false Alg.CoreFunSem (Bit.fromBool Datatypes.false,(amount,x)) =
    if Datatypes.false then @complement_spec 6 Alg.CoreFunSem
      (@shift64_plain_spec Datatypes.false Alg.CoreFunSem (amount, @complement_spec 6 Alg.CoreFunSem x))
    else @shift64_plain_spec Datatypes.false Alg.CoreFunSem (amount,x).
Proof.
  destruct x as [[[[[[x0 x1] [x2 x3]] [[x4 x5] [x6 x7]]] [[[x8 x9] [x10 x11]] [[x12 x13] [x14 x15]]]] [[[[x16 x17] [x18 x19]] [[x20 x21] [x22 x23]]] [[[x24 x25] [x26 x27]] [[x28 x29] [x30 x31]]]]] [[[[[x32 x33] [x34 x35]] [[x36 x37] [x38 x39]]] [[[x40 x41] [x42 x43]] [[x44 x45] [x46 x47]]]] [[[[x48 x49] [x50 x51]] [[x52 x53] [x54 x55]]] [[[x56 x57] [x58 x59]] [[x60 x61] [x62 x63]]]]]].
  destruct amount as [[[a b] [c d]] [[e f] [g h]]];
    destruct a as [[]|[]], b as [[]|[]], c as [[]|[]], d as [[]|[]],
      e as [[]|[]], f as [[]|[]], g as [[]|[]], h as [[]|[]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
  1-4: lazy; solve [repeat first [reflexivity | solve [symmetry; apply bit_flip_twice] | apply f_equal2]].
Qed.

Lemma shift64_with_complement_normalform right fill amount (x : Ty.tySem (Word 6)) :
  @shift64_with_spec right Alg.CoreFunSem (Bit.fromBool fill,(amount,x)) =
    if fill then @complement_spec 6 Alg.CoreFunSem
      (@shift64_plain_spec right Alg.CoreFunSem (amount, @complement_spec 6 Alg.CoreFunSem x))
    else @shift64_plain_spec right Alg.CoreFunSem (amount,x).
Proof.
  destruct fill, right.
  - apply shift64_with_complement_one_right.
  - apply shift64_with_complement_one_left.
  - apply shift64_with_complement_zero_right.
  - apply shift64_with_complement_zero_left.
Qed.
