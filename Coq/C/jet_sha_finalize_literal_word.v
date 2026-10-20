(** Constant word wiring used by the literal SHA finalizer.  These are
    equalities of programs in every Core algebra, not SHA arithmetic claims. *)
From Coq Require Import ZArith List.
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word Simplicity.Bit.
Require Import C.jet_canonical_add_adapter.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope term_scope.
Set Default Timeout 10.

Fixpoint sha_haskell_left_shift_list {X n} {term : Alg.Core.Algebra}
    (t : term Ty.Unit X) (amount : Z) : list (term (Vector X n) (Vector X n)) :=
  match n with
  | Datatypes.O => []
  | Datatypes.S k =>
    if Z.even amount then
      eq_rect _ (fun T => list (term T T))
        (sha_haskell_left_shift_list (t &&& t) (amount / 2)) _ (eq_sym VectorPromote)
    else left_shift1 t :: eq_rect _ (fun T => list (term T T))
      (sha_haskell_left_shift_list (t &&& t) ((amount-1) / 2)) _ (eq_sym VectorPromote)
  end.

Definition literal_sha_left_shift64 amount {term : Alg.Core.Algebra} : term (Word 6) (Word 6) :=
  if Z.leb 64 amount then unit >>> @fill Ty.Unit Bit 6 term Bit.false
  else foldr_comp (@sha_haskell_left_shift_list Bit 6 term Bit.false amount).

Lemma literal_sha_left_shift64_matches term amount : In amount [3;6] ->
  @literal_sha_left_shift64 amount term = @Word.shift_const 6 term amount.
Proof.
  intro HIn; cbn in HIn.
  do 2 (destruct HIn as [HEq|HIn]; [subst amount; reflexivity|]); contradiction.
Qed.

Definition literal_sha_add64 {term : Alg.Core.Algebra} :
    term (Ty.Prod (Word 6) (Word 6)) (Word 6) := @canonical_add_word 6 term >>> I H.

Lemma literal_sha_add64_matches term :
  @literal_sha_add64 term = (@Word.adder 6 term >>> I H).
Proof. reflexivity. Qed.
