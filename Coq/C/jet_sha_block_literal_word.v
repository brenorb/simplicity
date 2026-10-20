(** Literal Haskell constant-wiring generators at the SHA specializations.
    These are program equalities in every Core algebra, not numerical
    assertions that the abstract SHA specifications are correct. *)
From Coq Require Import ZArith List.
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word Simplicity.Bit.
Require Simplicity.SHA256.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope ty_scope.
Local Open Scope term_scope.
Set Default Timeout 10.

(** Programs.Word.rotate_const's go: even, 1 mod 4, or 3 mod 4.
    The casts only express Haskell's vectorPromote type equality. *)
Fixpoint sha_haskell_rotate_list {X n} {term : Alg.Core.Algebra} (z : Z) :
  list (term (Vector X n) (Vector X n)) :=
match n with
| 0%nat => []
| S k =>
  if Z.even z then
    eq_rect _ (fun T => list (term T T)) (sha_haskell_rotate_list (Z.div z 2)) _ (eq_sym VectorPromote)
  else if Z.eqb (z mod 4) 1 then
    left_rotate1 :: eq_rect _ (fun T => list (term T T))
      (sha_haskell_rotate_list (Z.div (z-1) 2)) _ (eq_sym VectorPromote)
  else if Z.eqb (z mod 4) 3 then
    right_rotate1 :: eq_rect _ (fun T => list (term T T))
      (sha_haskell_rotate_list (Z.div (z+1) 2)) _ (eq_sym VectorPromote)
  else []
end.

Definition literal_sha_rotate32 z {term : Alg.Core.Algebra} : term Word32 Word32 :=
  foldr_comp (@sha_haskell_rotate_list Bit 5 term z).

(** The nonnegative go branch of right_shift_const_by.  The SHA shifts
    enter it with the positive magnitudes 3 and 10. *)
Fixpoint sha_haskell_right_shift_list {X n} {term : Alg.Core.Algebra}
    (t : term Ty.Unit X) (amount : Z) : list (term (Vector X n) (Vector X n)) :=
match n with
| 0%nat => []
| S k =>
  if Z.even amount then
    eq_rect _ (fun T => list (term T T))
      (sha_haskell_right_shift_list (t &&& t) (amount / 2)) _ (eq_sym VectorPromote)
  else right_shift1 t :: eq_rect _ (fun T => list (term T T))
    (sha_haskell_right_shift_list (t &&& t) ((amount-1) / 2)) _ (eq_sym VectorPromote)
end.

Definition literal_sha_right_shift32 amount {term : Alg.Core.Algebra} : term Word32 Word32 :=
  if Z.leb 32 amount then unit >>> @fill Ty.Unit Bit 5 term Bit.false
  else foldr_comp (@sha_haskell_right_shift_list Bit 5 term Bit.false amount).

Lemma literal_sha_rotate32_matches term z :
  In z [-7;-18;-17;-19;-2;-13;-22;-6;-11;-25] ->
  @literal_sha_rotate32 z term = @SHA256.rotate32 z term.
Proof.
  intro HIn; cbn in HIn.
  do 10 (destruct HIn as [HEq|HIn]; [subst z; reflexivity|]); contradiction.
Qed.

Lemma literal_sha_right_shift32_matches term amount : In amount [3;10] ->
  @literal_sha_right_shift32 amount term = @SHA256.shift32 (-amount) term.
Proof.
  intro HIn; cbn in HIn.
  do 2 (destruct HIn as [HEq|HIn]; [subst amount; reflexivity|]); contradiction.
Qed.
