(** Value-preserving substitution for scalar executor expressions.
    The special 32-bit slot represents the actual unsigned overflow argument. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Zbits Integers AST Ctypes Values.
Require Import C.jet_sx_expr.
Set Default Timeout 10.

Fixpoint scalar_bind (sigma : nat -> sx) (flag : sx) (x : sx) : sx :=
  match x with
  | XLv n => sigma n
  | XIb o a b => XIb o (scalar_bind sigma flag a) (scalar_bind sigma flag b)
  | XLb o a b => XLb o (scalar_bind sigma flag a) (scalar_bind sigma flag b)
  | XIsh o a k => XIsh o (scalar_bind sigma flag a) k
  | XLsh o a k => XLsh o (scalar_bind sigma flag a) k
  | XIcmp c sg a b => XIcmp c sg (scalar_bind sigma flag a) (scalar_bind sigma flag b)
  | XLcmp c sg a b => XLcmp c sg (scalar_bind sigma flag a) (scalar_bind sigma flag b)
  | XI2L sg a => XI2L sg (scalar_bind sigma flag a)
  | XL2I a => match a with
      | XLv n => if Nat.eqb n 4 then flag else XL2I (sigma n)
      | _ => XL2I (scalar_bind sigma flag a)
      end
  | XIcast sz sg a => XIcast sz sg (scalar_bind sigma flag a)
  | XInz a => XInz (scalar_bind sigma flag a)
  | XLnz a => XLnz (scalar_bind sigma flag a)
  | XIz a => XIz (scalar_bind sigma flag a)
  | XLz a => XLz (scalar_bind sigma flag a)
  | XIneg a => XIneg (scalar_bind sigma flag a)
  | XLneg a => XLneg (scalar_bind sigma flag a)
  | XInot a => XInot (scalar_bind sigma flag a)
  | XLnot a => XLnot (scalar_bind sigma flag a)
  | _ => x
  end.

Lemma scalar_bind_den sigma flag rho rho' layout x :
  (forall n, den rho layout (sigma n) = Vlong (rho' n)) ->
  den rho layout flag = Vint (Int64.loword (rho' 4%nat)) ->
  den rho layout (scalar_bind sigma flag x) = den rho' layout x.
Proof.
  intros HS HF; induction x; cbn [scalar_bind den];
    rewrite ?IHx, ?IHx1, ?IHx2; try reflexivity.
  - apply HS.
  - destruct x; cbn [scalar_bind den] in *; try reflexivity; try (rewrite IHx; reflexivity).
    destruct (Nat.eqb n 4) eqn:HN.
    + apply Nat.eqb_eq in HN; subst n; exact HF.
    + cbn [den]; rewrite HS; reflexivity.
Qed.

Lemma scalar_loword_signed i : Int64.loword (Int64.repr (Int.signed i)) = i.
Proof.
  unfold Int64.loword; rewrite Int64.unsigned_repr_eq.
  rewrite <- (Int.repr_signed i) at 2.
  apply Int.eqm_samerepr; unfold Int.eqm, eqmod.
  exists (- (Int.signed i / Int64.modulus) * 4294967296)%Z.
  pose proof (Z.div_mod (Int.signed i) Int64.modulus
    ltac:(change Int64.modulus with 18446744073709551616; discriminate)).
  change Int64.modulus with 18446744073709551616 in *.
  change Int.modulus with 4294967296.
  lia.
Qed.

Lemma scalar_flag_lift rho layout flag :
  isk KI flag = true ->
  den rho layout flag =
    Vint (Int64.loword (Int64.repr (Int.signed (ii (den rho layout flag))))).
Proof.
  intro HK; rewrite scalar_loword_signed.
  apply den_KI; exact HK.
Qed.
