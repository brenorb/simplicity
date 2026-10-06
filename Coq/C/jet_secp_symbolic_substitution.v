(** Reuse checked helper arithmetic for expressions inlined in actual C wrappers. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import AST Ctypes Integers Values.
Require Import C.jet_sx_expr C.jet_sx_zval C.jet_sx_state C.jet_sx_zrep.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Fixpoint sx_subst (sigma : nat -> sx) (x : sx) : sx :=
  match x with
  | XLv n => sigma n
  | XIb op a b => XIb op (sx_subst sigma a) (sx_subst sigma b)
  | XLb op a b => XLb op (sx_subst sigma a) (sx_subst sigma b)
  | XIsh op a k => XIsh op (sx_subst sigma a) k
  | XLsh op a k => XLsh op (sx_subst sigma a) k
  | XIcmp cmp sign a b => XIcmp cmp sign (sx_subst sigma a) (sx_subst sigma b)
  | XLcmp cmp sign a b => XLcmp cmp sign (sx_subst sigma a) (sx_subst sigma b)
  | XI2L sign a => XI2L sign (sx_subst sigma a)
  | XL2I a => XL2I (sx_subst sigma a)
  | XIcast size sign a => XIcast size sign (sx_subst sigma a)
  | XInz a => XInz (sx_subst sigma a)
  | XLnz a => XLnz (sx_subst sigma a)
  | XIz a => XIz (sx_subst sigma a)
  | XLz a => XLz (sx_subst sigma a)
  | XIneg a => XIneg (sx_subst sigma a)
  | XLneg a => XLneg (sx_subst sigma a)
  | XInot a => XInot (sx_subst sigma a)
  | XLnot a => XLnot (sx_subst sigma a)
  | _ => x
  end.

Lemma zval_sx_subst sigma rho x :
  zval rho (sx_subst sigma x) = zval (fun n => zval rho (sigma n)) x.
Proof.
  induction x; cbn [sx_subst zval]; try rewrite ?IHx, ?IHx1, ?IHx2; try reflexivity.
  all: try (destruct o; cbn [zval]; rewrite IHx; reflexivity).
  all: try (destruct sz, sg; cbn [zval]; rewrite IHx; reflexivity).
Qed.
Definition cell_subst sigma c : cell :=
  mkcell (cofs c) (cchunk c) (option_map (sx_subst sigma) (cval c)).
Lemma zcells_cell_subst sigma rho cells :
  zcells rho (map (cell_subst sigma) cells) =
    zcells (fun n => zval rho (sigma n)) cells.
Proof.
  unfold zcells; rewrite map_map; apply map_ext; intros c.
  unfold cell_subst; destruct (cval c) as [x|]; cbn; [apply zval_sx_subst|reflexivity].
Qed.
