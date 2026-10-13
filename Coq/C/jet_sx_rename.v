(** Renaming symbolic scalar variables preserves machine-value denotation. *)
From Coq Require Import List.
From compcert Require Import Integers Values.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_rep
  C.jet_secp_symbolic_substitution.
Set Default Timeout 10.

Definition sx_rename (f : nat -> nat) := sx_subst (fun n => XLv (f n)).

Lemma den_sx_rename f rho beta x :
  den rho beta (sx_rename f x) = den (fun n => rho (f n)) beta x.
Proof.
  unfold sx_rename.
  induction x; cbn [sx_subst den];
    rewrite ?IHx, ?IHx1, ?IHx2; reflexivity.
Qed.

Lemma u64_cells_rename f xs : forall ofs,
  map (cell_subst (fun n => XLv (f n))) (u64_cells ofs xs) =
  u64_cells ofs (map (sx_rename f) xs).
Proof.
  induction xs as [|x xs IH]; intros ofs; cbn [map u64_cells cell_subst].
  - reflexivity.
  - rewrite IH; reflexivity.
Qed.
