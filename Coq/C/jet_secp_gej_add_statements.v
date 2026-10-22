(** Exact original projective-addition spine and checked mixed-addition reuse.
    This decomposition is not yet a public jet equivalence proof. *)
From Coq Require Import List.
From compcert Require Import Clight.
Require Import C.jets_secp C.jet_secp_statement_prefix C.jet_secp_mixed_difference
 C.jet_secp_mixed_zero C.jet_secp_mixed_products.
Import ListNotations.
Set Default Timeout 10.

Definition gej_add_statements := fst (split_statement_last (fn_body f_secp256k1_gej_add_var)).
Definition gej_add_last := snd (split_statement_last (fn_body f_secp256k1_gej_add_var)).
Definition gej_add_after n := statement_sequence (skipn n gej_add_statements) gej_add_last.

Lemma gej_add_body_source : fn_body f_secp256k1_gej_add_var=gej_add_after 0.
Proof. reflexivity. Qed.
Lemma gej_add_prepare_source : fn_body f_secp256k1_gej_add_var=
 statement_sequence (firstn 10 gej_add_statements) (gej_add_after 10).
Proof. reflexivity. Qed.
Lemma gej_add_differences_shared : gej_add_after 10=
 statement_sequence mixed_difference_statements (gej_add_after 14).
Proof. reflexivity. Qed.
Lemma gej_add_guard_shared : nth 14 gej_add_statements Sskip=mixed_zero_head.
Proof. reflexivity. Qed.
Lemma gej_add_zero_branch_shared :
 (match nth 14 gej_add_statements Sskip with
  | Ssequence _ (Sifthenelse _ branch _) => branch | _ => Sskip end)=mixed_zero_branch.
Proof. reflexivity. Qed.
Lemma gej_add_products_shared : gej_add_after 20=
 statement_sequence mixed_product_statements (gej_add_after 23).
Proof. reflexivity. Qed.
Lemma gej_add_xy_tail_shared : gej_add_after 23=mixed_after_products.
Proof. reflexivity. Qed.
