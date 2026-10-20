(** Original multiplication heads 82..96, through r[2] and the c shift. *)
From Coq Require Import ZArith List.
From compcert Require Import Integers AST Ctypes Clight Clightdefs Maps Values.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_mem C.jet_sx_rep.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_statement_prefix.
Require Import C.jet_secp_multiply_run_run C.jet_secp_multiply_checkpoint_prefix C.jet_secp_multiply_checkpoint_ops.
Require Import C.jet_secp_multiply_second_entry C.jet_secp_multiply_next_checkpoint.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition fifth_spine := firstn 15 (skipn 82 mul_spine).
Definition fifth_statement := statement_sequence fifth_spine Sskip.
Definition through_fifth := statement_sequence (firstn 97 mul_spine) Sskip.
Definition after_fifth := statement_sequence (skipn 97 mul_spine) mul_last.
Lemma through_fifth_suffix_source : statement_sequence (firstn 97 mul_spine) after_fifth = fn_body f_secp256k1_fe_mul_inner.
Proof. reflexivity. Qed.
Lemma fourth_fifth_source : statement_sequence (firstn 82 mul_spine) fifth_statement = through_fifth.
Proof. reflexivity. Qed.

Definition fifth_run digits written c d t3 t4 := xstmt (genv_cenv secp_ge) [] field_table 160
  (snd mul_allocated) (checkpoint_state digits written c d t3 t4) fifth_statement.
Lemma fifth_completes digits written c d t3 t4 :
  match fifth_run digits written c d t3 t4 with Some (RDone _ ONormal) => true | _ => false end = true.
Proof. vm_compute; reflexivity. Qed.
Definition fifth_state digits written c d t3 t4 := match fifth_run digits written c d t3 t4 with
  | Some (RDone st _) => st | _ => checkpoint_state digits written c d t3 t4 end.
Lemma fifth_run_eq digits written c d t3 t4 :
  fifth_run digits written c d t3 t4 = Some (RDone (fifth_state digits written c d t3 t4) ONormal).
Proof.
  pose proof (fifth_completes digits written c d t3 t4) as H; unfold fifth_state.
  destruct (fifth_run digits written c d t3 t4) as [r|]; [|discriminate].
  destruct r; [destruct o; try discriminate; reflexivity|discriminate].
Qed.

Definition fifth_base_c_sy (digits : nat -> int64) (c : int64 * int64) :=
  sx_accum (sx_accum (sx_accum (XL (fst c), XL (snd c)) (XL (digits 0%nat)) (XL (digits 7%nat)))
    (XL (digits 1%nat)) (XL (digits 6%nat))) (XL (digits 2%nat)) (XL (digits 5%nat)).
Definition fifth_fold_d_sy (digits : nat -> int64) (d : int64 * int64) :=
  sx_accum (sx_accum (XL (fst d), XL (snd d)) (XL (digits 3%nat)) (XL (digits 9%nat)))
    (XL (digits 4%nat)) (XL (digits 8%nat)).
Definition fifth_fold_c_sy digits c d := sx_accum (fifth_base_c_sy digits c)
  (XLc (Int64.repr 68719492368)) (fst (fifth_fold_d_sy digits d)).
Definition fifth_final_c_sy digits c d := sx_shift52 (fifth_fold_c_sy digits c d).
Definition fifth_final_d_sy digits d := sx_shift64 (fifth_fold_d_sy digits d).
Definition fifth_r2_sy digits c d := XLb Band (fst (fifth_fold_c_sy digits c d)) (XLc (Int64.repr 4503599627370495)).

Lemma fifth_regions_exact digits written c d t3 t4 : sregs (fifth_state digits written c d t3 t4) =
  [mkreg (u64_cells 0 [XL (written 0%nat); XL (written 1%nat); fifth_r2_sy digits c d; XL (written 3%nat); XL (written 4%nat)]) true (Some 40);
   mkreg (u64_cells 0 [XL (digits 5%nat); XL (digits 6%nat); XL (digits 7%nat); XL (digits 8%nat); XL (digits 9%nat)]) true (Some 40);
   mkreg (u64_cells 0 [fst (fifth_final_c_sy digits c d); snd (fifth_final_c_sy digits c d)]) true (Some 16);
   mkreg (u64_cells 0 [fst (fifth_final_d_sy digits d); snd (fifth_final_d_sy digits d)]) true (Some 16)].
Proof. reflexivity. Qed.
Lemma fifth_live_lookup digits written c d t3 t4 id x :
  In (id,x) (checkpoint_bindings digits t3 t4) -> (stemps (fifth_state digits written c d t3 t4))!id = Some x.
Proof.
  intro H; cbn [checkpoint_bindings second_bindings app In] in H.
  repeat destruct H as [H|H]; try contradiction; inversion H; subst; timeout 10 reflexivity.
Qed.
