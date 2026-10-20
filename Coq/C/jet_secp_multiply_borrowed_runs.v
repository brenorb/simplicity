(** The actual original statement slices with only rhs metadata borrowed.
    Computation here is on fixed symbolic syntax, never symbolic Mem.mem. *)
From Coq Require Import ZArith List.
From compcert Require Import Integers AST Ctypes Clight.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec.
Require Import C.jet_secp_linkage C.jets_secp.
Require Import C.jet_secp_multiply_run_run C.jet_secp_multiply_checkpoint_prefix.
Require Import C.jet_secp_multiply_second_state C.jet_secp_multiply_third_state.
Require Import C.jet_secp_multiply_next_checkpoint C.jet_secp_multiply_fourth_state.
Require Import C.jet_secp_multiply_fifth_state C.jet_secp_multiply_finish_state.
Require Import C.jet_secp_multiply_borrowed_transport.
Import ListNotations.
Set Default Timeout 10.

Lemma borrowed_prefix_run :
  xstmt (genv_cenv secp_ge) [] field_table 200 (snd mul_allocated)
    (borrow_state 1 prefix_initial) prefix_statement =
  Some (RDone (borrow_state 1 prefix_state) ONormal).
Proof. Timeout 10 vm_compute; reflexivity. Qed.

Lemma borrowed_second_run digits c d t3 :
  xstmt (genv_cenv secp_ge) [] field_table 160 (snd mul_allocated)
    (borrow_state 1 (second_initial digits c d t3)) second_statement =
  Some (RDone (borrow_state 1 (second_state digits c d t3)) ONormal).
Proof. Timeout 10 vm_compute; reflexivity. Qed.

Lemma borrowed_third_run digits c d t3 t4 tx :
  xstmt (genv_cenv secp_ge) [] field_table 160 (snd mul_allocated)
    (borrow_state 1 (third_initial digits c d t3 t4 tx)) third_statement =
  Some (RDone (borrow_state 1 (third_state digits c d t3 t4 tx)) ONormal).
Proof. Timeout 10 vm_compute; reflexivity. Qed.

Lemma borrowed_fourth_run digits written c d t3 t4 :
  xstmt (genv_cenv secp_ge) [] field_table 160 (snd mul_allocated)
    (borrow_state 1 (checkpoint_state digits written c d t3 t4)) fourth_statement =
  Some (RDone (borrow_state 1 (fourth_state digits written c d t3 t4)) ONormal).
Proof. Timeout 10 vm_compute; reflexivity. Qed.

Lemma borrowed_fifth_run digits written c d t3 t4 :
  xstmt (genv_cenv secp_ge) [] field_table 160 (snd mul_allocated)
    (borrow_state 1 (checkpoint_state digits written c d t3 t4)) fifth_statement =
  Some (RDone (borrow_state 1 (fifth_state digits written c d t3 t4)) ONormal).
Proof. Timeout 10 vm_compute; reflexivity. Qed.

Lemma borrowed_finish_run digits written c d t3 t4 :
  xstmt (genv_cenv secp_ge) [] field_table 160 (snd mul_allocated)
    (borrow_state 1 (checkpoint_state digits written c d t3 t4)) finish_statement =
  Some (RDone (borrow_state 1 (finish_state digits written c d t3 t4)) ONormal).
Proof. Timeout 10 vm_compute; reflexivity. Qed.
