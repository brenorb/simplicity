(** Rebase a read-only wrapper's invariant for the next reader invocation.
    Output capacity stays unchanged: it is not the consumed input length.
    The caller must separately establish the actual source-frame cursor. *)
From Coq Require Import ZArith List.
From compcert Require Import Integers Values Memory.
Require Import Simplicity.Word.
Require Import C.jet_secp_frame C.jet_frame_inv C.jet_secp_wrapper_run.
Require Import C.jet_secp_read_fe_numeric.
Require Import C.jet_input_layout.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma read_fe_final_inv_to_next_initial m0 bd dbase bw outedge cursor N bi
    edge rc next_rc cap (a b : Ty.tySem (Word 8)) m :
  invA m0 bd dbase bw outedge cursor N bi rc false [] cap
    (read_fe_rho (frame_input_word_bits a) rc) (read_fe_log bi (Ptrofs.repr edge)) m ->
  invA m0 bd dbase bw outedge cursor N bi next_rc false [] cap
    (read_fe_rho (frame_input_word_bits b) next_rc) [] m.
Proof.
  intro H.
  change (Int64.repr rc = Int64.repr rc /\
    finv m0 bd dbase bw outedge cursor N bi m false [] /\
    0 + cap <= N /\ 0 <= cap) in H.
  change (Int64.repr next_rc = Int64.repr next_rc /\
    finv m0 bd dbase bw outedge cursor N bi m false [] /\
    0 + cap <= N /\ 0 <= cap).
  split; [reflexivity|exact (proj2 H)].
Qed.
Print Assumptions read_fe_final_inv_to_next_initial.
