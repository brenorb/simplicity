(** Shared memory invariants for SHA's mutable dispatch and readonly counter.
    Concrete programs establish this state from their actual initializers. *)
From Coq Require Import ZArith Lia.
From compcert Require Import Integers AST Memory Values.
Require Import C.jet_sx_mem C.jet_clight_internal_preserve C.jet_sha_uchars_exec.
Local Open Scope Z_scope.
Set Default Timeout 10.
Definition sha_global_state_at (dispatch compression counter:block) m:=
 (Mem.load Mptr m dispatch 0=Some (Vptr compression Ptrofs.zero) /\
 Mem.load Mint64 m counter 0=Some (Vlong sha_max_counter)) /\
 (forall ofs,~Mem.perm m counter ofs Max Writable) /\
 (forall ofs,~Mem.perm m dispatch ofs Max Freeable).
Section GlobalState.
Variables dispatch compression counter:block.
Lemma sha_global_state_separate m b size : (sha_global_state_at dispatch compression counter) m -> 0<size ->
  Mem.range_perm m b 0 size Cur Freeable -> b<>dispatch /\ b<>counter.
Proof.
  intros [_ [Counter Dispatch]] Size Owned;split;intro Same;subst b.
  - apply (Dispatch 0);apply Mem.perm_cur_max;apply Owned;lia.
  - apply (Counter 0);apply Mem.perm_cur_max;eapply Mem.perm_implies;[apply Owned;lia|constructor].
Qed.

Lemma sha_global_state_preserved m mf P : (sha_global_state_at dispatch compression counter) m ->
  readonly_preserved m mf -> lframe P m mf ->
  (forall ofs,P dispatch ofs) -> (sha_global_state_at dispatch compression counter) mf.
Proof.
  intros [[Dispatch Counter] [NoWrite NoFree]] [Forward Unchanged] [Loads _] Outside.
  assert (VD:Mem.valid_block m dispatch).
  { apply Mem.load_valid_access in Dispatch.
    eapply Mem.valid_access_valid_block;eapply Mem.valid_access_implies;[exact Dispatch|constructor]. }
  assert (VC:Mem.valid_block m counter).
  { apply Mem.load_valid_access in Counter.
    eapply Mem.valid_access_valid_block;eapply Mem.valid_access_implies;[exact Counter|constructor]. }
  split.
  - split.
    +       change (Mem.load Mptr mf dispatch 0=
        Some (Vptr compression Ptrofs.zero)).
      rewrite Loads;[exact Dispatch|exact VD|intros;apply Outside].
    + eapply Mem.load_unchanged_on;[exact Unchanged| |exact Counter].
      intros ofs Range;split;[exact VC|apply NoWrite].
  - split.
    + intros ofs Perm;apply (NoWrite ofs);exact (proj2 (Forward _ VC) ofs Writable Perm).
    + intros ofs Perm;apply (NoFree ofs);exact (proj2 (Forward _ VD) ofs Freeable Perm).
Qed.

End GlobalState.
