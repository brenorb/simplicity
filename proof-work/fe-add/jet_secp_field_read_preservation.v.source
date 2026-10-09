(** Preserve the first field while the second original reader executes.
    These contracts consume the reader's already-derived memory frame,
    not assumed field/output preservation. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Integers Values Memory.
Require Import C.jet_sx_state C.jet_sx_rep C.jet_sx_mem C.jet_sx_exec.
Require Import C.jet_secp_fe_nv C.jet_secp_frame C.jet_secp_local_regions C.jet_secp_public_body.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma field_at_lframe m mf b ofs xs P :
  fe_at m b ofs xs -> lframe P m mf ->
  (forall pos, P b pos) -> fe_at mf b ofs xs.
Proof.
  intros (HBase & HAlign & HMax & HPerm & HLoad) HFrame HP.
  assert (HV : Mem.valid_block m b).
  { eapply Mem.perm_valid_block. apply (HPerm ofs). lia. }
  unfold fe_at. split; [exact HBase|]. split; [exact HAlign|].
  split; [exact HMax|]. split.
  - intros pos HPos. apply (proj1 (proj2 HFrame));
      [exact HV|apply HP|apply HPerm; exact HPos].
  - intros i x Hi. rewrite (proj1 HFrame) by (auto).
    apply HLoad. exact Hi.
Qed.

Lemma field_freeable_lframe m mf b ofs xs P :
  fe_at m b ofs xs -> Mem.range_perm m b ofs (ofs+40) Cur Freeable ->
  lframe P m mf -> (forall pos, P b pos) ->
  Mem.range_perm mf b ofs (ofs+40) Cur Freeable.
Proof.
  intros HField HFree HFrame HP pos HPos.
  assert (HV : Mem.valid_block m b).
  { eapply Mem.perm_valid_block. apply (HFree ofs).
    destruct HField as (HB & _). lia. }
  apply (proj1 (proj2 HFrame)); [exact HV|apply HP|apply HFree; exact HPos].
Qed.

Lemma field_preserved_across_other_read m mf m0 bd bw bi ba bb bl edge xs :
  ba <> bb -> ba <> bl -> ~ extA m0 bd bw bi ba ->
  fe_at m ba 0 xs -> Mem.range_perm m ba 0 40 Cur Freeable ->
  lframe (frame (extA m0 bd bw bi) [(bb,0);(bl,0)]
    (local_read_initial_regs bi (Ptrofs.repr edge)) m) m mf ->
  fe_at mf ba 0 xs /\ Mem.range_perm mf ba 0 40 Cur Freeable.
Proof.
  intros HAB HAL HE HF HFree HFrame.
  assert (HV : Mem.valid_block m ba).
  { eapply Mem.perm_valid_block. apply (HFree 0). lia. }
  assert (HP : forall pos, frame (extA m0 bd bw bi) [(bb,0);(bl,0)]
    (local_read_initial_regs bi (Ptrofs.repr edge)) m ba pos).
  { intro pos. unfold frame. split; [exact HV|]. split.
    - apply no_local_read_foot; assumption.
    - exact HE. }
  split.
  - eapply field_at_lframe; eauto.
  - eapply field_freeable_lframe; eauto.
Qed.
Print Assumptions field_preserved_across_other_read.
