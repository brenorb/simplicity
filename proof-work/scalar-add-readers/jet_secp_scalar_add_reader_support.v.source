(** Actual scalar-reader calls, invariant rebasing and preservation of a
    previously read scalar. Shared caller support; no public jet yet. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Values Memory Events.
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word.
Require Import C.jet_sx_state C.jet_sx_rep C.jet_sx_exec C.jet_sx_mem.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_frame C.jet_secp_wrapper_run.
Require Import C.jet_frame_layout C.jet_frame_inv C.jet_input_layout C.jet_output_layout.
Require Import C.jet_encoding C.jet_secp_local_regions C.jet_secp_public_body.
Require Import C.jet_secp_canonical_scalar C.jet_secp_scalar_get_b32_numeric.
Require Import C.jet_secp_scalar_get_b32_storage C.jet_secp_scalar_limb_bridge.
Require Import C.jet_secp_scalar_reader_run C.jet_secp_scalar_reader_set.
Require Import C.jet_secp_scalar_reader_lifecycle C.jet_secp_scalar_public_rest.
Require Import C.jet_secp_scalar_public_entry.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque canonical_scalar_normalize.

Theorem eval_read_scalar_canonical_with_source m0 bd dbase bw outedge cursor N cap bi edge rc
    (value : Ty.tySem (Word 8)) m ba bl :
  write_frame_at m0 bd dbase bw outedge cursor N ->
  frame_input_cells_at m0 bi edge rc (map Some (frame_input_word_bits value)) ->
  0 <= rc -> rc + 256 <= Int64.max_unsigned ->
  Mem.range_perm m ba 0 32 Cur Freeable -> Mem.range_perm m bl 0 16 Cur Freeable ->
  frame_fields_at m bl 0 bi edge rc -> ba <> bl ->
  xsep (extA m0 bd bw bi) [(ba,0);(bl,0)] ->
  invA m0 bd dbase bw outedge cursor N bi rc false [] cap
    (read_fe_rho (frame_input_word_bits value) rc) [] m ->
  exists mr,
    Clight2.eval_funcall secp_ge m (Internal f_read_scalar)
      [Vptr ba Ptrofs.zero; Vptr bl Ptrofs.zero] E0 mr Vundef /\
    scalar_at mr ba 0 (map Int64.repr (scalar_limbs_of
      (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem value)))) /\
    frame_fields_at mr bl 0 bi edge (rc+256) /\
    Mem.range_perm mr ba 0 32 Cur Freeable /\ Mem.range_perm mr bl 0 16 Cur Freeable /\
    invA m0 bd dbase bw outedge cursor N bi rc false [] cap
      (read_fe_rho (frame_input_word_bits value) rc) (scalar_reader_log bi (Ptrofs.repr edge)) mr /\
    lframe (frame (extA m0 bd bw bi) [(ba,0);(bl,0)]
      (scalar_reader_initial_regs bi (Ptrofs.repr edge)) m) m mr.
Proof.
  intros HO HI Hrc HM HA HL HS HSeparate HSep HInv.
  assert (HLength : length (frame_input_word_bits value) = 256%nat).
  { rewrite frame_input_word_bits_length; reflexivity. }
  assert (HMax : rc + Z.of_nat (length (frame_input_word_bits value)) <= Int64.max_unsigned).
  { rewrite HLength; exact HM. }
  pose proof (scalar_reader_initial_rep_from_storage (frame_input_word_bits value) rc
    m ba bl bi edge HA HL HS HSeparate) as HRep.
  destruct (eval_scalar_reader_numeric_owned m0 bd dbase bw outedge cursor N bi edge rc
    (frame_input_word_bits value) [] cap HO HI Hrc HMax HLength m [(ba,0);(bl,0)] HRep HSep HInv)
    as (mr & HRead & HLoads & HValue & HCursor & HFinal & HReadInv & HReadFrame).
  destruct (scalar_reader_storage_for_serializer value rc [(ba,0);(bl,0)] bi
    (Ptrofs.repr edge) mr HFinal) as [HStorage HFreeA].
  destruct (rep_free_region _ _ _ _ 1 16 HFinal
    ltac:(rewrite scalar_reader_final_length; lia)
    ltac:(unfold scalar_reader_final_regs; rewrite scalar_reader_set_regions; reflexivity))
    as [_ HFreeL].
  cbn [blk bas lay nth fst snd] in HRead, HStorage, HFreeA, HFreeL, HCursor.
  exists mr; split; [exact HRead|]; split; [exact HStorage|]; split; [exact HCursor|];
    split; [exact HFreeA|]; split; [exact HFreeL|]; split; assumption.
Qed.

Lemma scalar_reader_final_inv_to_next_initial m0 bd dbase bw outedge cursor N bi
    edge rc next_rc cap (a b : Ty.tySem (Word 8)) m :
  invA m0 bd dbase bw outedge cursor N bi rc false [] cap
    (read_fe_rho (frame_input_word_bits a) rc) (scalar_reader_log bi (Ptrofs.repr edge)) m ->
  invA m0 bd dbase bw outedge cursor N bi next_rc false [] cap
    (read_fe_rho (frame_input_word_bits b) next_rc) [] m.
Proof.
  intro HInv.
  change (Int64.repr rc = Int64.repr rc /\
    finv m0 bd dbase bw outedge cursor N bi m false [] /\
    0 + cap <= N /\ 0 <= cap) in HInv.
  change (Int64.repr next_rc = Int64.repr next_rc /\
    finv m0 bd dbase bw outedge cursor N bi m false [] /\
    0 + cap <= N /\ 0 <= cap).
  split; [reflexivity|exact (proj2 HInv)].
Qed.

Lemma scalar_at_lframe m mf b ofs xs P :
  scalar_at m b ofs xs -> lframe P m mf ->
  (forall pos, P b pos) -> scalar_at mf b ofs xs.
Proof.
  intros (HLength & HBase & HAlign & HMax & HPerm & HLoad) HFrame HP.
  assert (HV : Mem.valid_block m b).
  { eapply Mem.perm_valid_block; apply (HPerm ofs); lia. }
  unfold scalar_at; split; [exact HLength|]; split; [exact HBase|];
    split; [exact HAlign|]; split; [exact HMax|]; split.
  - intros pos HPos; apply (proj1 (proj2 HFrame));
      [exact HV|apply HP|apply HPerm; exact HPos].
  - intros i x Hi; rewrite (proj1 HFrame) by auto; apply HLoad; exact Hi.
Qed.

Lemma scalar_preserved_across_other_read m mf m0 bd bw bi ba bb bl edge xs :
  ba <> bb -> ba <> bl -> ~ extA m0 bd bw bi ba ->
  scalar_at m ba 0 xs -> Mem.range_perm m ba 0 32 Cur Freeable ->
  lframe (frame (extA m0 bd bw bi) [(bb,0);(bl,0)]
    (scalar_reader_initial_regs bi (Ptrofs.repr edge)) m) m mf ->
  scalar_at mf ba 0 xs /\ Mem.range_perm mf ba 0 32 Cur Freeable.
Proof.
  intros HAB HAL HE HF HFree HFrame.
  assert (HV : Mem.valid_block m ba).
  { eapply Mem.perm_valid_block; apply (HFree 0); lia. }
  assert (HP : forall pos, frame (extA m0 bd bw bi) [(bb,0);(bl,0)]
    (scalar_reader_initial_regs bi (Ptrofs.repr edge)) m ba pos).
  { intro pos; unfold frame; split; [exact HV|]; split.
    - apply scalar_locals_not_foot; assumption.
    - exact HE. }
  split.
  - eapply scalar_at_lframe; eauto.
  - intros pos HPos; apply (proj1 (proj2 HFrame));
      [exact HV|apply HP|apply HFree; exact HPos].
Qed.
