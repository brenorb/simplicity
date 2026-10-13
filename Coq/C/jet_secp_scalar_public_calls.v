(* Original public scalar-zero call nodes, not a rewritten function body. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight Clightdefs ClightBigstep Integers Values Maps Memory Events Globalenvs.
Require Import C.jet_exec C.jet_secp_linkage C.jets_secp.
Require Import C.jet_secp_scalar_public_entry.
Import ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition scalar_public_read_stmt :=
  match fn_body f_simplicity_scalar_is_zero with
  | Ssequence _ (Ssequence read _) => read | _ => Sskip end.
Definition scalar_public_zero_stmt :=
  match fn_body f_simplicity_scalar_is_zero with
  | Ssequence _ (Ssequence _ (Ssequence (Ssequence test _) _)) => test | _ => Sskip end.

Lemma scalar_public_read_symbols :
  Genv.find_symbol secp_ge _read_scalar = Some (secp_symbol_block _read_scalar) /\
  Genv.find_funct secp_ge (Vptr (secp_symbol_block _read_scalar) Ptrofs.zero) = Some (Internal f_read_scalar).
Proof. vm_compute; split; reflexivity. Qed.
Lemma scalar_public_zero_symbols :
  Genv.find_symbol secp_ge _secp256k1_scalar_is_zero = Some (secp_symbol_block _secp256k1_scalar_is_zero) /\
  Genv.find_funct secp_ge (Vptr (secp_symbol_block _secp256k1_scalar_is_zero) Ptrofs.zero) =
    Some (Internal f_secp256k1_scalar_is_zero).
Proof. vm_compute; split; reflexivity. Qed.
Local Opaque secp_ge.

(* These compositional call premises must be discharged by the full caller.
   Actual implementations are already proved in the reader/zero archives. *)
Lemma exec_scalar_public_read le m mf bl ba :
  Clight2.eval_funcall secp_ge m (Internal f_read_scalar)
    [Vptr ba Ptrofs.zero; Vptr bl Ptrofs.zero] E0 mf Vundef ->
  Clight2.exec_stmt secp_ge (scalar_public_env bl ba) le m scalar_public_read_stmt E0 le mf Out_normal.
Proof.
  intro HCall; destruct scalar_public_read_symbols as [HS HF].
  eapply ClightBigstep.exec_Scall with
    (vf := Vptr (secp_symbol_block _read_scalar) Ptrofs.zero)
    (vargs := [Vptr ba Ptrofs.zero; Vptr bl Ptrofs.zero]) (f := Internal f_read_scalar) (vres := Vundef).
  - reflexivity.
  - eapply eval_Elvalue.
    + eapply eval_Evar_global; [reflexivity|exact HS].
    + apply deref_loc_reference; reflexivity.
  - eapply eval_Econs.
    + apply eval_Eaddrof; apply eval_Evar_local; reflexivity.
    + reflexivity.
    + eapply eval_Econs.
      * apply eval_Eaddrof; apply eval_Evar_local; reflexivity.
      * reflexivity.
      * apply eval_Enil.
  - exact HF.
  - reflexivity.
  - exact HCall.
Qed.

Lemma exec_scalar_public_zero le m mf bl ba flag :
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_scalar_is_zero)
    [Vptr ba Ptrofs.zero] E0 mf (Vint flag) ->
  Clight2.exec_stmt secp_ge (scalar_public_env bl ba) le m scalar_public_zero_stmt E0
    (PTree.set _t'1 (Vint flag) le) mf Out_normal.
Proof.
  intro HCall; destruct scalar_public_zero_symbols as [HS HF].
  eapply ClightBigstep.exec_Scall with
    (vf := Vptr (secp_symbol_block _secp256k1_scalar_is_zero) Ptrofs.zero)
    (vargs := [Vptr ba Ptrofs.zero]) (f := Internal f_secp256k1_scalar_is_zero) (vres := Vint flag).
  - reflexivity.
  - eapply eval_Elvalue.
    + eapply eval_Evar_global; [reflexivity|exact HS].
    + apply deref_loc_reference; reflexivity.
  - eapply eval_Econs.
    + apply eval_Eaddrof; apply eval_Evar_local; reflexivity.
    + reflexivity.
    + apply eval_Enil.
  - exact HF.
  - reflexivity.
  - exact HCall.
Qed.

Require Import C.jet_sx_state C.jet_sx_exec C.jet_sx_mem C.jet_secp_frame C.jet_secp_wrapper_run.
Require Import C.jet_encoding C.jet_input_layout C.jet_output_layout C.jet_frame_layout C.jet_readBit_layout C.jet_frame_inv.
Require Simplicity.Ty Simplicity.Word Simplicity.Bit Simplicity.Alg Simplicity.BitMachine.
Require Import C.jet_secp_scalar_reader_run C.jet_secp_scalar_reader_lifecycle.
Require Import C.jet_secp_scalar_reader_zero C.jet_secp_scalar_zero_exec.
Require Import C.jet_secp_canonical_scalar_zero.
Require Import C.jet_secp_local_regions.
Require Import C.jet_secp_scalar_reader_set.

Lemma scalar_zero_foot_block ba b pos :
  foot [(ba,0)] (map rshape scalar_initial_regs) b pos -> b = ba.
Proof.
  intros (r & sh & d & ch & HNth & HIn & HBlock & HRange).
  destruct r as [ | r].
  - exact HBlock.
  - cbn [scalar_initial_regs map nth_error] in HNth; destruct r; discriminate.
Qed.

Theorem exec_scalar_public_read_and_test le m0 bd dbase bw outedge cursor N bi edge rc
    (value : Ty.tySem (Simplicity.Word.Word 8)) m ba bl :
  write_frame_at m0 bd dbase bw outedge cursor N ->
  frame_input_cells_at m0 bi edge rc (map Some (frame_input_word_bits value)) ->
  0 <= rc -> rc + 256 <= Int64.max_unsigned ->
  Mem.range_perm m ba 0 32 Cur Freeable -> Mem.range_perm m bl 0 16 Cur Freeable ->
  frame_fields_at m bl 0 bi edge rc -> ba <> bl ->
  xsep (extA m0 bd bw bi) [(ba,0);(bl,0)] ->
  invA m0 bd dbase bw outedge cursor N bi rc Datatypes.false [] 1
    (read_fe_rho (frame_input_word_bits value) rc) [] m ->
  exists mr mf,
    Clight2.exec_stmt secp_ge (scalar_public_env bl ba) le m
      scalar_public_read_stmt E0 le mr Out_normal /\
    Clight2.exec_stmt secp_ge (scalar_public_env bl ba) le mr
      scalar_public_zero_stmt E0
      (PTree.set _t'1 (Vint (bit_int (Bit.toBool (@canonical_scalar_is_zero Alg.CoreFunSem value)))) le)
      mf Out_normal /\
    rep (scalar_reader_zero_rho (read_fe_rho (frame_input_word_bits value) rc) (lay [(ba,0);(bl,0)]))
      [(ba,0)] scalar_initial_regs mf /\
    Mem.range_perm mf ba 0 32 Cur Freeable /\
    frame_fields_at mf bl 0 bi edge (rc+256) /\
    Mem.range_perm mf bl 0 16 Cur Freeable /\
    invA m0 bd dbase bw outedge cursor N bi rc Datatypes.false [] 1
      (read_fe_rho (frame_input_word_bits value) rc) (scalar_reader_log bi (Ptrofs.repr edge)) mf /\
    lframe (fun b pos => ~ foot [(ba,0)] (map rshape scalar_initial_regs) b pos) mr mf.
Proof.
  intros HO HI Hrc HM HA HL HS HSeparate HSep HInv.
  assert (HLength : length (frame_input_word_bits value) = 256%nat).
  { rewrite frame_input_word_bits_length; reflexivity. }
  assert (HMax : rc + Z.of_nat (length (frame_input_word_bits value)) <= Int64.max_unsigned).
  { rewrite HLength; exact HM. }
  pose proof (scalar_reader_initial_rep_from_storage (frame_input_word_bits value) rc
    m ba bl bi edge HA HL HS HSeparate) as HRep.
  destruct (eval_scalar_reader_numeric_owned m0 bd dbase bw outedge cursor N bi edge rc
    (frame_input_word_bits value) [] 1 HO HI Hrc HMax HLength m [(ba,0);(bl,0)] HRep HSep HInv)
    as (mr & HRead & HLoads & HValue & HCursor & HFinal & HReadInv & HReadFrame).
  destruct (eval_scalar_zero_after_reader value rc mr [(ba,0);(bl,0)] bi (Ptrofs.repr edge) HFinal)
    as (mf & HZero & HZeroRep & HFreeA & HZeroFrame).
  cbn [blk bas lay nth fst snd] in HRead, HCursor, HZero, HZeroRep, HFreeA, HZeroFrame.
  assert (HZeroOutside : lframe (fun b _ => b <> ba) mr mf).
  { eapply lframe_implies; [exact HZeroFrame|].
    intros b pos HNot _ HFoot; apply HNot; exact (scalar_zero_foot_block ba b pos HFoot). }
  assert (HValidL : Mem.valid_block mr bl).
  { eapply load_valid; exact (proj1 HCursor). }
  assert (HCursorFinal : frame_fields_at mf bl 0 bi edge (rc+256)).
  { destruct HZeroOutside as [HLoadsPreserve _]; destruct HCursor as [HE HC].
    split; rewrite HLoadsPreserve by (auto; intros; congruence); assumption. }
  assert (HFreeLRead : Mem.range_perm mr bl 0 16 Cur Freeable).
  { pose proof (rep_free_region _ _ _ _ 1 16 HFinal
      ltac:(rewrite scalar_reader_final_length; lia)
      ltac:(unfold scalar_reader_final_regs; rewrite scalar_reader_set_regions; reflexivity))
      as [_ HF]; exact HF. }
  assert (HFreeLFinal : Mem.range_perm mf bl 0 16 Cur Freeable).
  { intros pos HPos; eapply (proj1 (proj2 HZeroOutside));
      [exact HValidL|congruence|apply HFreeLRead; exact HPos]. }
  assert (HFinalInv : invA m0 bd dbase bw outedge cursor N bi rc Datatypes.false [] 1
      (read_fe_rho (frame_input_word_bits value) rc) (scalar_reader_log bi (Ptrofs.repr edge)) mf).
  { eapply invA_stable; [exact HO|exact HReadInv|].
    eapply lframe_implies; [exact HZeroOutside|].
    intros b pos HExt _ HEq; subst b; apply (HSep 0%nat ltac:(cbn; lia)); exact HExt. }
  exists mr, mf; split.
  - apply exec_scalar_public_read; exact HRead.
  - split.
    + apply exec_scalar_public_zero; exact HZero.
    + split; [exact HZeroRep|].
      split; [exact HFreeA|]; split; [exact HCursorFinal|].
      split; [exact HFreeLFinal|]; split; assumption.
Qed.
