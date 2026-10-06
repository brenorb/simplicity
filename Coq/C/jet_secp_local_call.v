(** Canonical results of the original wrappers, preserving caller locals for
    the real public function's final free_list. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Values Maps Memory Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_mem C.jet_sx_rep C.jet_sx_zval C.jet_sx_zrep.
Require Import C.jet_secp_frame C.jet_secp_fe_nv C.jet_secp_fe_math C.jet_secp_linkage C.jets_secp.
Require Import C.jet_input_layout C.jet_encoding C.jet_output_layout C.jet_frame_layout C.jet_frame_inv.
Require Simplicity.Ty Simplicity.Word Simplicity.Alg Simplicity.Translate.
Require Import C.jet_secp_wrapper_run C.jet_secp_read_fe_numeric.
Require Import C.jet_secp_write_fe_wrapper C.jet_secp_write_fe_numeric.
Require Import C.jet_secp_local_regions C.jet_secp_canonical_normalize.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque canonical_fe_normalize Simplicity.Translate.encode.

Lemma nth_zero_hd_region (regs : list region) :
  nth 0 regs (mkreg [] true None) = hd (mkreg [] true None) regs.
Proof. destruct regs; reflexivity. Qed.

Lemma local_read_final_field m ba bl bi edge rc (value : Ty.tySem (Word.Word 8)) :
  rep (read_fe_rho (frame_input_word_bits value) rc) [(ba,0%Z);(bl,0%Z)]
    (sregs (fst (rsel (read_fe_rho (frame_input_word_bits value) rc) (lay [(ba,0%Z);(bl,0%Z)])
      (local_read_result bi (Ptrofs.repr edge))))) m ->
  fe_at m ba 0 (map Int64.repr (fe_limbs_of
    (@Word.ToZ.Theory.toZ (Word.WordToZ 8) (@canonical_fe_normalize Alg.CoreFunSem value)))) /\
  Mem.range_perm m ba 0 40 Cur Freeable /\ Mem.range_perm m bl 0 16 Cur Freeable.
Proof.
  intro HRep.
  pose proof (local_read_selected_storage (read_fe_rho (frame_input_word_bits value) rc)
    (lay [(ba,0%Z);(bl,0%Z)]) bi (Ptrofs.repr edge)) as [HCount [HFreeA HFreeL]].
  assert (HIndex0 : (0 < length (sregs (fst (rsel (read_fe_rho (frame_input_word_bits value) rc)
    (lay [(ba,0%Z);(bl,0%Z)]) (local_read_result bi (Ptrofs.repr edge))))))%nat) by (rewrite HCount; lia).
  pose proof (nth_error_nth' _ (mkreg [] true None) HIndex0) as HNth.
  destruct (rep_region _ _ _ _ 0 _ HRep HNth) as (_ & _ & _ & HCells & HStorage).
  rewrite HFreeA in HStorage; destruct HStorage as [HZero [HWrite [HFieldFree HSize]]].
  rewrite HWrite, nth_zero_hd_region in HCells.
  change (Forall (cell_ok (read_fe_rho (frame_input_word_bits value) rc) [(ba,0%Z);(bl,0%Z)] m 0 true)
    (cells0 (fst (rsel (read_fe_rho (frame_input_word_bits value) rc) (lay [(ba,0%Z);(bl,0%Z)])
      (local_read_result bi (Ptrofs.repr edge)))))) in HCells.
  assert (HCheck : zreg_okb read_bounds 0
    (cells0 (fst (rsel (read_fe_rho (frame_input_word_bits value) rc) (lay [(ba,0%Z);(bl,0%Z)])
      (local_read_result bi (Ptrofs.repr edge))))) = true).
  { rewrite local_read_selected_cells; apply read_fe_selected_checked. }
  destruct (zreg_load (read_fe_rho (frame_input_word_bits value) rc) read_bounds [(ba,0%Z);(bl,0%Z)]
    (read_rho_bounds (frame_input_word_bits value) rc) m 0 true _ 0 HCheck HCells) as [HLoad _].
  rewrite local_read_selected_cells, read_fe_selected_canonical in HLoad.
  cbn [blk bas lay nth fst snd] in HLoad, HFieldFree.
  pose proof (rep_free_region _ _ _ _ 1 16 HRep ltac:(rewrite HCount; lia) HFreeL) as [_ HFrameFree].
  split; [|split; assumption].
  split; [lia|]; split; [exists 0; reflexivity|]; split.
  - change (40 <= 18446744073709551615); lia.
  - split; [apply freeable_range_writable; exact HFieldFree|].
    intros i x HNthValue; rewrite nth_error_map in HNthValue.
    destruct (nth_error (fe_limbs_of (@Word.ToZ.Theory.toZ (Word.WordToZ 8)
      (@canonical_fe_normalize Alg.CoreFunSem value))) i) as [z|] eqn:HZ; [|discriminate].
    inversion HNthValue; subst x.
    rewrite <- (HLoad i z HZ); f_equal; lia.
Qed.

Theorem eval_local_read_fe_canonical m0 bd dbase bw outedge cursor N bi edge rc
    (value : Ty.tySem (Word.Word 8)) m ba bl :
  write_frame_at m0 bd dbase bw outedge cursor N ->
  frame_input_cells_at m0 bi edge rc (map Some (frame_input_word_bits value)) ->
  0 <= rc -> rc + 256 <= Int64.max_unsigned ->
  Mem.range_perm m ba 0 40 Cur Freeable -> Mem.range_perm m bl 0 16 Cur Freeable ->
  frame_fields_at m bl 0 bi edge rc -> ba <> bl ->
  xsep (extA m0 bd bw bi) [(ba,0);(bl,0)] ->
  invA m0 bd dbase bw outedge cursor N bi rc false [] 256
    (read_fe_rho (frame_input_word_bits value) rc) [] m ->
  exists mr,
    Clight2.eval_funcall secp_ge m (Internal f_read_fe) [Vptr ba Ptrofs.zero; Vptr bl Ptrofs.zero] E0 mr Vundef /\
    fe_at mr ba 0 (map Int64.repr (fe_limbs_of
      (@Word.ToZ.Theory.toZ (Word.WordToZ 8) (@canonical_fe_normalize Alg.CoreFunSem value)))) /\
    Mem.range_perm mr ba 0 40 Cur Freeable /\ Mem.range_perm mr bl 0 16 Cur Freeable /\
    invA m0 bd dbase bw outedge cursor N bi rc false [] 256
      (read_fe_rho (frame_input_word_bits value) rc) (read_fe_log bi (Ptrofs.repr edge)) mr /\
    lframe (frame (extA m0 bd bw bi) [(ba,0);(bl,0)]
      (local_read_initial_regs bi (Ptrofs.repr edge)) m) m mr.
Proof.
  intros HOutput HInput HCursor HMax HFieldFree HFrameFree HFields HSeparate HSep HInv.
  assert (HLength : length (frame_input_word_bits value) = 256%nat).
  { rewrite frame_input_word_bits_length; reflexivity. }
  assert (HMax' : rc + Z.of_nat (length (frame_input_word_bits value)) <= Int64.max_unsigned).
  { rewrite HLength; exact HMax. }
  pose proof (local_read_initial_rep_from_storage (frame_input_word_bits value) rc m ba bl bi edge
    HFieldFree HFrameFree HFields HSeparate) as HRep.
  destruct (eval_local_read_fe m0 bd dbase bw outedge cursor N bi edge rc (frame_input_word_bits value)
    [] 256 HOutput HInput HCursor HMax' HLength m [(ba,0);(bl,0)] HRep HSep HInv)
    as [mr [HExec [HFinal [HFinalInv HFrame]]]].
  destruct (local_read_final_field mr ba bl bi edge rc value HFinal) as [HValue [HFreeA HFreeL]].
  exists mr; split; [exact HExec|]; split; [exact HValue|]; split; [exact HFreeA|];
    split; [exact HFreeL|]; split; assumption.
Qed.
Lemma no_local_write_foot ba b pos : b <> ba ->
  ~ foot [(ba,0)] (map rshape local_write_initial_regs) b pos.
Proof.
  intros HSeparate [r [s [d [ch [HGet [_ [HBlock _]]]]]]].
  destruct r as [|r].
  - change (b = ba) in HBlock; contradiction.
  - cbn [local_write_initial_regs map nth_error] in HGet; destruct r; discriminate.
Qed.
Theorem eval_local_write_fe_after_read m0 bd dbase bw outedge cursor N bi edge rc
    (value : Ty.tySem (Word.Word 8)) mr ba bl :
  write_frame_at m0 bd dbase bw outedge cursor N ->
  fe_at mr ba 0 (map Int64.repr (fe_limbs_of
    (@Word.ToZ.Theory.toZ (Word.WordToZ 8) (@canonical_fe_normalize Alg.CoreFunSem value)))) ->
  Mem.range_perm mr ba 0 40 Cur Freeable -> Mem.range_perm mr bl 0 16 Cur Freeable ->
  ba <> bl -> xsep (extA m0 bd bw bi) [(ba,0);(bl,0)] ->
  invA m0 bd dbase bw outedge cursor N bi rc false [] 256
    (read_fe_rho (frame_input_word_bits value) rc) (read_fe_log bi (Ptrofs.repr edge)) mr ->
  exists mw,
    Clight2.eval_funcall secp_ge mr (Internal f_write_fe)
      [Vptr bd (Ptrofs.repr dbase); Vptr ba Ptrofs.zero] E0 mw Vundef /\
    finv m0 bd dbase bw outedge cursor N bi mw true
      (Simplicity.Translate.encode (@canonical_fe_normalize Alg.CoreFunSem value)) /\
    Mem.range_perm mw ba 0 40 Cur Freeable /\ Mem.range_perm mw bl 0 16 Cur Freeable /\
    lframe (frame (extA m0 bd bw bi) [(ba,0)] local_write_initial_regs mr) mr mw.
Proof.
  intros HOutput HField HFieldFree HFrameFree HSeparate HSep HReadInv.
  pose proof (local_write_initial_rep_from_field
    (@Word.ToZ.Theory.toZ (Word.WordToZ 8) (@canonical_fe_normalize Alg.CoreFunSem value)) rc mr ba
    HField HFieldFree) as HRep.
  pose proof (read_fe_final_inv_to_write_initial m0 bd dbase bw outedge cursor N bi edge rc value mr HReadInv) as HInv.
  assert (HSepW : xsep (extA m0 bd bw bi) [(ba,0)]).
  { intros [|r] HIndex; [apply (HSep 0%nat); cbn; lia|cbn in HIndex; lia]. }
  destruct (eval_local_write_fe m0 bd dbase bw outedge cursor N bi 0 rc [] false [] HOutput
    mr [(ba,0)] (write_fe_rho
      (@Word.ToZ.Theory.toZ (Word.WordToZ 8) (@canonical_fe_normalize Alg.CoreFunSem value)) rc)
    HRep HSepW HInv) as [mw [HExec [HFinal [HFinalInv HFrame]]]].
  pose proof (local_write_selected_storage
    (write_fe_rho (@Word.ToZ.Theory.toZ (Word.WordToZ 8) (@canonical_fe_normalize Alg.CoreFunSem value)) rc)
    (lay [(ba,0)]) bd (Ptrofs.repr dbase)) as [HCount HFree].
  pose proof (rep_free_region _ _ _ _ 0 40 HFinal ltac:(rewrite HCount; lia) HFree) as [_ HFreeA].
  assert (HValidL : Mem.valid_block mr bl).
  { eapply Mem.perm_valid_block; apply (HFrameFree 0); lia. }
  assert (HFreeL : Mem.range_perm mw bl 0 16 Cur Freeable).
  { intros pos HPos; apply (proj1 (proj2 HFrame) bl pos Cur Freeable HValidL).
    - split; [exact HValidL|]; split.
      + apply no_local_write_foot; congruence.
      + apply (HSep 1%nat); cbn; lia.
    - apply HFrameFree; exact HPos. }
  unfold jet_secp_local_regions.wr_inv, invA in HFinalInv.
  rewrite local_write_selected_log, write_fe_has_written, orb_true_r,
    write_fe_selected_outs_canonical in HFinalInv.
  rewrite (canonical_fe_normalize_idempotent value) in HFinalInv.
  exists mw; split; [exact HExec|]; split; [exact (proj1 (proj2 HFinalInv))|];
    split; [exact HFreeA|]; split; [exact HFreeL|exact HFrame].
Qed.
