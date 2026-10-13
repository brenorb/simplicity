(** Actual normalized coordinate, source cursor and ownership from final rep. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Integers Values Memory.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_rep C.jet_sx_mem.
Require Import C.jet_sx_zval C.jet_sx_zrep.
Require Import C.jet_encoding C.jet_input_layout C.jet_frame_layout.
Require Import C.jet_secp_frame C.jet_secp_fe_nv C.jet_secp_fe_math.
Require Import C.jet_secp_wrapper_run C.jet_secp_local_regions C.jet_secp_local_call.
Require Import C.jet_secp_read_fe_numeric C.jet_secp_canonical_normalize.
Require Import C.jet_secp_point_write_run C.jet_secp_point_read_run C.jet_secp_point_read_values.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque canonical_fe_normalize.

Lemma point_read_leaf_source k bi edge :
  all_leaf_property (fun state =>
    rcells (nth 1 (sregs state) (mkreg [] true None)) =
      mk_frame_cells (XA bi edge) (Int64.repr 256)) (point_read_result k bi edge).
Proof. unfold point_read_result; destruct k; repeat split; reflexivity. Qed.
Lemma point_read_selected_source k rho layout bi edge :
  rcells (nth 1 (sregs (fst (rsel rho layout (point_read_result k bi edge))))
    (mkreg [] true None)) = mk_frame_cells (XA bi edge) (Int64.repr 256).
Proof. apply all_leaf_property_selected; apply point_read_leaf_source. Qed.
Local Opaque point_read_result.

Lemma point_read_final_source_fields k m ba bl bi edge rc rho :
  rho 0%nat = Int64.repr rc ->
  rep rho [(ba,0);(bl,0)]
    (sregs (fst (rsel rho (lay [(ba,0);(bl,0)])
      (point_read_result k bi (Ptrofs.repr edge))))) m ->
  frame_fields_at m bl 0 bi edge (rc+256).
Proof.
  intros HR HRep.
  set (regs := sregs (fst (rsel rho (lay [(ba,0);(bl,0)])
    (point_read_result k bi (Ptrofs.repr edge))))) in *.
  assert (HCount : length regs = 2%nat).
  { exact (proj1 (point_read_selected_storage k bi (Ptrofs.repr edge)
      rho (lay [(ba,0);(bl,0)]))). }
  assert (HIndex : (1 < length regs)%nat) by (rewrite HCount; lia).
  pose proof (nth_error_nth' regs (mkreg [] true None) HIndex) as HNth.
  pose proof (rep_region rho [(ba,0);(bl,0)] regs m 1 _ HRep HNth) as HRegion.
  assert (HCells : rcells (nth 1 regs (mkreg [] true None)) =
    mk_frame_cells (XA bi (Ptrofs.repr edge)) (Int64.repr 256)).
  { apply point_read_selected_source. }
  pose proof (region_load rho [(ba,0);(bl,0)] m 1 _ 0 Mint64
    (XA bi (Ptrofs.repr edge)) HRegion ltac:(rewrite HCells; cbn; auto)) as HP.
  pose proof (region_load rho [(ba,0);(bl,0)] m 1 _ 8 Mint64
    (XLb Badd (XLv 0%nat) (XLc (Int64.repr 256))) HRegion
    ltac:(rewrite HCells; cbn; auto)) as HC.
  change (Mem.load Mint64 m bl 0 = Some (Vptr bi (Ptrofs.repr edge))) in HP.
  change (Mem.load Mint64 m bl 8 =
    Some (Vlong (Int64.add (rho 0%nat) (Int64.repr 256)))) in HC.
  assert (HAdd : Int64.add (Int64.repr rc) (Int64.repr 256) = Int64.repr (rc+256)).
  { rewrite Int64.add_unsigned. apply Int64.eqm_samerepr.
    apply Int64.eqm_add; apply Int64.eqm_sym; apply Int64.eqm_unsigned_repr. }
  rewrite HR, HAdd in HC. split; assumption.
Qed.

Lemma point_read_final_field k m ba bl bi edge rc (value : Ty.tySem (Simplicity.Word.Word 8)) :
  rep (read_fe_rho (frame_input_word_bits value) rc) [(ba,0);(bl,0)]
    (sregs (fst (rsel (read_fe_rho (frame_input_word_bits value) rc) (lay [(ba,0);(bl,0)])
      (point_read_result k bi (Ptrofs.repr edge))))) m ->
  fe_at m ba (point_coordinate_offset k) (map Int64.repr (fe_limbs_of
    (@Simplicity.Word.ToZ.Theory.toZ (Simplicity.Word.WordToZ 8)
      (@canonical_fe_normalize Simplicity.Alg.CoreFunSem value)))) /\
  Mem.range_perm m ba 0 128 Cur Freeable /\ Mem.range_perm m bl 0 16 Cur Freeable.
Proof.
  intro HRep.
  pose proof (point_read_selected_storage k bi (Ptrofs.repr edge)
    (read_fe_rho (frame_input_word_bits value) rc) (lay [(ba,0);(bl,0)]))
    as [HCount [HFreeA HFreeL]].
  assert (HIndex : (0 < length (sregs (fst (rsel (read_fe_rho (frame_input_word_bits value) rc)
    (lay [(ba,0%Z);(bl,0%Z)]) (point_read_result k bi (Ptrofs.repr edge))))))%nat)
    by (rewrite HCount; lia).
  pose proof (nth_error_nth' _ (mkreg [] true None) HIndex) as HNth.
  destruct (rep_region _ _ _ _ 0 _ HRep HNth) as (_ & _ & _ & HCells & HStorage).
  rewrite HFreeA in HStorage; destruct HStorage as [HZero [HWrite [HPointFree HSize]]].
  rewrite HWrite, nth_zero_hd_region in HCells.
  change (Forall (cell_ok (read_fe_rho (frame_input_word_bits value) rc) [(ba,0);(bl,0)] m 0 true)
    (cells0 (fst (rsel (read_fe_rho (frame_input_word_bits value) rc) (lay [(ba,0);(bl,0)])
      (point_read_result k bi (Ptrofs.repr edge)))))) in HCells.
  pose proof (point_read_selected_checked k bi (Ptrofs.repr edge)
    (read_fe_rho (frame_input_word_bits value) rc) (lay [(ba,0);(bl,0)])) as HCheck.
  destruct (zreg_load (read_fe_rho (frame_input_word_bits value) rc) read_bounds [(ba,0);(bl,0)]
    (read_rho_bounds (frame_input_word_bits value) rc) m 0 true _ (point_coordinate_offset k)
    HCheck HCells) as [HLoad _].
  rewrite point_read_selected_canonical in HLoad.
  cbn [blk bas lay nth fst snd] in HLoad, HPointFree.
  pose proof (rep_free_region _ _ _ _ 1 16 HRep ltac:(rewrite HCount; lia) HFreeL) as [_ HFrameFree].
  pose proof (point_coordinate_offset_bounds k) as HB.
  assert (HMax : 128 <= Ptrofs.max_unsigned).
  { change (128 <= 18446744073709551615); lia. }
  split; [|split; assumption].
  split; [lia|]; split; [destruct k; cbn; [exists 0|exists 5|exists 10]; reflexivity|].
  split; [lia|]. split.
  - apply freeable_range_writable. intros pos HPos; apply HPointFree; lia.
  - intros i x HValue. rewrite nth_error_map in HValue.
    destruct (nth_error (fe_limbs_of (@Simplicity.Word.ToZ.Theory.toZ (Simplicity.Word.WordToZ 8)
      (@canonical_fe_normalize Simplicity.Alg.CoreFunSem value))) i) as [z|] eqn:HZ;
      [|discriminate].
    inversion HValue; subst x.
    rewrite <- (HLoad i z HZ); f_equal; lia.
Qed.
Print Assumptions point_read_final_field.
