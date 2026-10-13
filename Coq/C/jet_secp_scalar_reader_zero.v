(* Adapt actual reduced reader limbs to the unchanged scalar-zero helper. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Values Memory Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Bit Simplicity.Alg.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_rep C.jet_sx_mem.
Require Import C.jet_secp_local_regions C.jet_secp_linkage C.jets_secp.
Require Import C.jet_encoding C.jet_input_layout C.jet_secp_input_bytes C.jet_secp_wrapper_run.
Require Import C.jet_exec C.jet_readBit_layout C.jet_predicate_wide_exec C.jet_toZ.
Require Import C.jet_secp_scalar_reader_lifecycle C.jet_secp_scalar_reader_value.
Require Import C.jet_secp_scalar_reader_set C.jet_secp_scalar_set_shape.
Require Import C.jet_secp_scalar_zero_exec C.jet_secp_scalar_zero_numeric.
Require Import C.jet_secp_scalar_overflow_numeric C.jet_secp_canonical_scalar.
Require Import C.jet_secp_canonical_scalar_zero.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition scalar_reader_zero_rho rho layout n : int64 :=
  match n with
  | 1%nat => scalar_reader_limb rho layout 0
  | 2%nat => scalar_reader_limb rho layout 1
  | 3%nat => scalar_reader_limb rho layout 2
  | 4%nat => scalar_reader_limb rho layout 3
  | _ => Int64.zero
  end.

Lemma scalar_reader_zero_value rho layout :
  scalar_value (scalar_reader_zero_rho rho layout) =
    scalar_limb_value (scalar_reader_limb rho layout).
Proof. reflexivity. Qed.

Lemma scalar_reader_zero_rep rho layout bi edge m :
  rep rho layout (scalar_reader_final_regs bi edge) m ->
  rep (scalar_reader_zero_rho rho (lay layout))
    [(blk layout 0, bas layout 0)] scalar_initial_regs m.
Proof.
  intro HRep.
  pose proof (scalar_reader_final_loads rho layout bi edge m HRep) as HLoads.
  assert (HStorage : bas layout 0 = 0 /\ Mem.range_perm m (blk layout 0) 0 32 Cur Freeable).
  { eapply rep_free_region; [exact HRep|rewrite scalar_reader_final_length; lia|].
    unfold scalar_reader_final_regs; rewrite scalar_reader_set_regions; reflexivity. }
  destruct HStorage as [HBase HFree].
  assert (HValid : Mem.valid_block m (blk layout 0)).
  { pose proof (rep_region _ _ _ _ 0 _ HRep eq_refl) as HR.
    exact (proj1 (proj2 HR)). }
  apply (rep_add _ [] [] m (blk layout 0) (bas layout 0));
    [apply rep_nil|cbn; tauto|].
  change (region_ok (scalar_reader_zero_rho rho (lay layout))
    [(blk layout 0, bas layout 0)] m 0
    (free_region (mkreg (u64_cells 0 [XLv 1; XLv 2; XLv 3; XLv 4]) Datatypes.true None) 32)).
  apply region_with_freeable.
  - apply region_u64; cbn [bas blk lay nth fst snd length].
    + lia.
    + rewrite HBase; exists 0; lia.
    + rewrite HBase; change (32 <= 18446744073709551615); lia.
    + exact HValid.
    + rewrite HBase; apply freeable_range_writable; exact HFree.
    + intros i x HNth.
      assert (HI : (i < 4)%nat).
      { change (i < length [XLv 1; XLv 2; XLv 3; XLv 4])%nat.
        apply nth_error_Some; congruence. }
      destruct i as [ | [ | [ | [ | i]]]]; try lia; cbn [nth_error] in HNth;
        inversion HNth; subst x.
      all: split; [apply HLoads; lia|reflexivity].
  - exact HBase.
  - reflexivity.
  - exact HFree.
  - repeat constructor; cbn; lia.
Qed.

Lemma scalar_reader_zero_canonical_value value rc layout :
  scalar_value (scalar_reader_zero_rho (read_fe_rho (frame_input_word_bits value) rc) layout) =
    @toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem value).
Proof.
  rewrite scalar_reader_zero_value, scalar_reader_value_mod_group.
  - rewrite input_bytes_word256_value, canonical_scalar_normalize_numeric; reflexivity.
  - rewrite frame_input_word_bits_length; reflexivity.
Qed.

Theorem eval_scalar_zero_after_reader value rc m layout bi edge :
  rep (read_fe_rho (frame_input_word_bits value) rc) layout (scalar_reader_final_regs bi edge) m ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_scalar_is_zero)
      [Vptr (blk layout 0) (Ptrofs.repr (bas layout 0))] E0 mf
      (Vint (bit_int (Bit.toBool (@canonical_scalar_is_zero Alg.CoreFunSem value)))) /\
    rep (scalar_reader_zero_rho (read_fe_rho (frame_input_word_bits value) rc) (lay layout))
      [(blk layout 0, bas layout 0)] scalar_initial_regs mf /\
    Mem.range_perm mf (blk layout 0) (bas layout 0) (bas layout 0 + 32) Cur Freeable /\
    lframe (fun b pos => ~ foot [(blk layout 0, bas layout 0)]
      (map rshape scalar_initial_regs) b pos) m mf.
Proof.
  intro HRep.
  exact (eval_scalar_zero_canonical m [(blk layout 0, bas layout 0)]
    (scalar_reader_zero_rho (read_fe_rho (frame_input_word_bits value) rc) (lay layout)) value
    (scalar_reader_zero_rep _ _ bi edge m HRep)
    (scalar_reader_zero_canonical_value value rc (lay layout))).
Qed.
