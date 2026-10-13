(** Transfer actual in-place negation output to the existing serializer
    representation; ownership and exact loads are derived, not assumed. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Values Memory Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_rep C.jet_sx_mem.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_frame.
Require Import C.jet_secp_scalar_get_b32_numeric C.jet_secp_scalar_get_b32_storage.
Require Import C.jet_secp_scalar_overflow_numeric C.jet_secp_canonical_scalar.
Require Import C.jet_secp_scalar_limb_bridge C.jet_secp_scalar_writer_run.
Require Import C.jet_secp_scalar_writer_storage.
Require Import C.jet_secp_scalar_negate_run C.jet_secp_scalar_negate_exec.
Require Import C.jet_secp_scalar_negate_values C.jet_secp_scalar_negate_numeric.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma scalar_negate_output_limbs_numeric rho layout :
  map (fun x => il (den rho layout x)) scalar_negate_limbs =
  map Int64.repr (scalar_limbs_of (scalar_negate_output_value rho layout)).
Proof.
  unfold scalar_negate_output_value; rewrite scalar_negate_output_exact.
  cbn [scalar_negate_raw map nth].
  rewrite scalar_limbs_of_four_words; cbn [map].
  rewrite !Int64.repr_unsigned; reflexivity.
Qed.

Lemma scalar_negate_output_scalar_at rho layout m :
  rep rho layout (sregs scalar_negate_state) m ->
  scalar_at m (blk layout 0) (bas layout 0)
    (map Int64.repr (scalar_limbs_of (scalar_negate_output_value rho (lay layout)))) /\
  Mem.range_perm m (blk layout 0) 0 32 Cur Freeable.
Proof.
  intro HRep.
  destruct (scalar_negate_final_storage rho layout m HRep) as [HBase [HFree HLoad]].
  split; [|exact HFree].
  rewrite <- scalar_negate_output_limbs_numeric.
  unfold scalar_at.
  split; [rewrite map_length; exact scalar_negate_limbs_length|].
  split; [lia|]. split; [rewrite HBase; exists 0; lia|].
  split; [rewrite HBase; change (32 <= 18446744073709551615); lia|].
  split.
  - rewrite HBase; intros pos HPos; eapply Mem.perm_implies; [apply HFree; lia|constructor].
  - intros i limb HNth.
    rewrite nth_error_map in HNth.
    destruct (nth_error scalar_negate_limbs i) as [x|] eqn:HX; [|discriminate].
    inversion HNth; subst limb.
    rewrite HBase, Z.add_0_l; exact (HLoad i x HX).
Qed.

Local Opaque secp_ge.
Theorem eval_scalar_negate_numeric_owned rho layout m :
  rep rho layout scalar_writer_initial_regs m ->
  0 <= scalar_limb_value rho < canonical_group_order ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_scalar_negate)
      [Vptr (blk layout 0) (Ptrofs.repr (bas layout 0));
       Vptr (blk layout 0) (Ptrofs.repr (bas layout 0))] E0 mf Vundef /\
    scalar_at mf (blk layout 0) (bas layout 0)
      (map Int64.repr (scalar_limbs_of ((- scalar_limb_value rho) mod canonical_group_order))) /\
    Mem.range_perm mf (blk layout 0) 0 32 Cur Freeable /\
    lframe (fun b ofs => ~ foot layout (map rshape scalar_writer_initial_regs) b ofs) m mf.
Proof.
  intros HRep HRange.
  destruct (eval_scalar_negate_from_owned_region rho layout m HRep) as [mf [HCall [HFinal HFrame]]].
  destruct (scalar_negate_output_scalar_at rho layout mf HFinal) as [HStorage HFree].
  rewrite (scalar_negate_normalized_value rho (lay layout) HRange) in HStorage.
  exists mf; split; [exact HCall|]; split; [exact HStorage|]; split; assumption.
Qed.

Theorem scalar_writer_initial_rep_from_negate rho layout m :
  rep rho layout (sregs scalar_negate_state) m ->
  rep (scalar_limb_rho (scalar_negate_output_value rho (lay layout)))
    [(blk layout 0, bas layout 0)] scalar_writer_initial_regs m.
Proof.
  intro HRep.
  destruct (scalar_negate_output_scalar_at rho layout m HRep) as [HStorage HFree].
  destruct (scalar_negate_final_storage rho layout m HRep) as [HBase _].
  rewrite HBase in HStorage |- *.
  apply scalar_writer_initial_rep_from_storage; assumption.
Qed.
