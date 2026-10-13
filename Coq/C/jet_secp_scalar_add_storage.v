(** Actual addition output reconstructed as serializer storage. The existing
    radix/serializer lemmas are shared with normalize and negate. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Integers Values Memory.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_rep.
Require Import C.jet_secp_frame C.jet_secp_local_regions.
Require Import C.jet_secp_scalar_get_b32_numeric C.jet_secp_scalar_get_b32_storage.
Require Import C.jet_secp_scalar_overflow_numeric C.jet_secp_scalar_limb_bridge.
Require Import C.jet_secp_scalar_writer_run C.jet_secp_scalar_writer_storage.
Require Import C.jet_secp_scalar_add_run C.jet_secp_scalar_add_exec.
Require Import C.jet_secp_scalar_add_reduced.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque scalar_add_limbs.

Lemma scalar_add_output_limbs_numeric rho layout :
  map (fun x => il (den rho layout x)) scalar_add_limbs =
  map Int64.repr (scalar_limbs_of (scalar_add_output_value rho layout)).
Proof.
  assert (HMap : map (fun x => il (den rho layout x)) scalar_add_limbs =
    [scalar_add_limb rho layout 0; scalar_add_limb rho layout 1;
     scalar_add_limb rho layout 2; scalar_add_limb rho layout 3]).
  { unfold scalar_add_limb.
    generalize scalar_add_limbs_length; generalize scalar_add_limbs.
    intros xs HL; destruct xs as [|x0 [|x1 [|x2 [|x3 xs]]]]; try discriminate.
    destruct xs; [reflexivity|cbn [length] in HL; lia]. }
  rewrite HMap; unfold scalar_add_output_value, scalar_limb_value.
  rewrite scalar_limbs_of_four_words; cbn [map]; rewrite !Int64.repr_unsigned; reflexivity.
Qed.

Lemma scalar_add_output_scalar_at rho layout m :
  rep rho layout (sregs scalar_add_state) m ->
  scalar_at m (blk layout 0) (bas layout 0)
    (map Int64.repr (scalar_limbs_of (scalar_add_output_value rho (lay layout)))) /\
  Mem.range_perm m (blk layout 0) 0 32 Cur Freeable /\
  Mem.range_perm m (blk layout 1) 0 32 Cur Freeable.
Proof.
  intro HRep.
  destruct (scalar_add_final_storage rho layout m HRep)
    as [HBase [HFree [HBase1 [HFree1 [HLoad HSecond]]]]].
  split; [|split; assumption].
  rewrite <- scalar_add_output_limbs_numeric.
  unfold scalar_at.
  split; [rewrite map_length; exact scalar_add_limbs_length|].
  split; [lia|]. split; [rewrite HBase; exists 0; lia|].
  split; [rewrite HBase; change (32 <= 18446744073709551615); lia|].
  split.
  - rewrite HBase; intros pos HPos; eapply Mem.perm_implies; [apply HFree; lia|constructor].
  - intros i limb HNth.
    rewrite nth_error_map in HNth.
    destruct (nth_error scalar_add_limbs i) as [x|] eqn:HX; [|discriminate].
    inversion HNth; subst limb.
    rewrite HBase, Z.add_0_l; exact (HLoad i x HX).
Qed.

Theorem scalar_writer_initial_rep_from_add rho layout m :
  rep rho layout (sregs scalar_add_state) m ->
  rep (scalar_limb_rho (scalar_add_output_value rho (lay layout)))
    [(blk layout 0, bas layout 0)] scalar_writer_initial_regs m.
Proof.
  intro HRep.
  destruct (scalar_add_output_scalar_at rho layout m HRep) as [HStorage [HFree HSecond]].
  destruct (scalar_add_final_storage rho layout m HRep) as [HBase _].
  rewrite HBase in HStorage |- *.
  apply scalar_writer_initial_rep_from_storage; assumption.
Qed.
