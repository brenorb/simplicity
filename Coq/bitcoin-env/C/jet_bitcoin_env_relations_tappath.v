(** The [tappath] relation for every path length: the [txEnv] left by the
    real builders satisfies [bitcoin_tappath_env_rep_nullable], under which
    the jet is proved in [C.jet_bitcoin_tappath_nullable], also when the
    path is empty (where the builder stores a null path pointer). *)
From Coq Require Import ZArith List Lia PeanoNat.
From compcert Require Import Coqlib Integers AST Values Memory.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest.
Require Import C.jet_uint32_array_init C.jet_sha_add_n_calls C.jet_sha_hash_closed.
Require Import C.jet_bitcoin_ext_prim C.jet_bitcoin_ext_ptr_jets C.jet_bitcoin_tappath_nullable.
Require Import C.jet_bitcoin_env_tomidstate C.jet_bitcoin_env_tapenv_key C.jet_bitcoin_env_tapenv.
Require Import C.jet_bitcoin_env_tapenv_link C.jet_bitcoin_env_build.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 120.

Theorem ready_tappath_nullable m bD oD bT bE (e : ext_environment)
    niv nov ver lt txb data val spb nb cb0 kb cmrb pb :
  env_ready m bD oD bT bE e niv nov ver lt txb data val spb nb cb0 kb cmrb pb ->
  0 <= oD /\ oD + 56 <= Ptrofs.max_unsigned ->
  bitcoin_tappath_env_rep_nullable m (Vptr bD (Ptrofs.repr oD)) e
    [(bD, oD + 8, oD + 16); (bE, 0 + 0, 0 + 8); (bE, 176, 176 + 32 * Z.of_nat (length (extTappath e)))].
Proof.
  intros (_ & R8 & _ & _ & _ & HTb & _ & (_ & _ & DLn & DP & _)) HoD.
  unfold tapenv_built in HTb. cbv beta zeta in HTb.
  destruct HTb as (TP0 & _ & _ & _ & _ & _ & TLen & _ & TArr).
  pose proof (Int.unsigned_range_2 nb) as HN. change Int.max_unsigned with 4294967295 in HN.
  pose proof (extTappath_len e) as HPL.
  exists bD, oD, bE, 0, bE, 176.
  split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [change Ptrofs.max_unsigned with 18446744073709551615; lia|].
  split; [lia|]. split; [change Ptrofs.max_unsigned with 18446744073709551615; lia|].
  split; [exact R8|].
  split.
  { intros Hpos. rewrite Z.add_0_l. unfold te_path_value in TP0.
    destruct (Z.eq_dec (Int.unsigned nb) 0) as [E0|_]; [rewrite DLn in Hpos; lia|exact TP0]. }
  split.
  { rewrite Z.add_0_l, DLn, Z2Nat.id, Int.repr_unsigned by lia. exact TLen. }
  split; [|reflexivity].
  intros j h Hj. unfold hash_elem_rep. apply u32_of_nth. intros i Hi. rewrite hash256_len in Hi.
  rewrite <- (DP j h Hj).
  assert (Hjn : (j < Z.to_nat (Int.unsigned nb))%nat) by (rewrite <- DLn; apply nth_error_Some; congruence).
  apply TArr; assumption.
Qed.
