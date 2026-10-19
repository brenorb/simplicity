(** Every logical Bitcoin environment has a representing C memory for the
    lock-distance relation (transaction pointer, input array with sequence
    numbers, input count, version, current index), and the four registered
    distance jets run for every environment and input with no memory, frame
    or environment premise. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Memory Values Events Ctypes Clight ClightBigstep.
Require Import Simplicity.Ty Simplicity.BitMachine Simplicity.Translate Simplicity.Primitive.Bitcoin.
Require Import C.jet_application_contract C.jet_application_sep C.jet_application_partial.
Require Import C.jet_frame_constructible_app C.jet_env_constructible C.jet_env_constructible_array_x.
Require Import C.jet_bitcoin_linkage C.jet_bitcoin_env_constructible C.jet_bitcoin_env_constructible_indexed.
Require Import C.jet_bitcoin_distance_local C.jet_bitcoin_check_distance C.jet_app_executable_registry.
Import ListNotations.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 120.

Lemma bitcoin_distance_env_rep_constructible (e : Bitcoin.env) :
  exists m env, bitcoin_distance_env_rep m env e.
Proof.
  destruct (bitcoin_inputs_fit e 160 ltac:(lia)) as [Hs Hn].
  pose proof (Bitcoin.envIxBounded e) as Hix.
  destruct (env_array_built_x (sigTxIn (Bitcoin.envTx e))
    (fun m b ofs (x : sigTxInput) =>
      Mem.load Mint64 m b (ofs + 144) = Some (Vlong (Int64.repr (Int.unsigned (sigTxiSequence x)))))
    56 488 48 160 0 448 464
    (Int64.repr (Z.of_nat (Bitcoin.envIx e)))
    (Int64.repr (Int.unsigned (sigTxVersion (Bitcoin.envTx e)))) Mem.empty)
    as (m & be & bt & bin & Ve & Vt & Vi & L1 & L2 & L3 & L4 & L5 & HR);
    try lia; try divides; try (left; lia).
  - eapply elem_local_larger;
      [|apply (elem_local_shift (fun m b ofs (x : sigTxInput) =>
          Mem.load Mint64 m b ofs = Some (Vlong (Int64.repr (Int.unsigned (sigTxiSequence x))))) 8 144
          ltac:(lia));
        apply (load_local Mint64
          (fun x : sigTxInput => Vlong (Int64.repr (Int.unsigned (sigTxiSequence x)))))]. lia.
  - eapply elem_buildable_larger;
      [|apply (elem_buildable_shift 8 (fun m b ofs (x : sigTxInput) =>
          Mem.load Mint64 m b ofs = Some (Vlong (Int64.repr (Int.unsigned (sigTxiSequence x))))) 8 144
          ltac:(lia) ltac:(divides));
        apply (int64_buildable (fun x : sigTxInput => Int64.repr (Int.unsigned (sigTxiSequence x))))]. lia.
  - exists m, (Vptr be (Ptrofs.repr 0)).
    exists be, 0, bt, 0, bin, 0, (Int64.repr (Z.of_nat (length (sigTxIn (Bitcoin.envTx e))))),
      (Int64.repr (Z.of_nat (Bitcoin.envIx e))),
      (Int64.repr (Int.unsigned (sigTxVersion (Bitcoin.envTx e)))).
    rewrite ?ptrofs_max; repeat split;
      first [reflexivity | lia | assumption | exact HR
            | (apply repr_small; lia) | (apply repr_small; apply int_small)].
Qed.

Theorem bitcoin_tx_lock_distance_runs_everywhere :
  ltac:(statement bitcoin_tx_lock_distance_local_spec_executable).
Proof.
  exact (plain_runs_everywhere _ _ _ _ _ bitcoin_tx_lock_distance_local_spec_executable
    bitcoin_distance_env_rep_constructible).
Qed.

Theorem bitcoin_tx_lock_duration_runs_everywhere :
  ltac:(statement bitcoin_tx_lock_duration_local_spec_executable).
Proof.
  exact (plain_runs_everywhere _ _ _ _ _ bitcoin_tx_lock_duration_local_spec_executable
    bitcoin_distance_env_rep_constructible).
Qed.

Theorem bitcoin_check_lock_distance_runs_everywhere :
  ltac:(statement bitcoin_check_lock_distance_local_spec_executable).
Proof.
  exact (partial_runs_everywhere _ _ _ _ _ bitcoin_check_lock_distance_local_spec_executable
    bitcoin_distance_env_rep_constructible).
Qed.

Theorem bitcoin_check_lock_duration_runs_everywhere :
  ltac:(statement bitcoin_check_lock_duration_local_spec_executable).
Proof.
  exact (partial_runs_everywhere _ _ _ _ _ bitcoin_check_lock_duration_local_spec_executable
    bitcoin_distance_env_rep_constructible).
Qed.
