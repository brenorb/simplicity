(** The environment builders for the memcpy-linked environment unit.

    In this derived tree [C.jets_sha] is the environment unit
    ([C/jets_bitcoin_env.v]) in which the external declaration of [memcpy]
    is replaced by the internal definition generated from
    [jet_memcpy_exact.c], and [memcpy_model] is the theorem
    [memcpy_model_holds] of the linked model.  Every proof source of
    [bitcoin-env/C] is compiled unchanged against that program, so the
    builder theorems hold for it without the [memcpy_model] premise.  As for
    the linked jets ([Coq/linked/README.md]), this is a statement about the
    C code linked with the reference [memcpy], not about the unit with an
    external [memcpy]. *)
Require Import C.jet_memcpy_model.
Require Import C.jet_bitcoin_env_hashbuffer C.jet_bitcoin_env_copyinput C.jet_bitcoin_env_copyoutput.
Require Import C.jet_bitcoin_env_tapenv C.jet_bitcoin_env_tx C.jet_bitcoin_env_txenv.
Require Import C.jet_bitcoin_env_tapenv_raw C.jet_bitcoin_env_tx_raw.
Require Import C.jet_bitcoin_env_build C.jet_bitcoin_env_raw_exists.

Definition eval_mallocTapEnv_linked := eval_mallocTapEnv memcpy_model_holds.
Definition eval_mallocTransaction_linked := eval_mallocTransaction memcpy_model_holds.
Definition eval_build_txEnv_linked := eval_build_txEnv memcpy_model_holds.
Definition mallocTapEnv_raw_cached_hashes_linked := mallocTapEnv_raw_cached_hashes memcpy_model_holds.
Definition mallocTransaction_raw_cached_hashes_linked := mallocTransaction_raw_cached_hashes memcpy_model_holds.
Definition build_environment_linked := build_environment memcpy_model_holds.
Definition build_environment_readable_linked := build_environment_readable memcpy_model_holds.
