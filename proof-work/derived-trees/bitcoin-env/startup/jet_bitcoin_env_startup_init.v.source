(** Program start of the environment unit (SHA unit + bitcoin/env.c +
    bitcoin/txEnv.c): the initial memory of the actual program satisfies
    [sha_started], the state the environment builders and the SHA jets
    require.  With [build_keeps_startup] and [free_keeps_startup] the state
    is thus established at start-up and kept through the real callers; it is
    not an assumption about the environment. *)
From compcert Require Import Coqlib Integers AST Ctypes Clight Globalenvs Values Memory.
Require Import C.jets_sha C.jet_sha_linkage C.jet_sha_block_local C.jet_sha_add_n_exec.
Require Import C.jet_bitcoin_make_tapleaf_exec.
Require Import JetStartup.jet_sha_startup_state.
Require Import C.jet_bitcoin_env_build C.jet_bitcoin_env_startup_kept.

Theorem env_unit_started m : Genv.init_mem jets_sha.prog = Some m -> sha_started m.
Proof.
  intros HInit.
  destruct (sha_startup_state_tapleaf m (sha_startup_state_initialized m HInit)) as [[Hd Hm] Ht].
  split; [exact Hd|]. split; [exact Hm|exact Ht].
Qed.
