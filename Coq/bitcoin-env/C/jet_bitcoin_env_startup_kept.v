(** The SHA start-up state through the actual environment callers: building
    the environment with the three real builders and releasing it with the
    two real free functions leaves the dispatch pointer, the maximum counter
    and the "TapLeaf" tag array as they were, so the state the SHA jets need
    ([sha_started], hence [sha_globals_ok]) survives the whole life cycle. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory.
Require Import C.jet_bitmachine_rep C.jets_sha C.jet_sha_linkage C.jet_sha_block_local C.jet_sha_uchars_exec.
Require Import C.jet_sha_add_n_exec C.jet_sha_ctx_abs C.jet_bitcoin_make_tapleaf_exec.
Require Import C.jet_bitcoin_env_build.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 120.

Notation TAG := (sha_symbol_block _tagName__1).

Lemma sha_started_valid m : sha_started m ->
  Mem.valid_block m GC /\ Mem.valid_block m GM /\ Mem.valid_block m TAG.
Proof.
  intros (Hd & Hm & Ht). split; [eapply load_valid_block; exact Hd|].
  split; [eapply load_valid_block; exact Hm|eapply load_valid_block; exact (Ht 0%nat ltac:(lia))].
Qed.

(** Any change that keeps the loads of the three global blocks. *)
Lemma sha_started_kept m m' :
  sha_started m ->
  (forall ch ofs, Mem.load ch m' GC ofs = Mem.load ch m GC ofs) ->
  (forall ch ofs, Mem.load ch m' GM ofs = Mem.load ch m GM ofs) ->
  (forall ch ofs, Mem.load ch m' TAG ofs = Mem.load ch m TAG ofs) ->
  sha_started m'.
Proof.
  intros (Hd & Hm & Ht) L1 L2 L3. split; [unfold sha_dispatch_ok; rewrite L1; exact Hd|].
  split; [rewrite L2; exact Hm|]. intros i Hi. rewrite L3. apply Ht, Hi.
Qed.

Lemma sha_started_globals m : sha_started m -> sha_globals_ok m.
Proof. intros (Hd & Hm & _). split; assumption. Qed.

(** After [build_environment] (its frame conclusion), for a destination
    outside the three global blocks. *)
Theorem build_keeps_startup m m3 bD oD :
  sha_started m ->
  (forall ch b ofs, Mem.valid_block m b -> (b <> bD \/ ofs + size_chunk ch <= oD \/ oD + 56 <= ofs) ->
     Mem.load ch m3 b ofs = Mem.load ch m b ofs) ->
  GC <> bD -> GM <> bD -> TAG <> bD ->
  sha_started m3.
Proof.
  intros HS HL N1 N2 N3. destruct (sha_started_valid m HS) as (V1 & V2 & V3).
  apply (sha_started_kept m m3 HS); intros ch ofs; apply HL; auto.
Qed.

(** After [free_environment] (its load conclusion): the freed blocks were
    allocated by the builders, hence are not the global blocks. *)
Theorem free_keeps_startup m0 m m2 bT bE :
  sha_started m ->
  Mem.valid_block m0 GC -> Mem.valid_block m0 GM -> Mem.valid_block m0 TAG ->
  ~ Mem.valid_block m0 bT -> ~ Mem.valid_block m0 bE ->
  (forall ch b ofs, b <> bT -> b <> bE -> Mem.load ch m2 b ofs = Mem.load ch m b ofs) ->
  sha_started m2.
Proof.
  intros HS V1 V2 V3 FT FE HL.
  apply (sha_started_kept m m2 HS); intros ch ofs; apply HL; intros E; subst; contradiction.
Qed.
