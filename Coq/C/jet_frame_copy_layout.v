(** The actual by-value frame copy, with a source at any aligned byte offset. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Memory.
Require Import C.jet_frame_copy.
Import Values Mem ListNotations.
Local Open Scope Z_scope.

Lemma frame_loadbytes_at m bs base edge offset :
  Mem.load Mptr m bs base = Some edge ->
  Mem.load Mint64 m bs (base + 8) = Some offset ->
  exists bytes, Mem.loadbytes m bs base 16 = Some bytes.
Proof.
  intros HE HO.
  destruct (Mem.load_loadbytes _ _ _ _ _ HE) as [a [HA _]].
  destruct (Mem.load_loadbytes _ _ _ _ _ HO) as [b [HB _]].
  exists (a ++ b).
  apply (Mem.loadbytes_concat m bs base 8 8 a b); try assumption; lia.
Qed.

Lemma frame_copy_fields_at m mf bs base bl bytes edge offset :
  Mem.loadbytes m bs base 16 = Some bytes ->
  Mem.storebytes m bl 0 bytes = Some mf ->
  Mem.load Mptr m bs base = Some edge ->
  Mem.load Mint64 m bs (base + 8) = Some offset ->
  Mem.load Mptr mf bl 0 = Some edge /\
  Mem.load Mint64 mf bl 8 = Some offset.
Proof.
  intros HB HS HE HO.
  pose proof (Mem.loadbytes_length _ _ _ _ _ HB) as Hlen.
  pose proof (Mem.loadbytes_storebytes_same _ _ _ _ _ HS) as HD.
  rewrite Hlen in HD.
  change (Mem.loadbytes mf bl 0 16 = Some bytes) in HD.
  destruct (Mem.loadbytes_split m bs base 8 8 bytes HB ltac:(lia) ltac:(lia))
    as [a [b [HA [HB' Hab]]]].
  destruct (Mem.loadbytes_split mf bl 0 8 8 bytes HD ltac:(lia) ltac:(lia))
    as [c [d [HC [HD' Hcd]]]].
  assert (length a = length c) as Hac.
  { pose proof (Mem.loadbytes_length _ _ _ _ _ HA).
    pose proof (Mem.loadbytes_length _ _ _ _ _ HC). congruence. }
  destruct (equal_length_app_parts a b c d Hac ltac:(congruence)) as [<- <-].
  pose proof (proj2 (Mem.load_valid_access _ _ _ _ _ HE)) as AE.
  pose proof (proj2 (Mem.load_valid_access _ _ _ _ _ HO)) as AO.
  pose proof (Mem.loadbytes_load Mptr m bs base a HA AE).
  assert (AE0 : (align_chunk Mptr | 0)) by (exists 0; reflexivity).
  assert (AO8 : (align_chunk Mint64 | 8)) by (exists 1; reflexivity).
  pose proof (Mem.loadbytes_load Mptr mf bl 0 a HC AE0).
  pose proof (Mem.loadbytes_load Mint64 m bs (base + 8) b HB' AO).
  pose proof (Mem.loadbytes_load Mint64 mf bl 8 b HD' AO8).
  split; congruence.
Qed.
