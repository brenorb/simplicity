(** Byte-copy facts for the actual 64-bit [frameItem] layout. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Memory.
Import Values Mem ListNotations.
Local Open Scope Z_scope.

Lemma equal_length_app_parts {A : Type} (a b c d : list A) :
  length a = length c -> a ++ b = c ++ d -> a = c /\ b = d.
Proof.
  revert c. induction a as [|x a IH]; intros [|y c] Hlen Heq;
    simpl in *; try discriminate.
  - auto.
  - injection Heq as Hxy Heq. subst y.
    destruct (IH c ltac:(lia) Heq) as [-> ->]. auto.
Qed.

Lemma frame_loadbytes m bs edge offset :
  Mem.load Mptr m bs 0 = Some edge ->
  Mem.load Mint64 m bs 8 = Some offset ->
  exists bytes, Mem.loadbytes m bs 0 16 = Some bytes.
Proof.
  intros HE HO.
  destruct (Mem.load_loadbytes _ _ _ _ _ HE) as [a [HA _]].
  destruct (Mem.load_loadbytes _ _ _ _ _ HO) as [b [HB _]].
  exists (a ++ b).
  apply (Mem.loadbytes_concat m bs 0 8 8 a b); try assumption; lia.
Qed.

Lemma frame_copy_fields m m' bs bl bytes edge offset :
  Mem.loadbytes m bs 0 16 = Some bytes ->
  Mem.storebytes m bl 0 bytes = Some m' ->
  Mem.load Mptr m bs 0 = Some edge ->
  Mem.load Mint64 m bs 8 = Some offset ->
  Mem.load Mptr m' bl 0 = Some edge /\
  Mem.load Mint64 m' bl 8 = Some offset.
Proof.
  intros HB HS HE HO.
  pose proof (Mem.loadbytes_length _ _ _ _ _ HB) as Hlen.
  pose proof (Mem.loadbytes_storebytes_same _ _ _ _ _ HS) as HD.
  rewrite Hlen in HD.
  change (Mem.loadbytes m' bl 0 16 = Some bytes) in HD.
  destruct (Mem.loadbytes_split m bs 0 8 8 bytes HB ltac:(lia) ltac:(lia))
    as [a [b [HA [HB' Hab]]]].
  destruct (Mem.loadbytes_split m' bl 0 8 8 bytes HD ltac:(lia) ltac:(lia))
    as [c [d [HC [HD' Hcd]]]].
  assert (length a = length c) as Hac.
  { pose proof (Mem.loadbytes_length _ _ _ _ _ HA).
    pose proof (Mem.loadbytes_length _ _ _ _ _ HC). congruence. }
  destruct (equal_length_app_parts a b c d Hac ltac:(congruence)) as [<- <-].
  pose proof (proj2 (Mem.load_valid_access _ _ _ _ _ HE)) as AE.
  pose proof (proj2 (Mem.load_valid_access _ _ _ _ _ HO)) as AO.
  pose proof (Mem.loadbytes_load Mptr m bs 0 a HA AE).
  pose proof (Mem.loadbytes_load Mptr m' bl 0 a HC AE).
  pose proof (Mem.loadbytes_load Mint64 m bs 8 b HB' AO).
  pose proof (Mem.loadbytes_load Mint64 m' bl 8 b HD' AO).
  split; congruence.
Qed.
