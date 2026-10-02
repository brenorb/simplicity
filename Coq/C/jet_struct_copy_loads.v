(** Preserve typed field observations across Clight's actual By_copy
    loadbytes/storebytes assignment, without modeling external memcpy. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Memory.
Require Import C.jet_frame_copy.
Import Values Mem ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma equal_loadbytes_parts m1 m2 b1 b2 base1 base2 n1 n2 bytes :
  0 <= n1 -> 0 <= n2 ->
  Mem.loadbytes m1 b1 base1 (n1 + n2) = Some bytes ->
  Mem.loadbytes m2 b2 base2 (n1 + n2) = Some bytes ->
  exists front tail,
    Mem.loadbytes m1 b1 base1 n1 = Some front /\ Mem.loadbytes m2 b2 base2 n1 = Some front /\
    Mem.loadbytes m1 b1 (base1 + n1) n2 = Some tail /\ Mem.loadbytes m2 b2 (base2 + n1) n2 = Some tail.
Proof.
  intros H1 H2 L1 L2.
  destruct (Mem.loadbytes_split m1 b1 base1 n1 n2 bytes L1 ltac:(lia) ltac:(lia)) as (a & b & LA & LB & E1).
  destruct (Mem.loadbytes_split m2 b2 base2 n1 n2 bytes L2 ltac:(lia) ltac:(lia)) as (c & d & LC & LD & E2).
  assert (Hlen : length a = length c) by (erewrite !Mem.loadbytes_length; eauto).
  destruct (equal_length_app_parts a b c d Hlen ltac:(congruence)) as [<- <-].
  exists a, b; auto.
Qed.

Theorem equal_loadbytes_field chunk m1 m2 b1 b2 base1 base2 n delta bytes v :
  0 <= delta -> delta + size_chunk chunk <= n ->
  Mem.loadbytes m1 b1 base1 n = Some bytes -> Mem.loadbytes m2 b2 base2 n = Some bytes ->
  (align_chunk chunk | base2 + delta) ->
  Mem.load chunk m1 b1 (base1 + delta) = Some v -> Mem.load chunk m2 b2 (base2 + delta) = Some v.
Proof.
  intros HD HN L1 L2 HA HL. pose proof (size_chunk_pos chunk) as HS.
  replace n with (delta + (n - delta)) in L1, L2 by ring.
  destruct (equal_loadbytes_parts m1 m2 b1 b2 base1 base2 delta (n - delta) bytes
    HD ltac:(lia) L1 L2) as (prefix & tail & LP1 & LP2 & LT1 & LT2).
  replace (n - delta) with (size_chunk chunk + (n - delta - size_chunk chunk)) in LT1, LT2 by ring.
  destruct (equal_loadbytes_parts m1 m2 b1 b2 (base1 + delta) (base2 + delta)
    (size_chunk chunk) (n - delta - size_chunk chunk) tail ltac:(lia) ltac:(lia) LT1 LT2)
    as (field & rest & LF1 & LF2 & LR1 & LR2).
  pose proof (Mem.loadbytes_load chunk m1 b1 (base1 + delta) field LF1
    (proj2 (Mem.load_valid_access _ _ _ _ _ HL))) as HV1.
  pose proof (Mem.loadbytes_load chunk m2 b2 (base2 + delta) field LF2 HA) as HV2.
  congruence.
Qed.
