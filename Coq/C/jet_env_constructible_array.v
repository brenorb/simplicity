(** The environment skeleton shared by both application units: an
    environment record pointing to a transaction record that holds an array
    pointer and its count, the current index, and the array of elements.
    Record sizes and the index offset are parameters. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Memory Values.
Require Import C.jet_env_constructible.
Import ListNotations.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 60.

Lemma env_array_built {X : Type} (xs : list X) (R : mem -> block -> Z -> X -> Prop)
    (esz tsz ixoff sz adelta cdelta : Z) (ixv : int64) (m0 : mem) :
  8 <= ixoff -> ixoff + 8 <= esz -> (8 | ixoff) ->
  0 <= sz -> (8 | sz) -> elem_local R sz -> elem_buildable 8 R sz ->
  0 <= adelta -> adelta + 8 <= tsz -> (8 | adelta) ->
  0 <= cdelta -> cdelta + 8 <= tsz -> (8 | cdelta) ->
  adelta + 8 <= cdelta \/ cdelta + 8 <= adelta ->
  exists m be bt bin,
    Mem.valid_block m be /\ Mem.valid_block m bt /\ Mem.valid_block m bin /\
    Mem.load Mptr m be 0 = Some (Vptr bt (Ptrofs.repr 0)) /\
    Mem.load Mint64 m be ixoff = Some (Vlong ixv) /\
    Mem.load Mptr m bt adelta = Some (Vptr bin (Ptrofs.repr 0)) /\
    Mem.load Mint64 m bt cdelta = Some (Vlong (Int64.repr (Z.of_nat (length xs)))) /\
    forall j x, nth_error xs j = Some x -> R m bin (0 + sz * Z.of_nat j) x.
Proof.
  intros Hx0 Hx1 Hxa Hsz Hal HL HB Ha0 Ha1 Haa Hc0 Hc1 Hca Hdis.
  destruct (three_blocks m0 esz tsz (sz * Z.of_nat (length xs)))
    as (m & be & bt & bin & Net & Nei & Nti & Ve & Vt & Vi & Pe & Pt & Pi).
  destruct (built_store_ptr m be 0 bt (Ptrofs.repr 0) 0 8 eq_refl) as (m1 & B1 & L1);
    [intros o Ho; apply Pe; lia|apply Z.divide_0_r|lia|lia|].
  destruct (built_store_int64 m1 be ixoff ixv ixoff (ixoff + 8)) as (m2 & B2 & L2);
    [eapply built_range_perm; [exact B1|]; intros o Ho; apply Pe; lia|exact Hxa|lia|lia|].
  destruct (built_store_ptr m2 bt adelta bin (Ptrofs.repr 0) adelta (adelta + 8) eq_refl) as (m3 & B3 & L3);
    [eapply built_range_perm; [exact B2|]; eapply built_range_perm; [exact B1|]; intros o Ho; apply Pt; lia
    |exact Haa|lia|lia|].
  destruct (built_store_int64 m3 bt cdelta (Int64.repr (Z.of_nat (length xs))) cdelta (cdelta + 8))
    as (m4 & B4 & L4);
    [eapply built_range_perm; [exact B3|]; eapply built_range_perm; [exact B2|];
     eapply built_range_perm; [exact B1|]; intros o Ho; apply Pt; lia|exact Hca|lia|lia|].
  destruct (array_buildable R sz Hsz Hal HL HB xs m4 bin 0) as (m5 & B5 & HR).
  { eapply built_range_perm; [exact B4|]. eapply built_range_perm; [exact B3|].
    eapply built_range_perm; [exact B2|]. eapply built_range_perm; [exact B1|]. exact Pi. }
  { apply Z.divide_0_r. }
  destruct B1 as (_ & _ & V1 & _). destruct B2 as (LB2 & _ & V2 & _). destruct B3 as (LB3 & _ & V3 & _).
  destruct B4 as (LB4 & _ & V4 & _). destruct B5 as (LB5 & _ & V5 & _).
  exists m5, be, bt, bin.
  split; [exact (V5 _ (V4 _ (V3 _ (V2 _ (V1 _ Ve)))))|].
  split; [exact (V5 _ (V4 _ (V3 _ (V2 _ (V1 _ Vt)))))|].
  split; [exact (V5 _ (V4 _ (V3 _ (V2 _ (V1 _ Vi)))))|].
  split.
  { rewrite (LB5 Mptr be 0) by (left; exact Nei). rewrite (LB4 Mptr be 0) by (left; exact Net).
    rewrite (LB3 Mptr be 0) by (left; exact Net).
    rewrite (LB2 Mptr be 0) by (right; left; change (size_chunk Mptr) with 8; lia). exact L1. }
  split.
  { rewrite (LB5 Mint64 be ixoff) by (left; exact Nei). rewrite (LB4 Mint64 be ixoff) by (left; exact Net).
    rewrite (LB3 Mint64 be ixoff) by (left; exact Net). exact L2. }
  split.
  { rewrite (LB5 Mptr bt adelta) by (left; exact Nti).
    rewrite (LB4 Mptr bt adelta) by (right; change (size_chunk Mptr) with 8; lia). exact L3. }
  split.
  { rewrite (LB5 Mint64 bt cdelta) by (left; exact Nti). exact L4. }
  exact HR.
Qed.
