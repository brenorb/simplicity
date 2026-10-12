(** The environment skeleton of [jet_env_constructible_array] with one more
    64-bit field in the transaction record (for relations that also read,
    e.g., the transaction version). *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Memory Values.
Require Import C.jet_env_constructible.
Import ListNotations.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 120.

Ltac keepx B :=
  rewrite (proj1 B) by
    (first [left; assumption | left; apply not_eq_sym; assumption
           | right; try change (size_chunk Mptr) with 8; cbn [size_chunk]; lia]).

Lemma env_array_built_x {X : Type} (xs : list X) (R : mem -> block -> Z -> X -> Prop)
    (esz tsz ixoff sz adelta cdelta xdelta : Z) (ixv xv : int64) (m0 : mem) :
  8 <= ixoff -> ixoff + 8 <= esz -> (8 | ixoff) ->
  0 <= sz -> (8 | sz) -> elem_local R sz -> elem_buildable 8 R sz ->
  0 <= adelta -> adelta + 8 <= tsz -> (8 | adelta) ->
  0 <= cdelta -> cdelta + 8 <= tsz -> (8 | cdelta) ->
  0 <= xdelta -> xdelta + 8 <= tsz -> (8 | xdelta) ->
  adelta + 8 <= cdelta \/ cdelta + 8 <= adelta ->
  adelta + 8 <= xdelta \/ xdelta + 8 <= adelta ->
  cdelta + 8 <= xdelta \/ xdelta + 8 <= cdelta ->
  exists m be bt bin,
    Mem.valid_block m be /\ Mem.valid_block m bt /\ Mem.valid_block m bin /\
    Mem.load Mptr m be 0 = Some (Vptr bt (Ptrofs.repr 0)) /\
    Mem.load Mint64 m be ixoff = Some (Vlong ixv) /\
    Mem.load Mptr m bt adelta = Some (Vptr bin (Ptrofs.repr 0)) /\
    Mem.load Mint64 m bt cdelta = Some (Vlong (Int64.repr (Z.of_nat (length xs)))) /\
    Mem.load Mint64 m bt xdelta = Some (Vlong xv) /\
    forall j x, nth_error xs j = Some x -> R m bin (0 + sz * Z.of_nat j) x.
Proof.
  intros Hx0 Hx1 Hxa Hsz Hal HL HB Ha0 Ha1 Haa Hc0 Hc1 Hca Hy0 Hy1 Hya Hd1 Hd2 Hd3.
  destruct (three_blocks m0 esz tsz (sz * Z.of_nat (length xs)))
    as (m & be & bt & bin & Net & Nei & Nti & Ve & Vt & Vi & Pe & Pt & Pi).
  destruct (built_store_ptr m be 0 bt (Ptrofs.repr 0) 0 8 eq_refl) as (m1 & B1 & L1);
    [intros o Ho; apply Pe; lia|apply Z.divide_0_r|lia|lia|].
  pose proof (built_range_perm _ _ _ _ _ be 0 esz Cur Writable B1 Pe) as Pe1.
  pose proof (built_range_perm _ _ _ _ _ bt 0 tsz Cur Writable B1 Pt) as Pt1.
  pose proof (built_range_perm _ _ _ _ _ bin 0 _ Cur Writable B1 Pi) as Pi1.
  destruct (built_store_int64 m1 be ixoff ixv ixoff (ixoff + 8)) as (m2 & B2 & L2);
    [intros o Ho; apply Pe1; lia|exact Hxa|lia|lia|].
  pose proof (built_range_perm _ _ _ _ _ bt 0 tsz Cur Writable B2 Pt1) as Pt2.
  pose proof (built_range_perm _ _ _ _ _ bin 0 _ Cur Writable B2 Pi1) as Pi2.
  destruct (built_store_ptr m2 bt adelta bin (Ptrofs.repr 0) adelta (adelta + 8) eq_refl) as (m3 & B3 & L3);
    [intros o Ho; apply Pt2; lia|exact Haa|lia|lia|].
  pose proof (built_range_perm _ _ _ _ _ bt 0 tsz Cur Writable B3 Pt2) as Pt3.
  pose proof (built_range_perm _ _ _ _ _ bin 0 _ Cur Writable B3 Pi2) as Pi3.
  destruct (built_store_int64 m3 bt cdelta (Int64.repr (Z.of_nat (length xs))) cdelta (cdelta + 8))
    as (m4 & B4 & L4); [intros o Ho; apply Pt3; lia|exact Hca|lia|lia|].
  pose proof (built_range_perm _ _ _ _ _ bt 0 tsz Cur Writable B4 Pt3) as Pt4.
  pose proof (built_range_perm _ _ _ _ _ bin 0 _ Cur Writable B4 Pi3) as Pi4.
  destruct (built_store_int64 m4 bt xdelta xv xdelta (xdelta + 8))
    as (m5 & B5 & L5); [intros o Ho; apply Pt4; lia|exact Hya|lia|lia|].
  pose proof (built_range_perm _ _ _ _ _ bin 0 _ Cur Writable B5 Pi4) as Pi5.
  destruct (array_buildable R sz Hsz Hal HL HB xs m5 bin 0 Pi5 (Z.divide_0_r 8)) as (m6 & B6 & HR).
  exists m6, be, bt, bin.
  split; [repeat match goal with B : built _ _ _ _ _ |- _ => apply (proj1 (proj2 (proj2 B))) end; exact Ve|].
  split; [repeat match goal with B : built _ _ _ _ _ |- _ => apply (proj1 (proj2 (proj2 B))) end; exact Vt|].
  split; [repeat match goal with B : built _ _ _ _ _ |- _ => apply (proj1 (proj2 (proj2 B))) end; exact Vi|].
  split. { keepx B6. keepx B5. keepx B4. keepx B3. keepx B2. exact L1. }
  split. { keepx B6. keepx B5. keepx B4. keepx B3. exact L2. }
  split. { keepx B6. keepx B5. keepx B4. exact L3. }
  split. { keepx B6. keepx B5. exact L4. }
  split. { keepx B6. exact L5. }
  exact HR.
Qed.
