(** Building C memories that represent logical environments.

    The application-jet contracts take an environment relation as a premise:
    the C environment holds the values the canonical primitives denote.  This
    module provides the generic construction steps (stores into freshly
    allocated blocks, word arrays, arrays of structured elements) from which
    such a memory is built for every logical environment, so that those
    premises are satisfiable on the whole domain.  Independent of any
    translation unit. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Memory Values.
Require Import C.jet_uint32_array_init.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 60.

(** [m'] differs from [m] at most in the contents of [b] within [lo, hi). *)
Definition built (m m' : mem) (b : block) (lo hi : Z) : Prop :=
  (forall c b' o, b' <> b \/ o + size_chunk c <= lo \/ hi <= o ->
    Mem.load c m' b' o = Mem.load c m b' o) /\
  (forall b' o k p, Mem.perm m b' o k p -> Mem.perm m' b' o k p) /\
  (forall b', Mem.valid_block m b' -> Mem.valid_block m' b') /\
  (forall b' o k p, Mem.perm m' b' o k p -> Mem.perm m b' o k p).

Lemma built_refl m b lo hi : built m m b lo hi.
Proof. repeat split; auto. Qed.

Lemma built_weaken m m' b lo hi lo' hi' :
  lo' <= lo -> hi <= hi' -> built m m' b lo hi -> built m m' b lo' hi'.
Proof.
  intros H1 H2 (L & P & V & Q). split; [|split; [|split]; assumption].
  intros c b' o H. apply L. destruct H as [H|[H|H]]; [left; exact H|right; left; lia|right; right; lia].
Qed.

Lemma built_trans m m1 m2 b lo hi :
  built m m1 b lo hi -> built m1 m2 b lo hi -> built m m2 b lo hi.
Proof.
  intros (L1 & P1 & V1 & Q1) (L2 & P2 & V2 & Q2). split; [|split; [|split]].
  - intros c b' o H. rewrite (L2 c b' o H). exact (L1 c b' o H).
  - intros b' o k p H. exact (P2 _ _ _ _ (P1 _ _ _ _ H)).
  - intros b' H. exact (V2 _ (V1 _ H)).
  - intros b' o k p H. exact (Q1 _ _ _ _ (Q2 _ _ _ _ H)).
Qed.

(** A step on another block is a (trivial) step on any range of this one. *)
Lemma built_other m m' b b' lo hi :
  b <> b' -> built m m' b lo hi ->
  (forall c o, Mem.load c m' b' o = Mem.load c m b' o) /\
  (forall o k p, Mem.perm m b' o k p -> Mem.perm m' b' o k p).
Proof.
  intros Hb (L & P & V & Q). split.
  - intros c o. apply L. left. exact (not_eq_sym Hb).
  - intros o k p H. exact (P _ _ _ _ H).
Qed.

Lemma built_range_perm m m' b lo hi b' l h k p :
  built m m' b lo hi -> Mem.range_perm m b' l h k p -> Mem.range_perm m' b' l h k p.
Proof. intros (_ & P & _ & _) H o Ho. exact (P _ _ _ _ (H o Ho)). Qed.

Lemma built_load_some m m' b lo hi c b' o v :
  built m m' b lo hi -> b' <> b \/ o + size_chunk c <= lo \/ hi <= o ->
  Mem.load c m b' o = Some v -> Mem.load c m' b' o = Some v.
Proof. intros (L & _) H HL. rewrite (L c b' o H). exact HL. Qed.

Lemma built_store m b c o v lo hi :
  Mem.range_perm m b o (o + size_chunk c) Cur Writable -> (align_chunk c | o) ->
  lo <= o -> o + size_chunk c <= hi ->
  exists m', built m m' b lo hi /\ Mem.load c m' b o = Some (Val.load_result c v).
Proof.
  intros HP HA Hlo Hhi.
  destruct (Mem.valid_access_store m c b o v (conj HP HA)) as [m' HS].
  exists m'. split; [|exact (Mem.load_store_same _ _ _ _ _ _ HS)].
  split; [|split; [|split]].
  - intros c' b' o' H. eapply Mem.load_store_other; [exact HS|].
    destruct H as [H|[H|H]]; [left; exact H|right; left; lia|right; right; lia].
  - intros b' o' k p H. eapply Mem.perm_store_1; eauto.
  - intros b' H. eapply Mem.store_valid_block_1; eauto.
  - intros b' o' k p H. eapply Mem.perm_store_2; eauto.
Qed.

(** Eight-bit, 32-bit, 64-bit and pointer cells store their value exactly. *)
Lemma built_store_int32 m b o (x : int) lo hi :
  Mem.range_perm m b o (o + 4) Cur Writable -> (4 | o) -> lo <= o -> o + 4 <= hi ->
  exists m', built m m' b lo hi /\ Mem.load Mint32 m' b o = Some (Vint x).
Proof. intros HP HA Hlo Hhi. exact (built_store m b Mint32 o (Vint x) lo hi HP HA Hlo Hhi). Qed.

Lemma built_store_int64 m b o (x : int64) lo hi :
  Mem.range_perm m b o (o + 8) Cur Writable -> (8 | o) -> lo <= o -> o + 8 <= hi ->
  exists m', built m m' b lo hi /\ Mem.load Mint64 m' b o = Some (Vlong x).
Proof. intros HP HA Hlo Hhi. exact (built_store m b Mint64 o (Vlong x) lo hi HP HA Hlo Hhi). Qed.

Lemma built_store_ptr m b o (b' : block) (p : ptrofs) lo hi :
  Archi.ptr64 = true ->
  Mem.range_perm m b o (o + 8) Cur Writable -> (8 | o) -> lo <= o -> o + 8 <= hi ->
  exists m', built m m' b lo hi /\ Mem.load Mptr m' b o = Some (Vptr b' p).
Proof.
  intros H64 HP HA Hlo Hhi.
  assert (HM : Mptr = Mint64) by (unfold Mptr; rewrite H64; reflexivity).
  rewrite HM.
  destruct (built_store m b Mint64 o (Vptr b' p) lo hi HP HA Hlo Hhi) as (m' & HB & HL).
  exists m'. split; [exact HB|]. rewrite HL. cbn. rewrite H64. reflexivity.
Qed.

Lemma built_store_bool m b o (v : bool) lo hi :
  Mem.range_perm m b o (o + 1) Cur Writable -> lo <= o -> o + 1 <= hi ->
  exists m', built m m' b lo hi /\
    Mem.load Mint8unsigned m' b o = Some (Vint (if v then Int.one else Int.zero)).
Proof.
  intros HP Hlo Hhi.
  destruct (built_store m b Mint8unsigned o (Vint (if v then Int.one else Int.zero)) lo hi HP
    (Z.divide_1_l o) Hlo Hhi) as (m' & HB & HL).
  exists m'. split; [exact HB|]. rewrite HL. destruct v; reflexivity.
Qed.

(** A word array. *)
Lemma built_uint32_array (xs : list int) : forall m b ofs,
  Mem.range_perm m b ofs (ofs + 4 * Z.of_nat (length xs)) Cur Writable -> (4 | ofs) ->
  exists m', built m m' b ofs (ofs + 4 * Z.of_nat (length xs)) /\ uint32_array_at m' b ofs xs.
Proof.
  induction xs as [|x t IH]; intros m b ofs HP HA.
  - exists m. split; [apply built_refl|]. intros i w Hi. destruct i; discriminate.
  - cbn [length] in *. rewrite Nat2Z.inj_succ in *.
    destruct (built_store_int32 m b ofs x ofs (ofs + 4 * Z.succ (Z.of_nat (length t))))
      as (m1 & HB1 & HL1); [intros o Ho; apply HP; lia|exact HA|lia|lia|].
    destruct (IH m1 b (ofs + 4)) as (m2 & HB2 & HA2).
    { eapply built_range_perm; [exact HB1|]. intros o Ho. apply HP. lia. }
    { apply Z.divide_add_r; [exact HA|apply Z.divide_refl]. }
    exists m2. split.
    + eapply built_trans; [exact HB1|].
      eapply built_weaken; [| |exact HB2]; lia.
    + intros i w Hi. destruct i as [|i].
      * cbn in Hi. inversion Hi; subst w. rewrite Z.mul_0_r, Z.add_0_r.
        eapply built_load_some; [exact HB2| |exact HL1]. right; left. cbn. lia.
      * cbn in Hi. rewrite Nat2Z.inj_succ.
        replace (ofs + 4 * Z.succ (Z.of_nat i)) with (ofs + 4 + 4 * Z.of_nat i) by lia.
        exact (HA2 i w Hi).
Qed.

(** * Structured elements *)

(** [rep] at [ofs] depends only on successful loads within [ofs, ofs+psz). *)
Definition elem_local {X : Type} (rep : mem -> block -> Z -> X -> Prop) (psz : Z) : Prop :=
  forall m1 m2 b ofs x, rep m1 b ofs x ->
    (forall c o v, ofs <= o -> o + size_chunk c <= ofs + psz ->
      Mem.load c m1 b o = Some v -> Mem.load c m2 b o = Some v) -> rep m2 b ofs x.

(** [rep] can be established at any [al]-aligned writable place of size [psz]. *)
Definition elem_buildable {X : Type} (al : Z) (rep : mem -> block -> Z -> X -> Prop) (psz : Z) : Prop :=
  forall x m b ofs, Mem.range_perm m b ofs (ofs + psz) Cur Writable -> (al | ofs) ->
    exists m', built m m' b ofs (ofs + psz) /\ rep m' b ofs x.

Lemma elem_buildable_align {X : Type} al al' (rep : mem -> block -> Z -> X -> Prop) psz :
  (al | al') -> elem_buildable al rep psz -> elem_buildable al' rep psz.
Proof.
  intros Hd HB x m b ofs HP HA. exact (HB x m b ofs HP (Z.divide_trans _ _ _ Hd HA)).
Qed.

Lemma elem_local_built {X : Type} (rep : mem -> block -> Z -> X -> Prop) psz m m' b lo hi b' ofs x :
  elem_local rep psz -> built m m' b lo hi ->
  b' <> b \/ ofs + psz <= lo \/ hi <= ofs ->
  rep m b' ofs x -> rep m' b' ofs x.
Proof.
  intros HL HB Hd Hr. eapply HL; [exact Hr|].
  intros c o v H1 H2 Hl. eapply built_load_some; [exact HB| |exact Hl].
  destruct Hd as [H|[H|H]]; [left; exact H|right; left; lia|right; right].
  pose proof (size_chunk_pos c). lia.
Qed.

Lemma elem_buildable_impl {X : Type} al (rep rep' : mem -> block -> Z -> X -> Prop) psz :
  (forall m b ofs x, rep m b ofs x -> rep' m b ofs x) ->
  elem_buildable al rep psz -> elem_buildable al rep' psz.
Proof.
  intros HI HB x m b ofs HP HA. destruct (HB x m b ofs HP HA) as (m' & H1 & H2).
  exists m'. split; [exact H1|exact (HI _ _ _ _ H2)].
Qed.

Lemma elem_buildable_larger {X : Type} al (rep : mem -> block -> Z -> X -> Prop) psz psz' :
  psz <= psz' -> elem_buildable al rep psz -> elem_buildable al rep psz'.
Proof.
  intros Hle HB x m b ofs HP HA.
  destruct (HB x m b ofs ltac:(intros o Ho; apply HP; lia) HA) as (m' & H1 & H2).
  exists m'. split; [eapply built_weaken; [| |exact H1]; lia|exact H2].
Qed.

Lemma elem_local_larger {X : Type} (rep : mem -> block -> Z -> X -> Prop) psz psz' :
  psz <= psz' -> elem_local rep psz -> elem_local rep psz'.
Proof.
  intros Hle HL m1 m2 b ofs x Hr Hl. eapply HL; [exact Hr|].
  intros c o v H1 H2. apply Hl; lia.
Qed.

(** The element placed [off] bytes into a record. *)
Lemma elem_buildable_shift {X : Type} al (rep : mem -> block -> Z -> X -> Prop) psz off :
  0 <= off -> (al | off) -> elem_buildable al rep psz ->
  elem_buildable al (fun m b ofs x => rep m b (ofs + off) x) (off + psz).
Proof.
  intros H0 Ha HB x m b ofs HP HA.
  destruct (HB x m b (ofs + off)) as (m' & H1 & H2).
  { intros o Ho. apply HP. lia. }
  { apply Z.divide_add_r; assumption. }
  exists m'. split; [eapply built_weaken; [| |exact H1]; lia|exact H2].
Qed.

Lemma elem_local_shift {X : Type} (rep : mem -> block -> Z -> X -> Prop) psz off :
  0 <= off -> elem_local rep psz ->
  elem_local (fun m b ofs x => rep m b (ofs + off) x) (off + psz).
Proof.
  intros H0 HL m1 m2 b ofs x Hr Hl. eapply HL; [exact Hr|].
  intros c o v H1 H2. apply Hl; lia.
Qed.

(** Two parts of a record at disjoint places. *)
Lemma elem_buildable_pair {X : Type} al (rep1 rep2 : mem -> block -> Z -> X -> Prop) off1 psz1 off2 psz2 psz :
  0 <= off1 -> (al | off1) -> off1 + psz1 <= off2 -> (al | off2) -> off2 + psz2 <= psz ->
  0 <= psz1 -> 0 <= psz2 ->
  elem_local rep1 psz1 -> elem_buildable al rep1 psz1 -> elem_buildable al rep2 psz2 ->
  elem_buildable al (fun m b ofs x => rep1 m b (ofs + off1) x /\ rep2 m b (ofs + off2) x) psz.
Proof.
  intros H0 Ha1 Hd Ha2 Hin Hp1 Hp2 HL1 HB1 HB2 x m b ofs HP HA.
  destruct (HB1 x m b (ofs + off1)) as (m1 & HBu1 & Hr1).
  { intros o Ho. apply HP. lia. }
  { apply Z.divide_add_r; assumption. }
  destruct (HB2 x m1 b (ofs + off2)) as (m2 & HBu2 & Hr2).
  { eapply built_range_perm; [exact HBu1|]. intros o Ho. apply HP. lia. }
  { apply Z.divide_add_r; assumption. }
  exists m2. split; [|split; [|exact Hr2]].
  - eapply built_trans; (eapply built_weaken; [| |eassumption]; lia).
  - eapply elem_local_built; [exact HL1|exact HBu2| |exact Hr1]. right; left. lia.
Qed.

Lemma elem_local_pair {X : Type} (rep1 rep2 : mem -> block -> Z -> X -> Prop) off1 psz1 off2 psz2 psz :
  0 <= off1 -> off1 + psz1 <= psz -> 0 <= off2 -> off2 + psz2 <= psz ->
  elem_local rep1 psz1 -> elem_local rep2 psz2 ->
  elem_local (fun m b ofs x => rep1 m b (ofs + off1) x /\ rep2 m b (ofs + off2) x) psz.
Proof.
  intros H1 H1' H2 H2' HL1 HL2 m1 m2 b ofs x [Hr1 Hr2] Hl. split.
  - eapply HL1; [exact Hr1|]. intros c o v Ha Hb. apply Hl; lia.
  - eapply HL2; [exact Hr2|]. intros c o v Ha Hb. apply Hl; lia.
Qed.

(** A part that is only required for some values. *)
Lemma elem_buildable_option {X Y : Type} al (g : X -> option Y) (rep : mem -> block -> Z -> Y -> Prop) psz :
  0 <= psz -> elem_buildable al rep psz ->
  elem_buildable al (fun m b ofs x => forall y, g x = Some y -> rep m b ofs y) psz.
Proof.
  intros Hp HB x m b ofs HP HA. destruct (g x) as [y|] eqn:Hg.
  - destruct (HB y m b ofs HP HA) as (m' & H1 & H2). exists m'. split; [exact H1|].
    intros y' Hy. inversion Hy; subst y'. exact H2.
  - exists m. split; [apply built_refl|]. intros y Hy. discriminate.
Qed.

Lemma elem_local_option {X Y : Type} (g : X -> option Y) (rep : mem -> block -> Z -> Y -> Prop) psz :
  elem_local rep psz ->
  elem_local (fun m b ofs x => forall y, g x = Some y -> rep m b ofs y) psz.
Proof.
  intros HL m1 m2 b ofs x Hr Hl y Hy. eapply HL; [exact (Hr y Hy)|exact Hl].
Qed.

(** Basic parts: a word array and single cells. *)
Lemma words_buildable {X : Type} (W : X -> list int) :
  (forall x, length (W x) = 8%nat) ->
  elem_buildable 4 (fun m b ofs x => uint32_array_at m b ofs (W x)) 32.
Proof.
  intros HW x m b ofs HP HA.
  destruct (built_uint32_array (W x) m b ofs) as (m' & H1 & H2).
  { rewrite HW. exact HP. }
  { exact HA. }
  exists m'. rewrite HW in H1. split; [exact H1|exact H2].
Qed.

Lemma words_local {X : Type} (W : X -> list int) :
  (forall x, length (W x) = 8%nat) ->
  elem_local (fun m b ofs x => uint32_array_at m b ofs (W x)) 32.
Proof.
  intros HW m1 m2 b ofs x Hr Hl i w Hi.
  assert (Hi8 : (i < 8)%nat) by (rewrite <- (HW x); apply nth_error_Some; rewrite Hi; discriminate).
  apply Hl; [lia|change (size_chunk Mint32) with 4; lia|exact (Hr i w Hi)].
Qed.

Lemma int32_buildable {X : Type} (v : X -> int) :
  elem_buildable 4 (fun m b ofs x => Mem.load Mint32 m b ofs = Some (Vint (v x))) 4.
Proof.
  intros x m b ofs HP HA.
  exact (built_store_int32 m b ofs (v x) ofs (ofs + 4) HP HA ltac:(lia) ltac:(lia)).
Qed.

Lemma int64_buildable {X : Type} (v : X -> int64) :
  elem_buildable 8 (fun m b ofs x => Mem.load Mint64 m b ofs = Some (Vlong (v x))) 8.
Proof.
  intros x m b ofs HP HA.
  exact (built_store_int64 m b ofs (v x) ofs (ofs + 8) HP HA ltac:(lia) ltac:(lia)).
Qed.

Lemma bool_buildable {X : Type} (v : X -> bool) :
  elem_buildable 1 (fun m b ofs x =>
    Mem.load Mint8unsigned m b ofs = Some (Vint (if v x then Int.one else Int.zero))) 1.
Proof.
  intros x m b ofs HP HA.
  exact (built_store_bool m b ofs (v x) ofs (ofs + 1) HP ltac:(lia) ltac:(lia)).
Qed.

Lemma load_local {X : Type} (c : memory_chunk) (v : X -> val) :
  elem_local (fun m b ofs x => Mem.load c m b ofs = Some (v x)) (size_chunk c).
Proof. intros m1 m2 b ofs x Hr Hl. apply Hl; [lia|lia|exact Hr]. Qed.

(** An array of elements of size [sz]. *)
Lemma array_buildable {X : Type} (rep : mem -> block -> Z -> X -> Prop) (sz : Z) :
  0 <= sz -> (8 | sz) -> elem_local rep sz -> elem_buildable 8 rep sz ->
  forall (xs : list X) m b base,
    Mem.range_perm m b base (base + sz * Z.of_nat (length xs)) Cur Writable -> (8 | base) ->
    exists m', built m m' b base (base + sz * Z.of_nat (length xs)) /\
      forall j x, nth_error xs j = Some x -> rep m' b (base + sz * Z.of_nat j) x.
Proof.
  intros Hsz Hal HL HB xs. induction xs as [|x t IH]; intros m b base HP HA.
  - exists m. split; [apply built_refl|]. intros j x Hj. destruct j; discriminate.
  - cbn [length] in *. rewrite Nat2Z.inj_succ in *.
    assert (Ht : 0 <= sz * Z.of_nat (length t)) by (apply Z.mul_nonneg_nonneg; lia).
    destruct (HB x m b base) as (m1 & HB1 & Hr1); [intros o Ho; apply HP; lia|exact HA|].
    destruct (IH m1 b (base + sz)) as (m2 & HB2 & Hr2).
    { eapply built_range_perm; [exact HB1|]. intros o Ho. apply HP. lia. }
    { apply Z.divide_add_r; assumption. }
    exists m2. split.
    + eapply built_trans; (eapply built_weaken; [| |eassumption]; lia).
    + intros j y Hj. destruct j as [|j].
      * cbn in Hj. inversion Hj; subst y. rewrite Z.mul_0_r, Z.add_0_r.
        eapply elem_local_built; [exact HL|exact HB2| |exact Hr1]. right; left. lia.
      * cbn in Hj. rewrite Nat2Z.inj_succ.
        replace (base + sz * Z.succ (Z.of_nat j)) with (base + sz + sz * Z.of_nat j) by lia.
        exact (Hr2 j y Hj).
Qed.

(** Three fresh writable blocks: the environment record, the transaction
    record and an array. *)
Lemma three_blocks (m0 : mem) (esz tsz asz : Z) :
  exists m be bt bin,
    be <> bt /\ be <> bin /\ bt <> bin /\
    Mem.valid_block m be /\ Mem.valid_block m bt /\ Mem.valid_block m bin /\
    Mem.range_perm m be 0 esz Cur Writable /\
    Mem.range_perm m bt 0 tsz Cur Writable /\
    Mem.range_perm m bin 0 asz Cur Writable.
Proof.
  destruct (Mem.alloc m0 0 esz) as [m1 be] eqn:A1.
  destruct (Mem.alloc m1 0 tsz) as [m2 bt] eqn:A2.
  destruct (Mem.alloc m2 0 asz) as [m3 bin] eqn:A3.
  pose proof (Mem.valid_new_block _ _ _ _ _ A1) as V1.
  pose proof (Mem.valid_new_block _ _ _ _ _ A2) as V2.
  pose proof (Mem.valid_new_block _ _ _ _ _ A3) as V3.
  pose proof (Mem.fresh_block_alloc _ _ _ _ _ A2) as F2.
  pose proof (Mem.fresh_block_alloc _ _ _ _ _ A3) as F3.
  pose proof (Mem.valid_block_alloc _ _ _ _ _ A2 _ V1) as V12.
  exists m3, be, bt, bin.
  split; [intro; subst; contradiction|].
  split; [intro; subst; apply F3; exact V12|].
  split; [intro; subst; contradiction|].
  split; [eapply Mem.valid_block_alloc; eauto|].
  split; [eapply Mem.valid_block_alloc; eauto|].
  split; [exact V3|].
  split; [|split].
  - intros o Ho. eapply Mem.perm_alloc_1; [exact A3|]. eapply Mem.perm_alloc_1; [exact A2|].
    eapply Mem.perm_implies; [eapply Mem.perm_alloc_2; eauto|constructor].
  - intros o Ho. eapply Mem.perm_alloc_1; [exact A3|].
    eapply Mem.perm_implies; [eapply Mem.perm_alloc_2; eauto|constructor].
  - intros o Ho. eapply Mem.perm_implies; [eapply Mem.perm_alloc_2; eauto|constructor].
Qed.
