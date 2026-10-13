(** Constructed memories are extensions of the memory they start from: old
    blocks keep their contents and gain no permission.  This lets an
    invariant on existing objects (e.g. the SHA startup state) be carried
    through the construction of an environment. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Memory Values.
Require Import C.jet_frame_constructible_app C.jet_env_constructible.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 60.

Lemma memory_extension_refl m : memory_extension m m.
Proof. intros b Hb. repeat split; auto. Qed.

Lemma built_extension m0 m m' b lo hi :
  memory_extension m0 m -> ~ Mem.valid_block m0 b -> built m m' b lo hi ->
  memory_extension m0 m'.
Proof.
  intros HE Hf (L & P & V & Q) b' Hb'. destruct (HE b' Hb') as (Hv & Hl & Hp).
  assert (Hne : b' <> b) by (intro; subst; contradiction).
  split; [exact (V _ Hv)|]. split.
  - intros c o. rewrite (L c b' o (or_introl Hne)). exact (Hl c o).
  - intros o k p H. exact (Hp _ _ _ (Q _ _ _ _ H)).
Qed.

Lemma alloc_extension m0 m lo hi b :
  Mem.alloc m0 lo hi = (m, b) -> memory_extension m0 m /\ ~ Mem.valid_block m0 b.
Proof.
  intros HA. split; [|exact (Mem.fresh_block_alloc _ _ _ _ _ HA)].
  intros b' Hb'. split; [eapply Mem.valid_block_alloc; eauto|]. split.
  - intros c o. eapply Mem.load_alloc_unchanged; eauto.
  - intros o k p H. eapply Mem.perm_alloc_4; [exact HA|exact H|].
    intro; subst. exact (Mem.fresh_block_alloc _ _ _ _ _ HA Hb').
Qed.

Lemma memory_extension_trans m0 m1 m2 :
  memory_extension m0 m1 -> memory_extension m1 m2 -> memory_extension m0 m2.
Proof.
  intros H1 H2 b Hb. destruct (H1 b Hb) as (V1 & L1 & P1). destruct (H2 b V1) as (V2 & L2 & P2).
  split; [exact V2|]. split.
  - intros c o. rewrite L2. apply L1.
  - intros o k p H. exact (P1 _ _ _ (P2 _ _ _ H)).
Qed.

(** [three_blocks] as an extension with fresh blocks. *)
Lemma three_blocks_ext (m0 : mem) (esz tsz asz : Z) :
  exists m be bt bin,
    be <> bt /\ be <> bin /\ bt <> bin /\
    Mem.valid_block m be /\ Mem.valid_block m bt /\ Mem.valid_block m bin /\
    Mem.range_perm m be 0 esz Cur Writable /\
    Mem.range_perm m bt 0 tsz Cur Writable /\
    Mem.range_perm m bin 0 asz Cur Writable /\
    memory_extension m0 m /\
    ~ Mem.valid_block m0 be /\ ~ Mem.valid_block m0 bt /\ ~ Mem.valid_block m0 bin.
Proof.
  destruct (Mem.alloc m0 0 esz) as [m1 be] eqn:A1.
  destruct (Mem.alloc m1 0 tsz) as [m2 bt] eqn:A2.
  destruct (Mem.alloc m2 0 asz) as [m3 bin] eqn:A3.
  destruct (alloc_extension _ _ _ _ _ A1) as [E1 F1].
  destruct (alloc_extension _ _ _ _ _ A2) as [E2 F2].
  destruct (alloc_extension _ _ _ _ _ A3) as [E3 F3].
  pose proof (Mem.valid_new_block _ _ _ _ _ A1) as V1.
  pose proof (Mem.valid_new_block _ _ _ _ _ A2) as V2.
  pose proof (Mem.valid_new_block _ _ _ _ _ A3) as V3.
  pose proof (Mem.valid_block_alloc _ _ _ _ _ A2 _ V1) as V12.
  exists m3, be, bt, bin.
  split; [intro; subst; contradiction|].
  split; [intro; subst; apply F3; exact V12|].
  split; [intro; subst; contradiction|].
  split; [eapply Mem.valid_block_alloc; eauto|].
  split; [eapply Mem.valid_block_alloc; eauto|].
  split; [exact V3|].
  split.
  { intros o Ho. eapply Mem.perm_alloc_1; [exact A3|]. eapply Mem.perm_alloc_1; [exact A2|].
    eapply Mem.perm_implies; [eapply Mem.perm_alloc_2; eauto|constructor]. }
  split.
  { intros o Ho. eapply Mem.perm_alloc_1; [exact A3|].
    eapply Mem.perm_implies; [eapply Mem.perm_alloc_2; eauto|constructor]. }
  split.
  { intros o Ho. eapply Mem.perm_implies; [eapply Mem.perm_alloc_2; eauto|constructor]. }
  split; [exact (memory_extension_trans _ _ _ (memory_extension_trans _ _ _ E1 E2) E3)|].
  split; [exact F1|].
  split.
  - intro H. apply F2. destruct (E1 _ H) as (Hv & _). exact Hv.
  - intro H. apply F3. destruct (E1 _ H) as (Hv & _). destruct (E2 _ Hv) as (Hv2 & _). exact Hv2.
Qed.
