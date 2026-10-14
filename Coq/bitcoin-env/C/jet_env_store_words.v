(** Consecutive 32-bit stores as one memory operation, with the facts a
    caller needs afterwards: contents, permissions, block validity and what
    is left unchanged.  Pure CompCert memory model; no program. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory.
Require Import C.jet_uint32_array_init.
Import ListNotations.
Local Open Scope Z_scope.

Fixpoint store_words (m : mem) (b : block) (base : Z) (ws : list int) : option mem :=
  match ws with
  | [] => Some m
  | w :: rest =>
      match Mem.store Mint32 m b base (Vint w) with
      | Some m1 => store_words m1 b (base + 4) rest
      | None => None
      end
  end.

Lemma store_words_perm ws : forall m b base m', store_words m b base ws = Some m' ->
  forall b' ofs k p, Mem.perm m' b' ofs k p <-> Mem.perm m b' ofs k p.
Proof.
  induction ws as [|w ws IH]; intros m b base m' H b' ofs k p; cbn in H.
  - injection H as <-. tauto.
  - destruct (Mem.store Mint32 m b base (Vint w)) as [m1|] eqn:HS; [|discriminate].
    rewrite (IH _ _ _ _ H). split.
    + eapply Mem.perm_store_2; exact HS.
    + eapply Mem.perm_store_1; exact HS.
Qed.

Lemma store_words_nextblock ws : forall m b base m', store_words m b base ws = Some m' ->
  Mem.nextblock m' = Mem.nextblock m.
Proof.
  induction ws as [|w ws IH]; intros m b base m' H; cbn in H.
  - injection H as <-. reflexivity.
  - destruct (Mem.store Mint32 m b base (Vint w)) as [m1|] eqn:HS; [|discriminate].
    rewrite (IH _ _ _ _ H). eapply Mem.nextblock_store; exact HS.
Qed.

Lemma store_words_load_other ws : forall m b base m', store_words m b base ws = Some m' ->
  forall chunk b' ofs,
    b' <> b \/ ofs + size_chunk chunk <= base \/ base + 4 * Z.of_nat (length ws) <= ofs ->
    Mem.load chunk m' b' ofs = Mem.load chunk m b' ofs.
Proof.
  induction ws as [|w ws IH]; intros m b base m' H chunk b' ofs HO; cbn in H.
  - injection H as <-. reflexivity.
  - destruct (Mem.store Mint32 m b base (Vint w)) as [m1|] eqn:HS; [|discriminate].
    cbn [length] in HO.
    rewrite (IH _ _ _ _ H chunk b' ofs) by (destruct HO as [HO|[HO|HO]]; [left; exact HO|right; left; lia|right; right; lia]).
    eapply Mem.load_store_other; [exact HS|].
    destruct HO as [HO|[HO|HO]]; [left; exact HO|right; left; exact HO|right; right; cbn; lia].
Qed.

Lemma store_words_loads ws : forall m b base m', store_words m b base ws = Some m' ->
  uint32_array_at m' b base ws.
Proof.
  induction ws as [|w ws IH]; intros m b base m' H i x Hi; cbn in H.
  - destruct i; discriminate.
  - destruct (Mem.store Mint32 m b base (Vint w)) as [m1|] eqn:HS; [|discriminate].
    destruct i as [|i]; cbn in Hi.
    + injection Hi as <-. rewrite Z.mul_0_r, Z.add_0_r.
      rewrite (store_words_load_other _ _ _ _ _ H Mint32 b base) by (right; left; cbn; lia).
      rewrite (Mem.load_store_same _ _ _ _ _ _ HS). reflexivity.
    + replace (base + 4 * Z.of_nat (S i)) with (base + 4 + 4 * Z.of_nat i) by lia.
      exact (IH _ _ _ _ H i x Hi).
Qed.

Lemma store_words_exists ws : forall m b base,
  Mem.range_perm m b base (base + 4 * Z.of_nat (length ws)) Cur Writable -> (4 | base) ->
  exists m', store_words m b base ws = Some m'.
Proof.
  induction ws as [|w ws IH]; intros m b base HP HA; cbn.
  - eexists; reflexivity.
  - cbn [length] in HP.
    destruct (Mem.valid_access_store m Mint32 b base (Vint w)) as [m1 HS].
    { split; [|exact HA]. intros o Ho. apply HP. cbn in Ho. lia. }
    rewrite HS. apply IH.
    + intros o Ho. eapply Mem.perm_store_1; [exact HS|]. apply HP. lia.
    + apply Z.divide_add_r; [exact HA|exists 1; reflexivity].
Qed.

Lemma store_words_app ws1 : forall ws2 m b base m1 m2,
  store_words m b base ws1 = Some m1 ->
  store_words m1 b (base + 4 * Z.of_nat (length ws1)) ws2 = Some m2 ->
  store_words m b base (ws1 ++ ws2) = Some m2.
Proof.
  induction ws1 as [|w ws1 IH]; intros ws2 m b base m1 m2 H1 H2; cbn in H1.
  - injection H1 as <-. cbn [length] in H2. rewrite Z.mul_0_r, Z.add_0_r in H2. exact H2.
  - destruct (Mem.store Mint32 m b base (Vint w)) as [m0|] eqn:HS; [|discriminate].
    cbn. rewrite HS. eapply IH; [exact H1|].
    cbn [length] in H2. replace (base + 4 + 4 * Z.of_nat (length ws1)) with (base + 4 * Z.of_nat (S (length ws1))) by lia.
    exact H2.
Qed.

Lemma store_words_app_inv ws1 : forall ws2 m b base m2,
  store_words m b base (ws1 ++ ws2) = Some m2 ->
  exists m1, store_words m b base ws1 = Some m1 /\
    store_words m1 b (base + 4 * Z.of_nat (length ws1)) ws2 = Some m2.
Proof.
  induction ws1 as [|w ws1 IH]; intros ws2 m b base m2 H.
  - exists m. split; [reflexivity|]. cbn [length]. rewrite Z.mul_0_r, Z.add_0_r. exact H.
  - cbn [app store_words] in H |- *.
    destruct (Mem.store Mint32 m b base (Vint w)) as [m0|] eqn:HS; [|discriminate].
    destruct (IH _ _ _ _ _ H) as (m1 & H1 & H2). exists m1. split; [exact H1|].
    cbn [length]. replace (base + 4 * Z.of_nat (S (length ws1))) with (base + 4 + 4 * Z.of_nat (length ws1)) by lia.
    exact H2.
Qed.

Lemma repeat_snoc {A} (x : A) n : repeat x (S n) = repeat x n ++ [x].
Proof. induction n; [reflexivity|]. cbn [repeat app] in *. f_equal. exact IHn. Qed.
