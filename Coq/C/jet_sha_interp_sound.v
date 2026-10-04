(** Soundness of the compression-body interpreter with respect to the Clight
    big-step semantics of the SHA translation unit. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require Import C.jets_sha C.jet_sha_linkage C.jet_sha_round C.jet_sha_interp.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Local Opaque sha_ge.
Set Default Timeout 120.

Lemma is_tuint_true ty : is_tuint ty = true -> ty = tuint.
Proof. unfold is_tuint. destruct (type_eq ty tuint); [auto|discriminate]. Qed.
Lemma is_tint_true ty : is_tint ty = true -> ty = tint.
Proof. unfold is_tint. destruct (type_eq ty tint); [auto|discriminate]. Qed.
Lemma is_ptuint_true ty : is_ptuint ty = true -> ty = tptr tuint.
Proof. unfold is_ptuint. destruct (type_eq ty (tptr tuint)); [auto|discriminate]. Qed.

Lemma arr_expr_inv a p i :
  arr_expr a = Some (p, i) ->
  a = Ebinop Oadd (Etempvar p (tptr tuint)) (Econst_int i tint) (tptr tuint).
Proof.
  destruct a; try discriminate. cbn.
  destruct b; try discriminate. destruct a1; try discriminate. destruct a2; try discriminate.
  destruct (is_ptuint t0) eqn:E1; [|discriminate]. destruct (is_tint t1) eqn:E2; [|discriminate].
  destruct (is_ptuint t) eqn:E3; [|discriminate]. cbn. intros H. injection H as <- <-.
  rewrite (is_ptuint_true _ E1), (is_tint_true _ E2), (is_ptuint_true _ E3). reflexivity.
Qed.

Lemma addr_local_inv e i :
  addr_local e = Some i -> exists x, e = Eaddrof (Evar x tuint) (tptr tuint) /\ index_of x lids = Some i.
Proof.
  destruct e; try discriminate. cbn. destruct e; try discriminate.
  destruct (is_tuint t0) eqn:E1; [|discriminate]. destruct (is_ptuint t) eqn:E2; [|discriminate].
  cbn. intros H. exists i0. rewrite (is_tuint_true _ E1), (is_ptuint_true _ E2). split; [reflexivity|exact H].
Qed.

Lemma arr_ofs (base : ptrofs) (i : int) (k : nat) :
  k = Z.to_nat (Int.unsigned i) -> (k < 16)%nat ->
  Ptrofs.unsigned base + 4 * Z.of_nat k + 4 <= Ptrofs.max_unsigned ->
  Ptrofs.unsigned (Ptrofs.add base (Ptrofs.mul (Ptrofs.repr 4) (Ptrofs.of_ints i))) =
    Ptrofs.unsigned base + 4 * Z.of_nat k.
Proof.
  intros Hk Hlt Hb. pose proof (Int.unsigned_range i) as Hi. pose proof (Ptrofs.unsigned_range base) as Hbr.
  assert (Hu : Int.unsigned i = Z.of_nat k) by (rewrite Hk, Z2Nat.id; lia).
  assert (Hs : Int.signed i = Z.of_nat k).
  { rewrite Int.signed_eq_unsigned; [exact Hu|]. change Int.max_signed with 2147483647. lia. }
  unfold Ptrofs.add, Ptrofs.mul, Ptrofs.of_ints. rewrite Hs.
  rewrite (Ptrofs.unsigned_repr (Z.of_nat k)) by lia.
  rewrite (Ptrofs.unsigned_repr 4) by (change Ptrofs.max_unsigned with 18446744073709551615; lia).
  rewrite (Ptrofs.unsigned_repr (4 * Z.of_nat k)) by lia.
  apply Ptrofs.unsigned_repr. lia.
Qed.

Section Sound.
Variables (env : Clight.env) (lb : list block) (bs : block) (os : ptrofs) (bc : block) (oc : ptrofs).
Let so := Ptrofs.unsigned os.
Let co := Ptrofs.unsigned oc.
Hypothesis Hlb : length lb = 8%nat.
Hypothesis Hnodup : NoDup lb.
Hypothesis Hbs : ~ In bs lb.
Hypothesis Hbc : ~ In bc lb.
Hypothesis Henv : forall i x b, nth_error lids i = Some x -> nth_error lb i = Some b -> env!x = Some (b, tuint).
Hypothesis Hg0 : env!_sigma0 = None.
Hypothesis Hg1 : env!_sigma1 = None.
Hypothesis HgR : env!_Round = None.
Hypothesis Hso : so + 32 <= Ptrofs.max_unsigned.
Hypothesis Hco : co + 64 <= Ptrofs.max_unsigned.
Hypothesis Hsc : bs <> bc \/ so + 32 <= co \/ co + 64 <= so.

Definition sha_R (st : cst) (le : temp_env) (m : mem) : Prop :=
  length (wv st) = 16%nat /\ length (lv st) = 8%nat /\ length (sarr st) = 8%nat /\ length (chunk st) = 16%nat /\
  (wdef st <= 16)%nat /\ (ldef st <= 8)%nat /\
  (forall i x, (i < wdef st)%nat -> nth_error wids i = Some x -> le!x = Some (Vint (nth i (wv st) Int.zero))) /\
  (forall t v, alookup (scratch st) t = Some v ->
     le!t = Some (Vint v) /\ index_of t wids = None /\ t <> _s /\ t <> _chunk) /\
  le!_s = Some (Vptr bs os) /\ le!_chunk = Some (Vptr bc oc) /\
  (forall i b, nth_error lb i = Some b -> Mem.valid_access m Mint32 b 0 Writable /\
     ((i < ldef st)%nat -> Mem.load Mint32 m b 0 = Some (Vint (nth i (lv st) Int.zero)))) /\
  (forall i, (i < 8)%nat ->
     Mem.load Mint32 m bs (so + 4 * Z.of_nat i) = Some (Vint (nth i (sarr st) Int.zero)) /\
     Mem.valid_access m Mint32 bs (so + 4 * Z.of_nat i) Writable) /\
  (forall i, (i < 16)%nat -> Mem.load Mint32 m bc (co + 4 * Z.of_nat i) = Some (Vint (nth i (chunk st) Int.zero))).

Definition sha_F (m m' : mem) : Prop :=
  (forall chunk b ofs, ~ In b lb -> (b <> bs \/ ofs + size_chunk chunk <= so \/ so + 32 <= ofs) ->
     Mem.load chunk m' b ofs = Mem.load chunk m b ofs) /\
  (forall b ofs k p, Mem.perm m b ofs k p -> Mem.perm m' b ofs k p) /\
  (forall b, Mem.valid_block m b -> Mem.valid_block m' b).

Lemma sha_F_refl m : sha_F m m.
Proof. repeat split; auto. Qed.

Lemma sha_F_trans m1 m2 m3 : sha_F m1 m2 -> sha_F m2 m3 -> sha_F m1 m3.
Proof.
  intros (L1 & P1 & V1) (L2 & P2 & V2). repeat split.
  - intros chunk b ofs Hb Ho. rewrite L2 by assumption. apply L1; assumption.
  - intros b ofs k p Hp. apply P2, P1, Hp.
  - intros b Hv. apply V2, V1, Hv.
Qed.

Lemma lb_nth i : (i < 8)%nat -> exists b, nth_error lb i = Some b.
Proof.
  intros Hi. destruct (nth_error lb i) as [b|] eqn:E; [eauto|].
  apply nth_error_None in E. lia.
Qed.

Lemma lb_in i b : nth_error lb i = Some b -> In b lb.
Proof. apply nth_error_In. Qed.

Lemma eval_ie_sound st le m e v :
  sha_R st le m -> eval_ie st e = Some v ->
  eval_expr sha_ge env le m e (Vint v) /\ typeof e = tuint.
Proof.
  intros HR. destruct HR as (Lw & Ll & Ls & Lc & Dw & Dl & RW & RS & Rs & Rc & RL & RSA & RCA).
  revert v. induction e; intros v H; cbn [eval_ie] in H; try discriminate.
  - (* Econst_int *)
    destruct (is_tuint t) eqn:E; [|discriminate]. apply is_tuint_true in E. subst t.
    injection H as <-. split; [apply eval_Econst_int|reflexivity].
  - (* Evar *)
    destruct (is_tuint t) eqn:E; [|discriminate]. apply is_tuint_true in E. subst t.
    destruct (index_of i lids) as [k|] eqn:Ek; [|discriminate].
    destruct (k <? ldef st)%nat eqn:El; [|discriminate]. apply Nat.ltb_lt in El.
    injection H as <-. pose proof (index_of_nth _ _ _ Ek) as Hn.
    destruct (lb_nth k ltac:(lia)) as [b Hb].
    destruct (RL k b Hb) as [_ HL]. split; [|reflexivity].
    eapply eval_Elvalue.
    + apply eval_Evar_local. exact (Henv k i b Hn Hb).
    + eapply deref_loc_value; [reflexivity|]. exact (HL El).
  - (* Etempvar *)
    destruct (is_tuint t) eqn:E; [|discriminate]. apply is_tuint_true in E. subst t.
    split; [|reflexivity]. apply eval_Etempvar.
    destruct (index_of i wids) as [k|] eqn:Ek.
    + destruct (k <? wdef st)%nat eqn:El; [|discriminate]. apply Nat.ltb_lt in El.
      injection H as <-. exact (RW k i El (index_of_nth _ _ _ Ek)).
    + exact (proj1 (RS i v H)).
  - (* Ederef *)
    destruct (is_tuint t) eqn:E; [|discriminate]. apply is_tuint_true in E. subst t.
    destruct (arr_expr e) as [[p i]|] eqn:Ea; [|discriminate].
    apply arr_expr_inv in Ea. subst e. split; [|reflexivity].
    unfold arr_read in H.
    destruct (Pos.eqb_spec p _s) as [->|Np].
    + destruct (Z.to_nat (Int.unsigned i) <? 8)%nat eqn:Ek; [|discriminate]. apply Nat.ltb_lt in Ek.
      injection H as <-.
      assert (HP : eval_expr sha_ge env le m
        (Ebinop Oadd (Etempvar _s (tptr tuint)) (Econst_int i tint) (tptr tuint))
        (Vptr bs (Ptrofs.add os (Ptrofs.mul (Ptrofs.repr 4) (Ptrofs.of_ints i)))))
        by (eapply eval_Ebinop; [apply eval_Etempvar; exact Rs|apply eval_Econst_int|reflexivity]).
      eapply eval_Elvalue.
      * apply eval_Ederef. exact HP.
      * eapply deref_loc_value; [reflexivity|]. cbn [Mem.loadv].
        rewrite (arr_ofs os i _ eq_refl ltac:(lia) ltac:(fold so; lia)).
        exact (proj1 (RSA _ Ek)).
    + destruct (Pos.eqb_spec p _chunk) as [->|Nc]; [|discriminate].
      destruct (Z.to_nat (Int.unsigned i) <? 16)%nat eqn:Ek; [|discriminate]. apply Nat.ltb_lt in Ek.
      injection H as <-.
      assert (HP : eval_expr sha_ge env le m
        (Ebinop Oadd (Etempvar _chunk (tptr tuint)) (Econst_int i tint) (tptr tuint))
        (Vptr bc (Ptrofs.add oc (Ptrofs.mul (Ptrofs.repr 4) (Ptrofs.of_ints i)))))
        by (eapply eval_Ebinop; [apply eval_Etempvar; exact Rc|apply eval_Econst_int|reflexivity]).
      eapply eval_Elvalue.
      * apply eval_Ederef. exact HP.
      * eapply deref_loc_value; [reflexivity|]. cbn [Mem.loadv].
        rewrite (arr_ofs oc i _ eq_refl Ek ltac:(fold co; lia)).
        exact (RCA _ Ek).
  - (* Ebinop *)
    destruct (is_tuint t) eqn:E; [|discriminate]. apply is_tuint_true in E. subst t.
    destruct (eval_ie st e1) as [va|]; [|discriminate].
    destruct (eval_ie st e2) as [vb|]; [|discriminate].
    destruct (IHe1 va eq_refl) as [He1 Ht1]. destruct (IHe2 vb eq_refl) as [He2 Ht2].
    split; [|reflexivity].
    destruct b; try discriminate; injection H as <-;
      (eapply eval_Ebinop; [exact He1|exact He2|rewrite Ht1, Ht2; reflexivity]).
  - (* Ecast *)
    destruct (is_tuint t) eqn:E; [|discriminate]. apply is_tuint_true in E. subst t.
    destruct (IHe v H) as [He Ht]. split; [|reflexivity].
    eapply eval_Ecast; [exact He|rewrite Ht; reflexivity].
Qed.

Lemma set_temp_sound st st' le m t v :
  sha_R st le m -> set_temp st t v = Some st' -> sha_R st' (PTree.set t (Vint v) le) m.
Proof.
  intros (Lw & Ll & Ls & Lc & Dw & Dl & RW & RS & Rs & Rc & RL & RSA & RCA) H.
  unfold set_temp in H.
  destruct (index_of t wids) as [k|] eqn:Ek.
  - destruct (k <=? wdef st)%nat eqn:El; [|discriminate]. apply Nat.leb_le in El.
    injection H as <-. unfold sha_R. cbn [wv wdef lv ldef scratch sarr chunk].
    pose proof (index_of_nth _ _ _ Ek) as Hn. pose proof (index_of_lt _ _ _ Ek) as Hlt.
    change (length wids) with 16%nat in Hlt.
    assert (Ht_s : t <> _s) by (intro; subst t; vm_compute in Ek; discriminate).
    assert (Ht_c : t <> _chunk) by (intro; subst t; vm_compute in Ek; discriminate).
    split; [rewrite upd_length; exact Lw|]. split; [exact Ll|]. split; [exact Ls|]. split; [exact Lc|].
    split; [lia|]. split; [exact Dl|].
    split.
    { intros i x Hi Hx. destruct (Nat.eq_dec i k) as [->|Nik].
      - assert (x = t) by congruence. subst x. rewrite PTree.gss, nth_upd_same by lia. reflexivity.
      - rewrite nth_upd_other by congruence. rewrite PTree.gso.
        + apply RW; [lia|exact Hx].
        + intro Heq. subst x. apply Nik. exact (nth_error_inj_nodup wids i k t wids_nodup Hx Hn). }
    split.
    { intros t0 v0 H0. destruct (RS t0 v0 H0) as (HA & HB & HC & HD).
      split; [|split; [exact HB|split; [exact HC|exact HD]]].
      rewrite PTree.gso; [exact HA|]. intro Heq. subst t0. congruence. }
    split; [rewrite PTree.gso by (apply not_eq_sym; exact Ht_s); exact Rs|].
    split; [rewrite PTree.gso by (apply not_eq_sym; exact Ht_c); exact Rc|].
    split; [exact RL|]. split; [exact RSA|exact RCA].
  - destruct (Pos.eqb_spec t _s) as [->|Ns]; [discriminate|].
    destruct (Pos.eqb_spec t _chunk) as [->|Nc]; [discriminate|].
    cbn in H. injection H as <-. unfold sha_R. cbn [wv wdef lv ldef scratch sarr chunk].
    split; [exact Lw|]. split; [exact Ll|]. split; [exact Ls|]. split; [exact Lc|].
    split; [exact Dw|]. split; [exact Dl|].
    split.
    { intros i x Hi Hx. rewrite PTree.gso; [apply RW; assumption|].
      intro Heq. subst x. apply index_of_none in Ek. apply Ek. eapply nth_error_In. exact Hx. }
    split.
    { intros t0 v0 H0. cbn [alookup] in H0. destruct (Pos.eqb_spec t0 t) as [->|Nt].
      - injection H0 as <-. split; [apply PTree.gss|]. split; [exact Ek|]. split; [exact Ns|exact Nc].
      - destruct (RS t0 v0 H0) as (HA & HB & HC & HD).
        split; [rewrite PTree.gso by exact Nt; exact HA|]. split; [exact HB|]. split; [exact HC|exact HD]. }
    split; [rewrite PTree.gso by (apply not_eq_sym; exact Ns); exact Rs|].
    split; [rewrite PTree.gso by (apply not_eq_sym; exact Nc); exact Rc|].
    split; [exact RL|]. split; [exact RSA|exact RCA].
Qed.

Lemma reset_R st le m : sha_R st le m -> sha_R (reset st) le m.
Proof.
  intros (Lw & Ll & Ls & Lc & Dw & Dl & RW & RS & Rs & Rc & RL & RSA & RCA).
  unfold reset, sha_R. cbn [wv wdef lv ldef scratch sarr chunk].
  split; [exact Lw|]. split; [exact Ll|]. split; [exact Ls|]. split; [exact Lc|].
  split; [exact Dw|]. split; [exact Dl|]. split; [exact RW|].
  split; [intros t v H; cbn in H; discriminate|].
  split; [exact Rs|]. split; [exact Rc|]. split; [exact RL|]. split; [exact RSA|exact RCA].
Qed.
End Sound.
