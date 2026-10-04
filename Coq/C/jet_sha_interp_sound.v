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

Lemma attr_noattrb_true a : attr_noattrb a = true -> a = noattr.
Proof.
  destruct a as [v al]. unfold attr_noattrb. cbn. destruct v; [discriminate|].
  destruct al; [discriminate|]. reflexivity.
Qed.
Lemma is_tuint_true ty : is_tuint ty = true -> ty = tuint.
Proof.
  destruct ty; try discriminate. destruct i; try discriminate. destruct s; try discriminate.
  cbn. intros H. apply attr_noattrb_true in H. subst a. reflexivity.
Qed.
Lemma is_tint_true ty : is_tint ty = true -> ty = tint.
Proof.
  destruct ty; try discriminate. destruct i; try discriminate. destruct s; try discriminate.
  cbn. intros H. apply attr_noattrb_true in H. subst a. reflexivity.
Qed.
Lemma is_ptuint_true ty : is_ptuint ty = true -> ty = tptr tuint.
Proof.
  destruct ty; try discriminate. cbn. intros H. apply andb_true_iff in H. destruct H as [H1 H2].
  apply is_tuint_true in H1. apply attr_noattrb_true in H2. subst. reflexivity.
Qed.
Lemma is_cc_default_true cc : is_cc_default cc = true -> cc = cc_default.
Proof.
  destruct cc as [va up sr]. unfold is_cc_default. cbn. destruct va; [discriminate|].
  destruct up; [discriminate|]. destruct sr; [discriminate|]. reflexivity.
Qed.
Lemma is_sigma_ty_true ty : is_sigma_ty ty = true -> ty = sigma_ty.
Proof.
  destruct ty as [| | | | | |targs tres cc| | ]; try discriminate.
  destruct targs as [|ta [|? ?]]; try discriminate.
  cbn. intros H. apply andb_true_iff in H. destruct H as [H H3]. apply andb_true_iff in H. destruct H as [H1 H2].
  apply is_tuint_true in H1, H2. apply is_cc_default_true in H3. subst. reflexivity.
Qed.
Lemma is_round_ty_true ty : is_round_ty ty = true -> ty = round_ty.
Proof.
  destruct ty as [| | | | | |targs tres cc| | ]; try discriminate.
  destruct targs as [|a [|b [|c [|d [|e [|f [|g [|h [|k [|? ?]]]]]]]]]]; try discriminate.
  destruct tres; try discriminate.
  cbn. intros H. repeat (apply andb_true_iff in H; let H' := fresh "H" in destruct H as [H H']).
  repeat match goal with
  | X : is_tuint _ = true |- _ => apply is_tuint_true in X
  | X : is_ptuint _ = true |- _ => apply is_ptuint_true in X
  | X : is_cc_default _ = true |- _ => apply is_cc_default_true in X
  end. subst. reflexivity.
Qed.

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
Lemma lb_block_eq i j b : nth_error lb i = Some b -> nth_error lb j = Some b -> i = j.
Proof. intros Hi Hj. exact (nth_error_inj_nodup lb i j b Hnodup Hi Hj). Qed.

(** A store into local [i]. *)
Lemma local_store_R st le m m' i b v :
  sha_R st le m -> nth_error lb i = Some b -> (i <= ldef st)%nat ->
  Mem.store Mint32 m b 0 (Vint v) = Some m' ->
  sha_R (set_local st i v) le m' /\ sha_F m m'.
Proof.
  intros (Lw & Ll & Ls & Lc & Dw & Dl & RW & RS & Rs & Rc & RL & RSA & RCA) Hb Hi SM.
  assert (Hi8 : (i < 8)%nat) by (rewrite <- Hlb; apply nth_error_Some; rewrite Hb; discriminate).
  split.
  - unfold sha_R, set_local. cbn [wv wdef lv ldef scratch sarr chunk].
    split; [exact Lw|]. split; [rewrite upd_length; exact Ll|]. split; [exact Ls|]. split; [exact Lc|].
    split; [exact Dw|]. split; [lia|]. split; [exact RW|]. split; [exact RS|].
    split; [exact Rs|]. split; [exact Rc|].
    split.
    { intros j b' Hb'. destruct (RL j b' Hb') as [PW HL].
      split; [eapply Mem.store_valid_access_1; eauto|].
      intros Hj. destruct (Nat.eq_dec j i) as [->|Nji].
      - assert (b' = b) by congruence. subst b'. rewrite nth_upd_same by lia.
        exact (Mem.load_store_same _ _ _ _ _ _ SM).
      - rewrite nth_upd_other by congruence.
        erewrite Mem.load_store_other; [apply HL; lia|exact SM|].
        left. intro Heq. subst b'. apply Nji. exact (lb_block_eq j i b Hb' Hb). }
    split.
    { intros j Hj. destruct (RSA j Hj) as [HL PW].
      split; [|eapply Mem.store_valid_access_1; eauto].
      erewrite Mem.load_store_other; [exact HL|exact SM|].
      left. intro Heq. subst b. apply Hbs. exact (lb_in i bs Hb). }
    { intros j Hj. erewrite Mem.load_store_other; [exact (RCA j Hj)|exact SM|].
      left. intro Heq. subst b. apply Hbc. exact (lb_in i bc Hb). }
  - split; [|split].
    + intros chunk0 b' ofs Hb' _. eapply Mem.load_store_other; [exact SM|].
      left. intro Heq. subst b'. apply Hb'. exact (lb_in i b Hb).
    + intros b' ofs k p Hp. eapply Mem.perm_store_1; eauto.
    + intros b' Hv. eapply Mem.store_valid_block_1; eauto.
Qed.

Lemma interp_assign_sound st st' le m lhs e :
  sha_R st le m -> interp_assign st lhs e = Some st' ->
  exists m', Clight2.exec_stmt sha_ge env le m (Sassign lhs e) E0 le m' Out_normal /\
    sha_R st' le m' /\ sha_F m m'.
Proof.
  intros HR H. pose proof HR as (Lw & Ll & Ls & Lc & Dw & Dl & RW & RS & Rs & Rc & RL & RSA & RCA).
  destruct lhs; try discriminate; cbn [interp_assign] in H.
  - (* local *)
    destruct (is_tuint t) eqn:E; [|discriminate]. apply is_tuint_true in E. subst t.
    destruct (index_of i lids) as [k|] eqn:Ek; [|discriminate].
    destruct (eval_ie st e) as [v|] eqn:Ev; [|discriminate].
    destruct (k <=? ldef st)%nat eqn:El; [|discriminate]. apply Nat.leb_le in El.
    injection H as <-.
    pose proof (index_of_nth _ _ _ Ek) as Hn. pose proof (index_of_lt _ _ _ Ek) as Hlt.
    change (length lids) with 8%nat in Hlt.
    destruct (lb_nth k Hlt) as [b Hb].
    destruct (eval_ie_sound st le m e v HR Ev) as [He Ht].
    destruct (RL k b Hb) as [PW _].
    destruct (Mem.valid_access_store m Mint32 b 0 (Vint v) PW) as [m' SM].
    destruct (local_store_R st le m m' k b v HR Hb El SM) as [HR' HF'].
    exists m'. split; [|split; assumption].
    eapply exec_Sassign with (v2 := Vint v) (v := Vint v).
    + apply eval_Evar_local. exact (Henv k i b Hn Hb).
    + exact He.
    + rewrite Ht. reflexivity.
    + eapply assign_loc_value; [reflexivity|]. exact SM.
  - (* state array cell *)
    destruct (is_tuint t) eqn:E; [|discriminate]. apply is_tuint_true in E. subst t.
    destruct (arr_expr lhs) as [[p i]|] eqn:Ea; [|discriminate].
    destruct (eval_ie st e) as [v|] eqn:Ev; [|discriminate].
    destruct (Pos.eqb_spec p _s) as [->|Np]; [|discriminate].
    destruct (Z.to_nat (Int.unsigned i) <? 8)%nat eqn:Ek; [|discriminate]. apply Nat.ltb_lt in Ek.
    cbn in H. injection H as <-.
    apply arr_expr_inv in Ea. subst lhs.
    set (k := Z.to_nat (Int.unsigned i)) in *.
    destruct (eval_ie_sound st le m e v HR Ev) as [He Ht].
    destruct (RSA k Ek) as [_ PW].
    destruct (Mem.valid_access_store m Mint32 bs (so + 4 * Z.of_nat k) (Vint v) PW) as [m' SM].
    assert (Hofs : Ptrofs.unsigned (Ptrofs.add os (Ptrofs.mul (Ptrofs.repr 4) (Ptrofs.of_ints i))) =
      so + 4 * Z.of_nat k) by (apply arr_ofs; [reflexivity|lia|fold so; lia]).
    exists m'. split; [|split].
    + eapply exec_Sassign with (v2 := Vint v) (v := Vint v)
        (loc := bs) (ofs := Ptrofs.add os (Ptrofs.mul (Ptrofs.repr 4) (Ptrofs.of_ints i))).
      * apply eval_Ederef. eapply eval_Ebinop; [apply eval_Etempvar; exact Rs|apply eval_Econst_int|reflexivity].
      * exact He.
      * rewrite Ht. reflexivity.
      * eapply assign_loc_value; [reflexivity|]. cbn [Mem.storev]. rewrite Hofs. exact SM.
    + unfold sha_R. cbn [wv wdef lv ldef scratch sarr chunk].
      split; [exact Lw|]. split; [exact Ll|]. split; [rewrite upd_length; exact Ls|]. split; [exact Lc|].
      split; [exact Dw|]. split; [exact Dl|]. split; [exact RW|]. split; [exact RS|].
      split; [exact Rs|]. split; [exact Rc|].
      split.
      { intros j b' Hb'. destruct (RL j b' Hb') as [PW' HL].
        split; [eapply Mem.store_valid_access_1; eauto|].
        intros Hj. erewrite Mem.load_store_other; [exact (HL Hj)|exact SM|].
        left. intro Heq. subst b'. apply Hbs. exact (lb_in j bs Hb'). }
      split.
      { intros j Hj. destruct (RSA j Hj) as [HL PW'].
        split; [|eapply Mem.store_valid_access_1; eauto].
        destruct (Nat.eq_dec j k) as [->|Njk].
        - rewrite nth_upd_same by lia. exact (Mem.load_store_same _ _ _ _ _ _ SM).
        - rewrite nth_upd_other by congruence.
          erewrite Mem.load_store_other; [exact HL|exact SM|].
          right. change (size_chunk Mint32) with 4. lia. }
      { intros j Hj. erewrite Mem.load_store_other; [exact (RCA j Hj)|exact SM|].
        change (size_chunk Mint32) with 4. fold co.
        destruct Hsc as [H|[H|H]]; [left; intro Heq; apply H; symmetry; exact Heq|right; lia|right; lia]. }
    + split; [|split].
      * intros chunk0 b' ofs Hb' Ho. eapply Mem.load_store_other; [exact SM|].
        change (size_chunk Mint32) with 4. destruct Ho as [H|[H|H]]; [left; exact H|right; lia|right; lia].
      * intros b' ofs k0 p Hp. eapply Mem.perm_store_1; eauto.
      * intros b' Hv. eapply Mem.store_valid_block_1; eauto.
Qed.

Lemma interp_sigma_sound st st' le m t f fty a :
  sha_R st le m -> interp_sigma st t f fty a = Some st' ->
  exists le', Clight2.exec_stmt sha_ge env le m (Scall (Some t) (Evar f fty) [a]) E0 le' m Out_normal /\
    sha_R st' le' m.
Proof.
  intros HR H. unfold interp_sigma in H.
  destruct (is_sigma_ty fty) eqn:Efty; [|discriminate]. apply is_sigma_ty_true in Efty. subst fty.
  destruct (eval_ie st a) as [v|] eqn:Ev; [|discriminate].
  destruct (eval_ie_sound st le m a v HR Ev) as [He Ht].
  destruct (Pos.eqb_spec f _sigma0) as [->|N0].
  - exists (PTree.set t (Vint (c_sigma0 v)) le). split; [|eapply set_temp_sound; eassumption].
    eapply sha_helper_call1 with (f := f_sigma0) (x := v);
      [exact sha_sigma0_symbol|exact sha_sigma0_funct|reflexivity|exact Hg0|exact He|exact Ht|
       apply eval_sha_sigma0].
  - destruct (Pos.eqb_spec f _sigma1) as [->|N1]; [|discriminate].
    exists (PTree.set t (Vint (c_sigma1 v)) le). split; [|eapply set_temp_sound; eassumption].
    eapply sha_helper_call1 with (f := f_sigma1) (x := v);
      [exact sha_sigma1_symbol|exact sha_sigma1_funct|reflexivity|exact Hg1|exact He|exact Ht|
       apply eval_sha_sigma1].
Qed.

Lemma interp_round_sound st st' le m f fty a b c d e f' g h k :
  sha_R st le m -> interp_round st f fty a b c d e f' g h k = Some st' ->
  exists m', Clight2.exec_stmt sha_ge env le m
      (Scall None (Evar f fty) [a; b; c; d; e; f'; g; h; k]) E0 le m' Out_normal /\
    sha_R st' le m' /\ sha_F m m'.
Proof.
  intros HR H. unfold interp_round in H.
  destruct (is_round_ty fty) eqn:Efty; [|discriminate]. apply is_round_ty_true in Efty. subst fty.
  destruct (Pos.eqb_spec f _Round) as [->|]; [|discriminate].
  destruct (eval_ie st a) as [va|] eqn:Ea; [|discriminate].
  destruct (eval_ie st b) as [vb|] eqn:Eb; [|discriminate].
  destruct (eval_ie st c) as [vc|] eqn:Ec; [|discriminate].
  destruct (eval_ie st e) as [ve|] eqn:Ee; [|discriminate].
  destruct (eval_ie st f') as [vf|] eqn:Ef; [|discriminate].
  destruct (eval_ie st g) as [vg|] eqn:Eg; [|discriminate].
  destruct (eval_ie st k) as [vk|] eqn:Ekk; [|discriminate].
  destruct (addr_local d) as [id|] eqn:Ed; [|discriminate].
  destruct (addr_local h) as [ih|] eqn:Eh; [|discriminate].
  destruct (id <? ldef st)%nat eqn:Lid; [|discriminate]. apply Nat.ltb_lt in Lid.
  destruct (ih <? ldef st)%nat eqn:Lih; [|discriminate]. apply Nat.ltb_lt in Lih.
  destruct (Nat.eqb_spec id ih) as [|Ndh]; [discriminate|].
  cbn in H. injection H as <-.
  pose proof HR as (Lw & Ll & Ls & Lc & Dw & Dl & RW & RS & Rs & Rc & RL & RSA & RCA).
  destruct (addr_local_inv d id Ed) as (xd & -> & Exd).
  destruct (addr_local_inv h ih Eh) as (xh & -> & Exh).
  pose proof (index_of_nth _ _ _ Exd) as Hnd. pose proof (index_of_nth _ _ _ Exh) as Hnh.
  destruct (lb_nth id ltac:(lia)) as [bd Hbd]. destruct (lb_nth ih ltac:(lia)) as [bh Hbh].
  destruct (RL id bd Hbd) as [PWd HLd]. destruct (RL ih bh Hbh) as [PWh HLh].
  specialize (HLd Lid). specialize (HLh Lih).
  set (dv := nth id (lv st) Int.zero) in *. set (hv := nth ih (lv st) Int.zero) in *.
  destruct (eval_sha_Round m va vb vc bd Ptrofs.zero ve vf vg bh Ptrofs.zero vk dv hv HLd HLh PWd PWh)
    as (md & m' & SD & SH & Hcall).
  change (Ptrofs.unsigned Ptrofs.zero) with 0 in SD, SH.
  destruct (eval_ie_sound st le m a va HR Ea) as [Hea Hta].
  destruct (eval_ie_sound st le m b vb HR Eb) as [Heb Htb].
  destruct (eval_ie_sound st le m c vc HR Ec) as [Hec Htc].
  destruct (eval_ie_sound st le m e ve HR Ee) as [Hee Hte].
  destruct (eval_ie_sound st le m f' vf HR Ef) as [Hef Htf].
  destruct (eval_ie_sound st le m g vg HR Eg) as [Heg Htg].
  destruct (eval_ie_sound st le m k vk HR Ekk) as [Hek Htk].
  assert (Hbdh : bd <> bh) by (intro Heq; subst bh; apply Ndh; exact (lb_block_eq id ih bd Hbd Hbh)).
  exists m'. split; [|split].
  - change le with (set_opttemp None Vundef le) at 2.
    eapply exec_Scall with (vf := Vptr (sha_symbol_block _Round) Ptrofs.zero) (f := Internal f_Round)
      (vargs := [Vint va; Vint vb; Vint vc; Vptr bd Ptrofs.zero; Vint ve; Vint vf; Vint vg;
                 Vptr bh Ptrofs.zero; Vint vk]).
    + reflexivity.
    + eapply eval_Elvalue; [apply eval_Evar_global; [exact HgR|exact sha_Round_symbol]|
        apply deref_loc_reference; reflexivity].
    + eapply eval_Econs; [exact Hea|rewrite Hta; reflexivity|].
      eapply eval_Econs; [exact Heb|rewrite Htb; reflexivity|].
      eapply eval_Econs; [exact Hec|rewrite Htc; reflexivity|].
      eapply eval_Econs; [apply eval_Eaddrof; apply eval_Evar_local; exact (Henv id xd bd Hnd Hbd)|reflexivity|].
      eapply eval_Econs; [exact Hee|rewrite Hte; reflexivity|].
      eapply eval_Econs; [exact Hef|rewrite Htf; reflexivity|].
      eapply eval_Econs; [exact Heg|rewrite Htg; reflexivity|].
      eapply eval_Econs; [apply eval_Eaddrof; apply eval_Evar_local; exact (Henv ih xh bh Hnh Hbh)|reflexivity|].
      eapply eval_Econs; [exact Hek|rewrite Htk; reflexivity|apply eval_Enil].
    + exact sha_Round_funct.
    + reflexivity.
    + exact Hcall.
  - unfold sha_R. cbn [wv wdef lv ldef scratch sarr chunk].
    split; [exact Lw|]. split; [rewrite !upd_length; exact Ll|]. split; [exact Ls|]. split; [exact Lc|].
    split; [exact Dw|]. split; [exact Dl|]. split; [exact RW|]. split; [exact RS|].
    split; [exact Rs|]. split; [exact Rc|].
    split.
    { intros j b' Hb'. destruct (RL j b' Hb') as [PW' HL].
      split; [eapply Mem.store_valid_access_1; [exact SH|]; eapply Mem.store_valid_access_1; eauto|].
      intros Hj. destruct (Nat.eq_dec j ih) as [->|Njh].
      - assert (b' = bh) by congruence. subst b'. rewrite nth_upd_same by (rewrite upd_length; lia).
        exact (Mem.load_store_same _ _ _ _ _ _ SH).
      - rewrite (nth_upd_other _ ih j) by congruence.
        erewrite Mem.load_store_other; [|exact SH|left; intro Heq; subst b'; apply Njh;
          exact (lb_block_eq j ih bh Hb' Hbh)].
        destruct (Nat.eq_dec j id) as [->|Njd].
        + assert (b' = bd) by congruence. subst b'. rewrite nth_upd_same by lia.
          exact (Mem.load_store_same _ _ _ _ _ _ SD).
        + rewrite nth_upd_other by congruence.
          erewrite Mem.load_store_other; [exact (HL Hj)|exact SD|].
          left. intro Heq. subst b'. apply Njd. exact (lb_block_eq j id bd Hb' Hbd). }
    split.
    { intros j Hj. destruct (RSA j Hj) as [HL PW'].
      split; [|eapply Mem.store_valid_access_1; [exact SH|]; eapply Mem.store_valid_access_1; eauto].
      erewrite Mem.load_store_other; [|exact SH|left; intro Heq; subst bh; apply Hbs; exact (lb_in ih bs Hbh)].
      erewrite Mem.load_store_other; [exact HL|exact SD|].
      left. intro Heq. subst bd. apply Hbs. exact (lb_in id bs Hbd). }
    { intros j Hj.
      erewrite Mem.load_store_other; [|exact SH|left; intro Heq; subst bh; apply Hbc; exact (lb_in ih bc Hbh)].
      erewrite Mem.load_store_other; [exact (RCA j Hj)|exact SD|].
      left. intro Heq. subst bd. apply Hbc. exact (lb_in id bc Hbd). }
  - split; [|split].
    + intros chunk0 b' ofs Hb' _.
      erewrite Mem.load_store_other; [|exact SH|left; intro Heq; subst b'; apply Hb'; exact (lb_in ih bh Hbh)].
      eapply Mem.load_store_other; [exact SD|].
      left. intro Heq. subst b'. apply Hb'. exact (lb_in id bd Hbd).
    + intros b' ofs k0 p Hp. eapply Mem.perm_store_1; [exact SH|]. eapply Mem.perm_store_1; eauto.
    + intros b' Hv. eapply Mem.store_valid_block_1; [exact SH|]. eapply Mem.store_valid_block_1; eauto.
Qed.

Theorem interp_sound s : forall st st' le m,
  sha_R st le m -> interp s st = Some st' ->
  exists le' m', Clight2.exec_stmt sha_ge env le m s E0 le' m' Out_normal /\
    sha_R st' le' m' /\ sha_F m m'.
Proof.
  induction s; intros st st' le m HR H; cbn [interp] in H; try discriminate.
  - (* Sassign *)
    destruct (interp_assign_sound st st' le m e e0 HR H) as (m' & Hex & HR' & HF').
    exists le, m'. split; [exact Hex|split; assumption].
  - (* Sset *)
    destruct (eval_ie st e) as [v|] eqn:Ev; [|discriminate].
    destruct (eval_ie_sound st le m e v HR Ev) as [He _].
    exists (PTree.set i (Vint v) le), m. split; [constructor; exact He|].
    split; [eapply set_temp_sound; eassumption|apply sha_F_refl].
  - (* Scall *)
    destruct o as [t|].
    + destruct e; try discriminate. destruct l as [|a [|? ?]]; try discriminate.
      destruct (interp_sigma_sound st st' le m t i t0 a HR H) as (le' & Hex & HR').
      exists le', m. split; [exact Hex|]. split; [exact HR'|apply sha_F_refl].
    + destruct e; try discriminate.
      destruct l as [|a [|b [|c [|d [|e [|f' [|g [|h [|k [|? ?]]]]]]]]]]; try discriminate.
      destruct (interp_round_sound st st' le m i t a b c d e f' g h k HR H) as (m' & Hex & HR' & HF').
      exists le, m'. split; [exact Hex|split; assumption].
  - (* Ssequence *)
    destruct (interp s1 st) as [st1|] eqn:E1; [|discriminate].
    destruct (IHs1 st st1 le m HR E1) as (le1 & m1 & Hex1 & HR1 & HF1).
    destruct (IHs2 st1 st' le1 m1 HR1 H) as (le2 & m2 & Hex2 & HR2 & HF2).
    exists le2, m2. split; [|split; [exact HR2|eapply sha_F_trans; eassumption]].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact Hex1|exact Hex2].
Qed.

Theorem interp_spine_sound fuel : forall s st st' le m,
  sha_R st le m -> interp_spine fuel s st = Some st' ->
  exists le' m', Clight2.exec_stmt sha_ge env le m s E0 le' m' Out_normal /\
    sha_R st' le' m' /\ sha_F m m'.
Proof.
  induction fuel as [|fuel IH]; intros s st st' le m HR H; cbn [interp_spine] in H.
  - eapply interp_sound; [apply reset_R; exact HR|exact H].
  - destruct s; try (eapply interp_sound; [apply reset_R; exact HR|exact H]).
    destruct (interp s1 (reset st)) as [st1|] eqn:E1; [|discriminate].
    destruct (interp_sound s1 (reset st) st1 le m (reset_R st le m HR) E1) as (le1 & m1 & Hex1 & HR1 & HF1).
    destruct (IH s2 st1 st' le1 m1 HR1 H) as (le2 & m2 & Hex2 & HR2 & HF2).
    exists le2, m2. split; [|split; [exact HR2|eapply sha_F_trans; eassumption]].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact Hex1|exact Hex2].
Qed.
End Sound.
