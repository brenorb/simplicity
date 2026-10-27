(** The three explicit library models are jointly consistent with CompCert's
    axioms on external functions.

    Public theorems may combine [memcpy_model], [ctz_model] and
    [memset_model]. Each is a premise about the abstract parameter
    [external_functions_sem]. This module exhibits ONE assignment of
    semantics to all external functions that satisfies [extcall_properties]
    for every name and signature and makes all three statements true at
    once, so no combination of them is vacuous. It is a relative-consistency
    result and discharges none of the models. *)
From Coq Require Import ZArith List Lia String.
From compcert Require Import Coqlib Integers AST Values Memory Events Globalenvs.
Require Import C.jet_memcpy_model C.jet_memcpy_model_consistent
  C.jet_ctz_model C.jet_ctz_model_consistent C.jet_memset_model.
Import ListNotations.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 60.

(** The libc memset contract as an external-call semantics. *)
Inductive libc_memset_sem (ge : Senv.t) :
    list val -> mem -> trace -> val -> mem -> Prop :=
| libc_memset_sem_intro : forall bdst odst c sz m m',
    Int64.unsigned sz > 0 ->
    Mem.storebytes m bdst (Ptrofs.unsigned odst) (memset_bytes c (Int64.unsigned sz)) = Some m' ->
    libc_memset_sem ge [Vptr bdst odst; Vint c; Vlong sz] m E0 (Vptr bdst odst) m'.

Lemma memset_bytes_lessdef c n :
  list_forall2 memval_lessdef (memset_bytes c n) (memset_bytes c n).
Proof.
  unfold memset_bytes; induction (Z.to_nat n) as [|k IH]; constructor;
  [apply memval_lessdef_refl|exact IH].
Qed.

Lemma memset_bytes_inject f c n :
  list_forall2 (memval_inject f) (memset_bytes c n) (memset_bytes c n).
Proof.
  unfold memset_bytes; induction (Z.to_nat n) as [|k IH]; constructor;
  [constructor|exact IH].
Qed.

Ltac inv_args :=
  repeat match goal with
  | H : Val.lessdef_list (_ :: _) _ |- _ => inv H
  | H : Val.lessdef_list nil _ |- _ => inv H
  | H : Val.lessdef (Vptr _ _) _ |- _ => inv H
  | H : Val.lessdef (Vint _) _ |- _ => inv H
  | H : Val.lessdef (Vlong _) _ |- _ => inv H
  | H : Val.inject_list _ (_ :: _) _ |- _ => inv H
  | H : Val.inject_list _ nil _ |- _ => inv H
  | H : Val.inject _ (Vptr _ _) _ |- _ => inv H
  | H : Val.inject _ (Vint _) _ |- _ => inv H
  | H : Val.inject _ (Vlong _) _ |- _ => inv H
  end.

Lemma libc_memset_sem_ok : extcall_properties libc_memset_sem memset_sig.
Proof.
  constructor.
- (* return type *)
  intros ge vargs m1 t vres m2 H. inv H. reflexivity.
- (* change of globalenv *)
  intros ge1 ge2 vargs m1 t vres m2 _ H. inv H. econstructor; eauto.
- (* valid blocks *)
  intros ge vargs m1 t vres m2 b H Hb. inv H. eauto with mem.
- (* perms *)
  intros ge vargs m1 t vres m2 b ofs p H Hb Hp. inv H. eapply Mem.perm_storebytes_2; eauto.
- (* readonly *)
  intros ge vargs m1 t vres m2 b ofs n bytes0 H Hb HL HNW. inv H.
  eapply unchanged_on_readonly; eauto.
  eapply Mem.storebytes_unchanged_on; eauto.
  intros i Hi HNW'. apply HNW'.
  apply Mem.perm_cur_max. eapply Mem.storebytes_range_perm; eauto.
- (* extensions *)
  intros ge vargs m1 t vres m2 m1' vargs' H Hext Hargs. inv H. inv_args.
  match goal with
  | HSB : Mem.storebytes m1 bdst _ (memset_bytes ?c ?n) = Some m2 |- _ =>
      destruct (Mem.storebytes_within_extends _ _ _ _ _ _ _ Hext HSB (memset_bytes_lessdef c n))
        as [m2' [C D]];
      exists (Vptr bdst odst), m2';
      split; [econstructor; eauto|];
      split; [constructor|];
      split; [exact D|];
      eapply Mem.storebytes_unchanged_on; [exact C|];
      unfold loc_out_of_bounds; intros i Hi HOOB; apply HOOB;
      apply Mem.perm_cur_max; apply Mem.perm_implies with Writable; [|constructor];
      eapply Mem.storebytes_range_perm; [exact HSB|exact Hi]
  end.
- (* injections *)
  intros ge1 ge2 vargs m1 t vres m2 f m1' vargs' Hsym H Hinj Hargs. inv H. inv_args.
  match goal with
  | HSB : Mem.storebytes m1 bdst _ (memset_bytes ?c ?n) = Some m2,
    HFD : f bdst = Some (?bd2, ?dd),
    HPOS : Int64.unsigned ?sz > 0 |- _ =>
      assert (RPDST : Mem.range_perm m1 bdst (Ptrofs.unsigned odst)
          (Ptrofs.unsigned odst + Int64.unsigned sz) Cur Nonempty)
        by (rewrite <- (memset_bytes_length c (Int64.unsigned sz)) by lia;
            eapply Mem.range_perm_implies;
            [eapply Mem.storebytes_range_perm; exact HSB|constructor]);
      assert (PDST : Mem.perm m1 bdst (Ptrofs.unsigned odst) Cur Nonempty)
        by (apply RPDST; lia);
      pose proof (Mem.address_inject _ _ _ _ _ _ _ _ Hinj PDST HFD) as EQ2;
      destruct (Mem.storebytes_mapped_inject _ _ _ _ _ _ _ _ _ _ Hinj HSB HFD
        (memset_bytes_inject f c n)) as [m2' [C D]];
      exists f, (Vptr bd2 (Ptrofs.add odst (Ptrofs.repr dd))), m2';
      split; [econstructor; [exact HPOS|rewrite EQ2; exact C]|];
      split; [econstructor; [exact HFD|reflexivity]|];
      split; [exact D|];
      split; [eapply Mem.storebytes_unchanged_on; [exact HSB|];
              unfold loc_unmapped; intros; congruence|];
      split; [eapply Mem.storebytes_unchanged_on; [exact C|];
              unfold loc_out_of_reach; intros i Hi HOOR;
              eapply HOOR; [exact HFD|];
              apply Mem.perm_cur_max; apply Mem.perm_implies with Writable; [|constructor];
              eapply Mem.storebytes_range_perm; [exact HSB|lia]|];
      split; [apply inject_incr_refl|red; intros; congruence]
  end.
- (* trace length *)
  intros ge vargs m t vres m' H. inv H. simpl; lia.
- (* receptive *)
  intros ge vargs m t1 vres1 m1 t2 H Hmt.
  assert (t1 = t2) by (inv H; inv Hmt; auto). subst t2.
  exists vres1, m1; exact H.
- (* determ *)
  intros ge vargs m t1 vres1 m1 t2 vres2 m2 H1 H2. inv H1; inv H2.
  split; [constructor|]. intros _. split; congruence.
Qed.

Lemma libc_memset_sem_models : memset_model_for libc_memset_sem.
Proof.
  unfold memset_model_for; intros ge m bd od c n _ HP Hn.
  destruct (Mem.range_perm_storebytes m bd (Ptrofs.unsigned od) (memset_bytes c n)) as [m' HS].
  { rewrite memset_bytes_length by lia. exact HP. }
  exists m'. split; [exact HS|].
  assert (HU : Int64.unsigned (Int64.repr n) = n)
    by (apply Int64.unsigned_repr; unfold Int64.max_unsigned; cbn; lia).
  econstructor; rewrite ?HU; [lia|exact HS].
Qed.

Definition library_semantics (id : string) (sg : signature) : extcall_sem :=
  if string_dec id "memcpy" then
    if signature_eq sg memcpy_sig then libc_memcpy_sem else no_behaviour
  else if string_dec id "__builtin_ctzl" then
    if signature_eq sg ctz_sig then libc_ctz_sem else no_behaviour
  else if string_dec id "memset" then
    if signature_eq sg memset_sig then libc_memset_sem else no_behaviour
  else no_behaviour.

(** Joint model existence for every combination of the three premises. *)
Theorem library_models_consistent :
  exists S : string -> signature -> extcall_sem,
    (forall id sg, extcall_properties (S id sg) sg) /\
    memcpy_model_for (S "memcpy"%string memcpy_sig) /\
    ctz_model_for (S "__builtin_ctzl"%string ctz_sig) /\
    memset_model_for (S "memset"%string memset_sig).
Proof.
  exists library_semantics. split; [|split; [|split]].
  - intros id sg. unfold library_semantics.
    destruct (string_dec id "memcpy");
      [destruct (signature_eq sg memcpy_sig) as [->|];
       [exact libc_memcpy_sem_ok|apply no_behaviour_ok]|].
    destruct (string_dec id "__builtin_ctzl");
      [destruct (signature_eq sg ctz_sig) as [->|];
       [exact libc_ctz_sem_ok|apply no_behaviour_ok]|].
    destruct (string_dec id "memset");
      [destruct (signature_eq sg memset_sig) as [->|];
       [exact libc_memset_sem_ok|apply no_behaviour_ok]|apply no_behaviour_ok].
  - unfold library_semantics; cbn.
    destruct (signature_eq memcpy_sig memcpy_sig) as [_|N]; [|contradiction].
    exact libc_memcpy_sem_models.
  - unfold library_semantics; cbn.
    destruct (signature_eq ctz_sig ctz_sig) as [_|N]; [|contradiction].
    exact libc_ctz_sem_models.
  - unfold library_semantics; cbn.
    destruct (signature_eq memset_sig memset_sig) as [_|N]; [|contradiction].
    exact libc_memset_sem_models.
Qed.
