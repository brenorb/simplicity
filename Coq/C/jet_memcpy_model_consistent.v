(** [memcpy_model] is consistent with CompCert's axioms on external functions.

    The accepted copy-family and SHA-unit theorems take [memcpy_model] as a
    premise: a statement about [external_functions_sem "memcpy" memcpy_sig],
    which CompCert leaves abstract ([Parameter]) and constrains only by
    [external_functions_properties].  A premise about an abstract parameter
    could in principle contradict the constraint and make every theorem that
    assumes it vacuous.  This module rules that out: there is an assignment
    of semantics to *all* external functions that satisfies
    [extcall_properties] for every name and signature and for which the
    statement of [memcpy_model] holds.  The semantics chosen for memcpy is
    the libc contract itself (three arguments, positive size, disjoint
    ranges, the destination pointer returned, no event); its proof of
    [extcall_properties] follows CompCert's proof for the two-argument
    builtin [extcall_memcpy_sem].

    This is a relative-consistency (model existence) result.  It does not
    discharge [memcpy_model]: nothing identifies the abstract parameter with
    the semantics exhibited here. *)
From Coq Require Import ZArith List Lia String.
From compcert Require Import Coqlib Integers AST Values Memory Events Globalenvs.
Require Import C.jet_memcpy_model.
Import ListNotations.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 60.

(** The statement of [memcpy_model] for an arbitrary semantics of memcpy. *)
Definition memcpy_model_for (sem : extcall_sem) : Prop :=
  forall (ge : Senv.t) m bd od bs os n bytes,
    Mem.valid_block m bs -> Mem.valid_block m bd ->
    Mem.loadbytes m bs (Ptrofs.unsigned os) n = Some bytes ->
    Mem.range_perm m bd (Ptrofs.unsigned od) (Ptrofs.unsigned od + n) Cur Writable ->
    (bs <> bd \/ Ptrofs.unsigned os + n <= Ptrofs.unsigned od \/
      Ptrofs.unsigned od + n <= Ptrofs.unsigned os) ->
    0 < n <= Int64.max_unsigned ->
    Ptrofs.unsigned os + n <= Ptrofs.max_unsigned + 1 ->
    Ptrofs.unsigned od + n <= Ptrofs.max_unsigned + 1 ->
    exists m', Mem.storebytes m bd (Ptrofs.unsigned od) bytes = Some m' /\
      sem ge [Vptr bd od; Vptr bs os; Vlong (Int64.repr n)] m E0 (Vptr bd od) m'.

(** [memcpy_model] is that statement at CompCert's abstract parameter. *)
Lemma memcpy_model_is_instance :
  memcpy_model = memcpy_model_for (external_functions_sem "memcpy" memcpy_sig).
Proof. reflexivity. Qed.

(** The libc contract as an external-call semantics. *)
Inductive libc_memcpy_sem (ge : Senv.t) :
    list val -> mem -> trace -> val -> mem -> Prop :=
| libc_memcpy_sem_intro : forall bdst odst bsrc osrc sz m bytes m',
    Int64.unsigned sz > 0 ->
    bsrc <> bdst \/
      Ptrofs.unsigned osrc + Int64.unsigned sz <= Ptrofs.unsigned odst \/
      Ptrofs.unsigned odst + Int64.unsigned sz <= Ptrofs.unsigned osrc ->
    Mem.loadbytes m bsrc (Ptrofs.unsigned osrc) (Int64.unsigned sz) = Some bytes ->
    Mem.storebytes m bdst (Ptrofs.unsigned odst) bytes = Some m' ->
    libc_memcpy_sem ge [Vptr bdst odst; Vptr bsrc osrc; Vlong sz] m E0 (Vptr bdst odst) m'.

(** Disjoint ranges stay disjoint under a memory injection (CompCert's
    [Mem.disjoint_or_equal_inject] also admits the coinciding case, which
    the libc contract excludes). *)
Lemma inject_disjoint_ranges f m m' b1 b1' d1 b2 b2' d2 o1 o2 sz :
  Mem.inject f m m' ->
  f b1 = Some (b1', d1) -> f b2 = Some (b2', d2) ->
  Mem.range_perm m b1 o1 (o1 + sz) Max Nonempty ->
  Mem.range_perm m b2 o2 (o2 + sz) Max Nonempty ->
  sz > 0 ->
  b1 <> b2 \/ o1 + sz <= o2 \/ o2 + sz <= o1 ->
  b1' <> b2' \/ o1 + d1 + sz <= o2 + d2 \/ o2 + d2 + sz <= o1 + d1.
Proof.
  intros Hinj H1 H2 HP1 HP2 Hsz HSep.
  destruct (eq_block b1 b2) as [->|Hne].
  - rewrite H1 in H2. injection H2 as -> ->. right.
    destruct HSep as [HS|[HS|HS]]; [congruence|left; lia|right; lia].
  - destruct (eq_block b1' b2') as [->|Hne']; [|left; exact Hne'].
    right.
    destruct (zle (o1 + d1 + sz) (o2 + d2)) as [|Hgt1]; [left; assumption|].
    destruct (zle (o2 + d2 + sz) (o1 + d1)) as [|Hgt2]; [right; assumption|].
    exfalso.
    set (x := Z.max (o1 + d1) (o2 + d2)).
    destruct (Mem.mi_no_overlap _ _ _ Hinj b1 b2' d1 b2 b2' d2 (x - d1) (x - d2)
      Hne H1 H2) as [HN|HN].
    + apply HP1. unfold x. lia.
    + apply HP2. unfold x. lia.
    + exact (HN eq_refl).
    + apply HN. lia.
Qed.

Ltac inv_lessdef :=
  repeat match goal with
  | H : Val.lessdef_list (_ :: _) _ |- _ => inv H
  | H : Val.lessdef_list nil _ |- _ => inv H
  | H : Val.lessdef (Vptr _ _) _ |- _ => inv H
  | H : Val.lessdef (Vlong _) _ |- _ => inv H
  end.

Ltac inv_inject :=
  repeat match goal with
  | H : Val.inject_list _ (_ :: _) _ |- _ => inv H
  | H : Val.inject_list _ nil _ |- _ => inv H
  | H : Val.inject _ (Vptr _ _) _ |- _ => inv H
  | H : Val.inject _ (Vlong _) _ |- _ => inv H
  end.

Lemma libc_memcpy_sem_ok : extcall_properties libc_memcpy_sem memcpy_sig.
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
  intros ge vargs m1 t vres m2 m1' vargs' H Hext Hargs. inv H. inv_lessdef.
  match goal with
  | HLB : Mem.loadbytes m1 bsrc _ _ = Some bytes,
    HSB : Mem.storebytes m1 bdst _ bytes = Some m2 |- _ =>
      pose proof (Mem.loadbytes_length _ _ _ _ _ HLB) as LEN;
      destruct (Mem.loadbytes_extends _ _ _ _ _ _ Hext HLB) as [bytes2 [A B]];
      destruct (Mem.storebytes_within_extends _ _ _ _ _ _ _ Hext HSB B) as [m2' [C D]];
      exists (Vptr bdst odst), m2';
      split; [econstructor; eauto|];
      split; [constructor|];
      split; [exact D|];
      eapply Mem.storebytes_unchanged_on; [exact C|];
      unfold loc_out_of_bounds; intros i Hi HOOB; apply HOOB;
      apply Mem.perm_cur_max; apply Mem.perm_implies with Writable; [|constructor];
      eapply Mem.storebytes_range_perm; [exact HSB|];
      rewrite (list_forall2_length B); exact Hi
  end.
- (* injections *)
  intros ge1 ge2 vargs m1 t vres m2 f m1' vargs' Hsym H Hinj Hargs. inv H. inv_inject.
  match goal with
  | HLB : Mem.loadbytes m1 bsrc _ _ = Some bytes,
    HSB : Mem.storebytes m1 bdst _ bytes = Some m2,
    HFS : f bsrc = Some (?bs2, ?ds), HFD : f bdst = Some (?bd2, ?dd),
    HPOS : Int64.unsigned sz > 0,
    HSEP : bsrc <> bdst \/ _ |- _ =>
      set (sz' := Int64.unsigned sz) in *;
      pose proof (Mem.loadbytes_length _ _ _ _ _ HLB) as LEN;
      assert (RPSRC : Mem.range_perm m1 bsrc (Ptrofs.unsigned osrc)
          (Ptrofs.unsigned osrc + sz') Cur Nonempty)
        by (eapply Mem.range_perm_implies;
            [eapply Mem.loadbytes_range_perm; exact HLB|constructor]);
      assert (RPDST : Mem.range_perm m1 bdst (Ptrofs.unsigned odst)
          (Ptrofs.unsigned odst + sz') Cur Nonempty)
        by (replace sz' with (Z.of_nat (length bytes)) by (rewrite LEN; apply Z2Nat.id; lia);
            eapply Mem.range_perm_implies;
            [eapply Mem.storebytes_range_perm; exact HSB|constructor]);
      assert (PSRC : Mem.perm m1 bsrc (Ptrofs.unsigned osrc) Cur Nonempty)
        by (apply RPSRC; lia);
      assert (PDST : Mem.perm m1 bdst (Ptrofs.unsigned odst) Cur Nonempty)
        by (apply RPDST; lia);
      pose proof (Mem.address_inject _ _ _ _ _ _ _ _ Hinj PSRC HFS) as EQ1;
      pose proof (Mem.address_inject _ _ _ _ _ _ _ _ Hinj PDST HFD) as EQ2;
      destruct (Mem.loadbytes_inject _ _ _ _ _ _ _ _ _ Hinj HLB HFS) as [bytes2 [A B]];
      destruct (Mem.storebytes_mapped_inject _ _ _ _ _ _ _ _ _ _ Hinj HSB HFD B) as [m2' [C D]];
      assert (HD : bs2 <> bd2 \/
          Ptrofs.unsigned osrc + ds + sz' <= Ptrofs.unsigned odst + dd \/
          Ptrofs.unsigned odst + dd + sz' <= Ptrofs.unsigned osrc + ds)
        by (eapply inject_disjoint_ranges with (m := m1);
            [exact Hinj|exact HFS|exact HFD
            |apply Mem.range_perm_max with Cur; exact RPSRC
            |apply Mem.range_perm_max with Cur; exact RPDST
            |lia|exact HSEP]);
      exists f, (Vptr bd2 (Ptrofs.add odst (Ptrofs.repr dd))), m2';
      split;
        [econstructor; [exact HPOS| |rewrite EQ1; exact A|rewrite EQ2; exact C];
         rewrite EQ1, EQ2; fold sz';
         destruct HD as [HD|[HD|HD]];
           [left; exact HD|right; left; lia|right; right; lia]|];
      split; [econstructor; [exact HFD|reflexivity]|];
          split; [exact D|];
          split; [eapply Mem.storebytes_unchanged_on; [exact HSB|];
                  unfold loc_unmapped; intros; congruence|];
          split; [eapply Mem.storebytes_unchanged_on; [exact C|];
                  unfold loc_out_of_reach; intros i Hi HOOR;
                  eapply HOOR; [exact HFD|];
                  apply Mem.perm_cur_max; apply Mem.perm_implies with Writable; [|constructor];
                  eapply Mem.storebytes_range_perm; [exact HSB|];
                  rewrite (list_forall2_length B); lia|];
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

(** External functions other than memcpy: the empty semantics satisfies every
    property vacuously. *)
Definition no_behaviour : extcall_sem := fun _ _ _ _ _ _ => False.

Lemma no_behaviour_ok sg : extcall_properties no_behaviour sg.
Proof. constructor; unfold no_behaviour; intros; contradiction. Qed.

(** The libc contract satisfies the statement of [memcpy_model]. *)
Lemma libc_memcpy_sem_models : memcpy_model_for libc_memcpy_sem.
Proof.
  intros ge m bd od bs os n bytes _ _ HL HP HSep Hn _ _.
  assert (HLen : Z.of_nat (length bytes) = n).
  { rewrite (Mem.loadbytes_length _ _ _ _ _ HL). apply Z2Nat.id. lia. }
  destruct (Mem.range_perm_storebytes m bd (Ptrofs.unsigned od) bytes) as [m' HS].
  { rewrite HLen. exact HP. }
  exists m'. split; [exact HS|].
  assert (HU : Int64.unsigned (Int64.repr n) = n) by (apply Int64.unsigned_repr; lia).
  econstructor; rewrite ?HU; [lia|exact HSep|exact HL|exact HS].
Qed.

(** Model existence: an assignment of semantics to every external function
    that satisfies CompCert's required properties and the memcpy model. *)
Theorem memcpy_model_consistent :
  exists S : string -> signature -> extcall_sem,
    (forall id sg, extcall_properties (S id sg) sg) /\
    memcpy_model_for (S "memcpy"%string memcpy_sig).
Proof.
  exists (fun id sg =>
    if string_dec id "memcpy" then
      if signature_eq sg memcpy_sig then libc_memcpy_sem else no_behaviour
    else no_behaviour).
  split.
  - intros id sg. destruct (string_dec id "memcpy"); [|apply no_behaviour_ok].
    destruct (signature_eq sg memcpy_sig) as [->|]; [|apply no_behaviour_ok].
    exact libc_memcpy_sem_ok.
  - destruct (string_dec "memcpy" "memcpy") as [_|N]; [|contradiction].
    destruct (signature_eq memcpy_sig memcpy_sig) as [_|N]; [|contradiction].
    exact libc_memcpy_sem_models.
Qed.
