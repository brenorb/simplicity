(** Determinism of CompCert 3.14 Clight small-step semantics with
    [function_entry2], and the guarantees it yields at a function-call
    boundary.

    CompCert provides the big-step to small-step direction
    [ClightBigstep.eval_funcall_steps] but no determinism result for Clight.
    [step2_determ] proves it here from the Clight rules.  The only external
    fact used is CompCert's [external_call_determ], which covers builtins and
    external functions and rests on CompCert's own [external_functions_properties]
    and [inline_assembly_properties] axioms.  No determinism axiom is added.

    [eval_funcall_call_boundary] then turns a terminating, silent big-step
    call into guarantees about every small-step execution from the call
    state, up to and including the return to the caller's continuation. *)
From Coq Require Import Lia.
From compcert Require Import Coqlib Maps Integers Values AST Memory Events Globalenvs.
From compcert Require Import Smallstep Ctypes Cop Clight ClightBigstep.

(** * Determinism of expression evaluation and memory helpers *)

Section EXPR_DETERM.

Variable ge : genv.
Variable e : env.
Variable le : temp_env.
Variable m : mem.

Lemma deref_loc_determ ty b ofs bf v1 v2 :
  deref_loc ty m b ofs bf v1 -> deref_loc ty m b ofs bf v2 -> v1 = v2.
Proof.
  intros H1 H2. inv H1; inv H2; try congruence.
  inv H; inv H6; congruence.
Qed.

Lemma eval_expr_lvalue_determ :
  (forall a v1, eval_expr ge e le m a v1 ->
     forall v2, eval_expr ge e le m a v2 -> v1 = v2) /\
  (forall a b1 o1 bf1, eval_lvalue ge e le m a b1 o1 bf1 ->
     forall b2 o2 bf2, eval_lvalue ge e le m a b2 o2 bf2 ->
     b1 = b2 /\ o1 = o2 /\ bf1 = bf2).
Proof.
  apply eval_expr_lvalue_ind; intros;
    match goal with
    | H : eval_expr _ _ _ _ _ _ |- _ = _ => inv H
    | H : eval_lvalue _ _ _ _ _ _ _ _ |- _ /\ _ => inv H
    end;
    try (match goal with H : eval_lvalue _ _ _ _ _ _ _ _ |- _ => inv H; fail end);
    repeat match goal with
    | IH : forall v2, eval_expr _ _ _ _ ?a v2 -> _ = v2,
      H : eval_expr _ _ _ _ ?a _ |- _ =>
        let E := fresh in pose proof (IH _ H) as E; clear H;
        try (injection E; clear E; intros); try subst
    | IH : forall b2 o2 bf2, eval_lvalue _ _ _ _ ?a b2 o2 bf2 -> _,
      H : eval_lvalue _ _ _ _ ?a _ _ _ |- _ =>
        let E := fresh in pose proof (IH _ _ _ H) as E; clear H;
        destruct E as (? & ? & ?); try subst
    end;
    try (repeat split; congruence);
    try (eapply deref_loc_determ; eauto).
Qed.

Lemma eval_expr_determ a v1 v2 :
  eval_expr ge e le m a v1 -> eval_expr ge e le m a v2 -> v1 = v2.
Proof. intros. eapply (proj1 eval_expr_lvalue_determ); eauto. Qed.

Lemma eval_lvalue_determ a b1 o1 bf1 b2 o2 bf2 :
  eval_lvalue ge e le m a b1 o1 bf1 -> eval_lvalue ge e le m a b2 o2 bf2 ->
  b1 = b2 /\ o1 = o2 /\ bf1 = bf2.
Proof. intros. eapply (proj2 eval_expr_lvalue_determ); eauto. Qed.

Lemma eval_exprlist_determ al tyl vl1 vl2 :
  eval_exprlist ge e le m al tyl vl1 -> eval_exprlist ge e le m al tyl vl2 -> vl1 = vl2.
Proof.
  intros H1. revert vl2. induction H1; intros vl2 H2; inv H2; auto.
  assert (v1 = v0) by (eapply eval_expr_determ; eauto). subst.
  f_equal; [congruence|auto].
Qed.

End EXPR_DETERM.

Lemma assign_loc_determ ce ty m b ofs bf v m1 m2 :
  assign_loc ce ty m b ofs bf v m1 -> assign_loc ce ty m b ofs bf v m2 -> m1 = m2.
Proof.
  intros H1 H2. inv H1; inv H2; try congruence.
  match goal with
  | S1 : store_bitfield _ _ _ _ _ _ _ _ _ _, S2 : store_bitfield _ _ _ _ _ _ _ _ _ _ |- _ =>
      inv S1; inv S2
  end.
  congruence.
Qed.

Lemma alloc_variables_determ ge e m vars e1 m1 e2 m2 :
  alloc_variables ge e m vars e1 m1 -> alloc_variables ge e m vars e2 m2 ->
  e1 = e2 /\ m1 = m2.
Proof.
  intros H1. revert e2 m2. induction H1; intros e2' m2' H2; inv H2; auto.
  rewrite H in H9. inv H9. eauto.
Qed.

Lemma function_entry2_determ ge f vargs m e1 le1 m1 e2 le2 m2 :
  function_entry2 ge f vargs m e1 le1 m1 -> function_entry2 ge f vargs m e2 le2 m2 ->
  e1 = e2 /\ le1 = le2 /\ m1 = m2.
Proof.
  intros H1 H2. inv H1; inv H2.
  destruct (alloc_variables_determ _ _ _ _ _ _ _ _ H4 H8) as [-> ->].
  split; [reflexivity|]. split; [congruence|reflexivity].
Qed.

(** * Determinism of [step2] *)

Lemma match_traces_E0_inv (ge : Senv.t) t : match_traces ge E0 t -> t = E0.
Proof. intros H. inv H. reflexivity. Qed.

Ltac determ_step :=
  repeat match goal with
  | H1 : eval_expr ?ge ?e ?le ?m ?a ?v1, H2 : eval_expr ?ge ?e ?le ?m ?a ?v2 |- _ =>
      assert (v1 = v2) by (eapply eval_expr_determ; eauto); subst v2; clear H2
  | H1 : eval_lvalue ?ge ?e ?le ?m ?a ?b1 ?o1 ?f1,
    H2 : eval_lvalue ?ge ?e ?le ?m ?a ?b2 ?o2 ?f2 |- _ =>
      destruct (eval_lvalue_determ _ _ _ _ _ _ _ _ _ _ _ H1 H2) as (? & ? & ?);
      subst b2 o2 f2; clear H2
  | H1 : eval_exprlist ?ge ?e ?le ?m ?al ?tl ?v1, H2 : eval_exprlist ?ge ?e ?le ?m ?al ?tl ?v2 |- _ =>
      assert (v1 = v2) by (eapply eval_exprlist_determ; eauto); subst v2; clear H2
  | H1 : classify_fun ?ty = fun_case_f _ _ _, H2 : classify_fun ?ty = fun_case_f _ _ _ |- _ =>
      rewrite H1 in H2; injection H2; clear H2; intros; subst
  | H1 : ?x = Some ?a, H2 : ?x = Some ?b |- _ =>
      rewrite H1 in H2; injection H2; clear H2; intros; subst
  | H1 : assign_loc ?ce ?ty ?m ?b ?o ?f ?v ?m1, H2 : assign_loc ?ce ?ty ?m ?b ?o ?f ?v ?m2 |- _ =>
      assert (m1 = m2) by (eapply assign_loc_determ; eauto); subst m2; clear H2
  | H1 : function_entry2 ?ge ?f ?va ?m ?e1 ?l1 ?m1, H2 : function_entry2 ?ge ?f ?va ?m ?e2 ?l2 ?m2 |- _ =>
      destruct (function_entry2_determ _ _ _ _ _ _ _ _ _ _ H1 H2) as (? & ? & ?);
      subst e2 l2 m2; clear H2
  end.

Theorem step2_determ ge s t1 s1 t2 s2 :
  step2 ge s t1 s1 -> step2 ge s t2 s2 ->
  match_traces ge t1 t2 /\ (t1 = t2 -> s1 = s2).
Proof.
  intros H1 H2. unfold step2 in *.
  inv H1; inv H2; determ_step;
    try (match goal with H : _ \/ _ |- _ => destruct H as [Hx|Hx]; discriminate Hx end);
    try (simpl in *; contradiction);
    try (split; [constructor|intros; reflexivity]);
    try (match goal with
         | E1 : external_call ?ef ?g ?va ?m ?t1 ?r1 ?m1,
           E2 : external_call ?ef ?g ?va ?m ?t2 ?r2 ?m2 |- _ =>
             destruct (external_call_determ _ _ _ _ _ _ _ _ _ _ E1 E2) as [Hm Heq];
             split; [exact Hm|intros ->; destruct (Heq eq_refl) as [-> ->]; reflexivity]
         end).
Qed.

Corollary step2_silent_determ ge s s1 t2 s2 :
  step2 ge s E0 s1 -> step2 ge s t2 s2 -> t2 = E0 /\ s2 = s1.
Proof.
  intros H1 H2. destruct (step2_determ _ _ _ _ _ _ H1 H2) as [Hm Heq].
  apply match_traces_E0_inv in Hm. subst. split; [reflexivity|].
  symmetry. apply Heq. reflexivity.
Qed.

(** * Silent deterministic paths *)

Section PATHS.

Variable ge : genv.

Lemma starN_silent_determ n s a t b :
  starN step2 ge n s E0 a -> starN step2 ge n s t b -> t = E0 /\ b = a.
Proof.
  intros Ha. remember E0 as t0 eqn:HE. revert t b.
  induction Ha as [s|n s t0 t1 s1 t2 s2 Hstep Hrest IH Ht]; intros t b Hb.
  - inversion Hb; subst. split; reflexivity.
  - inversion Hb as [|n' s' tb t1b sb t2b s''b Hsb Hrb Htb]; subst.
    symmetry in Ht. apply Eapp_E0_inv in Ht. destruct Ht as [-> ->].
    destruct (step2_silent_determ _ _ _ _ _ Hstep Hsb) as [-> ->].
    destruct (IH eq_refl _ _ Hrb) as [-> ->]. split; reflexivity.
Qed.

Lemma starN_split n s t s' j :
  starN step2 ge n s t s' -> (j <= n)%nat ->
  exists sm t1 t2,
    starN step2 ge j s t1 sm /\ starN step2 ge (n - j) sm t2 s' /\ t = t1 ** t2.
Proof.
  intros H. revert j.
  induction H as [s|n s t t1 s1 t2 s2 Hstep Hrest IH Ht]; intros j Hj.
  - assert (j = O) by lia. subst. exists s, E0, E0.
    split; [constructor|]. split; [constructor|reflexivity].
  - destruct j as [|j].
    + exists s, E0, t. split; [constructor|]. split; [|reflexivity].
      econstructor; eauto.
    + destruct (IH j ltac:(lia)) as (sm & ta & tb & H1 & H2 & H3).
      exists sm, (t1 ** ta), tb. split; [econstructor; eauto|].
      split; [exact H2|]. subst. symmetry. apply Eapp_assoc.
Qed.

Lemma starN_silent_follow n s s' :
  starN step2 ge n s E0 s' ->
  forall j t S, starN step2 ge j s t S ->
  ((j <= n)%nat -> t = E0 /\ starN step2 ge (n - j) S E0 s') /\
  ((n <= j)%nat -> starN step2 ge (j - n) s' t S).
Proof.
  intros Hpath j t S HS. split.
  - intros Hj.
    destruct (starN_split _ _ _ _ _ Hpath Hj) as (sm & ta & tb & H1 & H2 & Ht).
    symmetry in Ht. apply Eapp_E0_inv in Ht. destruct Ht as [-> ->].
    destruct (starN_silent_determ _ _ _ _ _ H1 HS) as [-> ->]. auto.
  - intros Hj.
    destruct (starN_split _ _ _ _ _ HS Hj) as (sm & ta & tb & H1 & H2 & Ht).
    destruct (starN_silent_determ _ _ _ _ _ Hpath H1) as [-> ->].
    subst. exact H2.
Qed.

Lemma forever_silent_path n s s' T :
  starN step2 ge n s E0 s' -> forever step2 ge s T -> forever step2 ge s' T.
Proof.
  intros H. remember E0 as t0 eqn:HE. revert T.
  induction H as [s|n s t t1 s1 t2 s2 Hstep Hrest IH Ht]; intros T HF; [exact HF|].
  subst. symmetry in Ht. apply Eapp_E0_inv in Ht. destruct Ht as [-> ->].
  inversion HF as [s0 tf s3 T' Hsf Hff HT]; subst.
  destruct (step2_silent_determ _ _ _ _ _ Hstep Hsf) as [-> ->].
  apply IH; [reflexivity|exact Hff].
Qed.

End PATHS.

(** * Executions under an extended continuation *)

Fixpoint cont_app (k0 k : cont) : cont :=
  match k0 with
  | Kstop => k
  | Kseq s k1 => Kseq s (cont_app k1 k)
  | Kloop1 s1 s2 k1 => Kloop1 s1 s2 (cont_app k1 k)
  | Kloop2 s1 s2 k1 => Kloop2 s1 s2 (cont_app k1 k)
  | Kswitch k1 => Kswitch (cont_app k1 k)
  | Kcall o f e le k1 => Kcall o f e le (cont_app k1 k)
  end.

Definition state_app (k : cont) (s : state) : state :=
  match s with
  | State f st k0 e le m => State f st (cont_app k0 k) e le m
  | Callstate fd args k0 m => Callstate fd args (cont_app k0 k) m
  | Returnstate v k0 m => Returnstate v (cont_app k0 k) m
  end.

Fixpoint cont_size (k : cont) : nat :=
  match k with
  | Kstop => O
  | Kseq _ k | Kloop1 _ _ k | Kloop2 _ _ k | Kswitch k | Kcall _ _ _ _ k =>
      S (cont_size k)
  end.

Lemma cont_size_app k0 k : cont_size (cont_app k0 k) = (cont_size k0 + cont_size k)%nat.
Proof. induction k0; simpl; auto. Qed.

Lemma cont_app_self k0 k : cont_app k0 k = k -> k0 = Kstop.
Proof.
  intros H. apply (f_equal cont_size) in H. rewrite cont_size_app in H.
  destruct k0; simpl in H; [reflexivity|lia..].
Qed.

Lemma call_cont_app k0 k :
  is_call_cont k -> call_cont (cont_app k0 k) = cont_app (call_cont k0) k.
Proof.
  intros Hk. induction k0; simpl; auto.
  destruct k; simpl in *; tauto || reflexivity.
Qed.

Lemma is_call_cont_app k0 k :
  is_call_cont k0 -> is_call_cont k -> is_call_cont (cont_app k0 k).
Proof. destruct k0; simpl; tauto. Qed.

Fixpoint find_label_app lbl s k0 k {struct s} :
  find_label lbl s (cont_app k0 k) =
    option_map (fun p => (fst p, cont_app (snd p) k)) (find_label lbl s k0)
with find_label_ls_app lbl sl k0 k {struct sl} :
  find_label_ls lbl sl (cont_app k0 k) =
    option_map (fun p => (fst p, cont_app (snd p) k)) (find_label_ls lbl sl k0).
Proof.
  - destruct s; simpl; auto.
    + change (Kseq s2 (cont_app k0 k)) with (cont_app (Kseq s2 k0) k).
      rewrite find_label_app. destruct (find_label lbl s1 (Kseq s2 k0)); simpl; auto.
    + rewrite find_label_app. destruct (find_label lbl s1 k0); simpl; auto.
    + change (Kloop1 s1 s2 (cont_app k0 k)) with (cont_app (Kloop1 s1 s2 k0) k).
      rewrite find_label_app. destruct (find_label lbl s1 (Kloop1 s1 s2 k0)); simpl; auto.
      change (Kloop2 s1 s2 (cont_app k0 k)) with (cont_app (Kloop2 s1 s2 k0) k).
      apply find_label_app.
    + change (Kswitch (cont_app k0 k)) with (cont_app (Kswitch k0) k).
      apply find_label_ls_app.
    + destruct (ident_eq lbl l); simpl; auto.
  - destruct sl; simpl; auto.
    change (Kseq (seq_of_labeled_statement sl) (cont_app k0 k))
      with (cont_app (Kseq (seq_of_labeled_statement sl) k0) k).
    rewrite find_label_app.
    destruct (find_label lbl s (Kseq (seq_of_labeled_statement sl) k0)); simpl; auto.
Qed.

Lemma step_app ge fe k s t s' :
  is_call_cont k -> step ge fe s t s' -> step ge fe (state_app k s) t (state_app k s').
Proof.
  intros Hk H. inv H; simpl; try (rewrite <- call_cont_app by exact Hk);
    try (econstructor; eauto; fail).
  - econstructor; eauto. apply is_call_cont_app; auto.
  - econstructor. rewrite call_cont_app by exact Hk.
    rewrite find_label_app. match goal with H : find_label _ _ _ = _ |- _ => rewrite H end.
    reflexivity.
Qed.

Lemma starN_app ge k n s t s' :
  is_call_cont k -> starN step2 ge n s t s' ->
  starN step2 ge n (state_app k s) t (state_app k s').
Proof.
  intros Hk H. induction H; econstructor; eauto. apply step_app; auto.
Qed.

Lemma returnstate_Kstop_nostep ge v m t s :
  ~ step2 ge (Returnstate v Kstop m) t s.
Proof. intros H. inv H. Qed.

(** * Guarantees at a call boundary *)

(** [call_boundary ge fd args k m res mf n] describes every small-step
    execution starting from the call state [Callstate fd args k m]:
    - [cb_path]: the call reaches [Returnstate res k mf] in [n] silent steps;
    - [cb_before]: any execution of fewer than [n] steps is silent, has not
      yet returned to [k], and ends in a state with exactly one successor,
      which is silent (no stuck state and no alternative);
    - [cb_after]: any execution of at least [n] steps passes through
      [Returnstate res k mf] after exactly [n] steps;
    - [cb_forever]: an infinite execution is the silent call followed by an
      infinite execution of the caller from [Returnstate res k mf].
    Nothing is claimed about the caller's execution after the return. *)
Record call_boundary (ge : genv) (fd : fundef) (args : list val) (k : cont)
    (m : mem) (res : val) (mf : mem) (n : nat) : Prop := {
  cb_path : starN step2 ge n (Callstate fd args k m) E0 (Returnstate res k mf);
  cb_before : forall j t S, (j < n)%nat ->
    starN step2 ge j (Callstate fd args k m) t S ->
    t = E0 /\
    (forall v k' m', S = Returnstate v k' m' -> k' <> k) /\
    exists S', step2 ge S E0 S' /\
      forall t' S'', step2 ge S t' S'' -> t' = E0 /\ S'' = S';
  cb_after : forall j t S, (n <= j)%nat ->
    starN step2 ge j (Callstate fd args k m) t S ->
    starN step2 ge (j - n) (Returnstate res k mf) t S;
  cb_forever : forall T, forever step2 ge (Callstate fd args k m) T ->
    forever step2 ge (Returnstate res k mf) T
}.

Theorem eval_funcall_call_boundary p m fd args mf res k :
  Clight2.eval_funcall (Clight.globalenv p) m fd args E0 mf res -> is_call_cont k ->
  exists n, call_boundary (Clight.globalenv p) fd args k m res mf n.
Proof.
  intros Hcall Hk.
  pose proof (eval_funcall_steps function_entry2 p _ _ _ _ _ _ Hcall Kstop I) as Hstar.
  apply star_starN in Hstar. destruct Hstar as [n H0].
  pose proof (starN_app _ _ _ _ _ _ Hk H0) as Hk0. simpl in Hk0.
  exists n. constructor.
  - exact Hk0.
  - intros j t S Hj HS.
    destruct (starN_split _ _ _ _ _ _ H0 (Nat.lt_le_incl _ _ Hj))
      as (S0 & ta & tb & HA & HB & Ht).
    symmetry in Ht. apply Eapp_E0_inv in Ht. destruct Ht; subst.
    pose proof (starN_app _ _ _ _ _ _ Hk HA) as HAk. simpl in HAk.
    destruct (starN_silent_determ _ _ _ _ _ _ HAk HS) as [-> ->].
    split; [reflexivity|]. split.
    + intros v k' m' Heq. destruct S0; simpl in Heq; inv Heq.
      intros Hkk. apply cont_app_self in Hkk. subst.
      inv HB; [lia|]. eapply returnstate_Kstop_nostep; eauto.
    + inv HB; [lia|]. symmetry in H3. apply Eapp_E0_inv in H3. destruct H3; subst.
      exists (state_app k s'). split; [apply step_app; auto|].
      intros t' S'' HS''. eapply step2_silent_determ; [apply step_app; eauto|exact HS''].
  - intros j t S Hj HS. exact (proj2 (starN_silent_follow _ _ _ _ Hk0 _ _ _ HS) Hj).
  - intros T HF. eapply forever_silent_path; eauto.
Qed.

(** Uniqueness of terminating big-step results. *)
Theorem eval_funcall_unique p m fd args mf res t' m' res' :
  Clight2.eval_funcall (Clight.globalenv p) m fd args E0 mf res ->
  Clight2.eval_funcall (Clight.globalenv p) m fd args t' m' res' ->
  t' = E0 /\ m' = mf /\ res' = res.
Proof.
  intros H1 H2.
  pose proof (eval_funcall_steps function_entry2 p _ _ _ _ _ _ H1 Kstop I) as S1.
  pose proof (eval_funcall_steps function_entry2 p _ _ _ _ _ _ H2 Kstop I) as S2.
  apply star_starN in S1. destruct S1 as [n P1].
  apply star_starN in S2. destruct S2 as [j P2].
  destruct (starN_silent_follow _ _ _ _ P1 _ _ _ P2) as [Hle Hge].
  destruct (Nat.le_ge_cases j n) as [Hj|Hj].
  - destruct (Hle Hj) as [-> Hrest].
    destruct (n - j)%nat eqn:E.
    + inv Hrest. auto.
    + inv Hrest. exfalso. eapply returnstate_Kstop_nostep; eauto.
  - specialize (Hge Hj). destruct (j - n)%nat eqn:E.
    + inv Hge. auto.
    + inv Hge. exfalso. eapply returnstate_Kstop_nostep; eauto.
Qed.

(** At the top level ([Kstop]) the call has no infinite execution, and every
    maximal execution ends in [Returnstate res Kstop mf] with no events. *)
Theorem eval_funcall_Kstop_terminates p m fd args mf res :
  Clight2.eval_funcall (Clight.globalenv p) m fd args E0 mf res ->
  (forall T, ~ forever step2 (Clight.globalenv p) (Callstate fd args Kstop m) T) /\
  (forall t S, star step2 (Clight.globalenv p) (Callstate fd args Kstop m) t S ->
    (forall t' S', ~ step2 (Clight.globalenv p) S t' S') ->
    t = E0 /\ S = Returnstate res Kstop mf).
Proof.
  intros H. destruct (eval_funcall_call_boundary _ _ _ _ _ _ Kstop H I) as [n B].
  split.
  - intros T HF. apply (cb_forever _ _ _ _ _ _ _ _ B) in HF.
    inv HF. eapply returnstate_Kstop_nostep; eauto.
  - intros t S HS Hstuck. pose proof HS as HS'. apply star_starN in HS'. destruct HS' as [j HJ].
    destruct (Nat.lt_ge_cases j n) as [Hj|Hj].
    + destruct (cb_before _ _ _ _ _ _ _ _ B _ _ _ Hj HJ) as (_ & _ & S' & HS' & _).
      exfalso. eapply Hstuck; eauto.
    + pose proof (cb_after _ _ _ _ _ _ _ _ B _ _ _ Hj HJ) as HA.
      destruct (j - n)%nat eqn:E; inv HA; [auto|].
      exfalso. eapply returnstate_Kstop_nostep; eauto.
Qed.

(** A bundle of the execution guarantees for a terminating silent call. *)
Definition silent_call_guarantees (ge : genv) (fd : fundef) (args : list val)
    (m : mem) (res : val) (mf : mem) : Prop :=
  (forall k, is_call_cont k -> exists n, call_boundary ge fd args k m res mf n) /\
  (forall t' m' res', Clight2.eval_funcall ge m fd args t' m' res' ->
    t' = E0 /\ m' = mf /\ res' = res) /\
  (forall T, ~ forever step2 ge (Callstate fd args Kstop m) T) /\
  (forall t S, star step2 ge (Callstate fd args Kstop m) t S ->
    (forall t' S', ~ step2 ge S t' S') ->
    t = E0 /\ S = Returnstate res Kstop mf).

Theorem eval_funcall_silent_guarantees p m fd args mf res :
  Clight2.eval_funcall (Clight.globalenv p) m fd args E0 mf res ->
  silent_call_guarantees (Clight.globalenv p) fd args m res mf.
Proof.
  intros H. split; [intros k Hk; eapply eval_funcall_call_boundary; eauto|].
  split; [intros; eapply eval_funcall_unique; eauto|].
  exact (eval_funcall_Kstop_terminates _ _ _ _ _ _ H).
Qed.
