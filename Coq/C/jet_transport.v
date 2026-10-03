(** Transport of Clight big-step executions between two global environments.

    The Bitcoin and Elements translation units contain the same core helper
    functions (frame readers/writers, bit helpers, ...) as the core jets
    translation unit, but their global blocks are numbered differently and
    their composite environments are larger.  A function body that only
    - reads/writes through temporaries and locals,
    - calls named functions whose bodies are again of this kind,
    - uses types whose size, alignment and field offsets agree in both
      environments,
    executes identically in both.  Every side condition is a boolean check by
    computation, discharged once per helper by [vm_compute].  No external call,
    builtin or global variable is accessed by transported code. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps Errors Memory Values.
From compcert Require Import Globalenvs Events ClightBigstep.
Import ListNotations.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 30.

Definition ptr_agreeb (ce1 ce2 : composite_env) (t : type) : bool :=
  match t with
  | Tpointer t' _ | Tarray t' _ _ => Z.eqb (sizeof ce1 t') (sizeof ce2 t')
  | _ => true
  end.

Lemma ptr_agree_typeconv ce1 ce2 t : ptr_agreeb ce1 ce2 t = true -> ptr_agreeb ce1 ce2 (typeconv t) = true.
Proof. destruct t; simpl; auto; destruct i; simpl; auto. Qed.

Lemma classify_add_pointee ce1 ce2 t1 t2 :
  ptr_agreeb ce1 ce2 t1 = true -> ptr_agreeb ce1 ce2 t2 = true ->
  (forall ty si, classify_add t1 t2 = add_case_pi ty si -> sizeof ce1 ty = sizeof ce2 ty) /\
  (forall ty, classify_add t1 t2 = add_case_pl ty -> sizeof ce1 ty = sizeof ce2 ty) /\
  (forall ty si, classify_add t1 t2 = add_case_ip si ty -> sizeof ce1 ty = sizeof ce2 ty) /\
  (forall ty, classify_add t1 t2 = add_case_lp ty -> sizeof ce1 ty = sizeof ce2 ty).
Proof.
  intros H1 H2. apply ptr_agree_typeconv in H1. apply ptr_agree_typeconv in H2.
  unfold classify_add. destruct (typeconv t1), (typeconv t2); simpl in H1, H2;
  repeat split; intros; try discriminate; try (inversion H; subst; apply Z.eqb_eq; assumption);
  try (apply Z.eqb_eq; assumption).
Qed.

Lemma classify_sub_pointee ce1 ce2 t1 t2 :
  ptr_agreeb ce1 ce2 t1 = true ->
  (forall ty si, classify_sub t1 t2 = sub_case_pi ty si -> sizeof ce1 ty = sizeof ce2 ty) /\
  (forall ty, classify_sub t1 t2 = sub_case_pp ty -> sizeof ce1 ty = sizeof ce2 ty) /\
  (forall ty, classify_sub t1 t2 = sub_case_pl ty -> sizeof ce1 ty = sizeof ce2 ty).
Proof.
  intros H1. apply ptr_agree_typeconv in H1.
  unfold classify_sub. destruct (typeconv t1), (typeconv t2); simpl in H1;
  repeat split; intros; try discriminate; try (inversion H; subst; apply Z.eqb_eq; assumption).
Qed.

Definition binop_agreeb ce1 ce2 op t1 t2 : bool :=
  match op with
  | Oadd => ptr_agreeb ce1 ce2 t1 && ptr_agreeb ce1 ce2 t2
  | Osub => ptr_agreeb ce1 ce2 t1
  | _ => true
  end.

Lemma sem_binary_operation_agree ce1 ce2 op v1 t1 v2 t2 m :
  binop_agreeb ce1 ce2 op t1 t2 = true ->
  sem_binary_operation ce1 op v1 t1 v2 t2 m = sem_binary_operation ce2 op v1 t1 v2 t2 m.
Proof.
  intros H. destruct op; try reflexivity; simpl in H.
  - apply andb_prop in H as [H1 H2].
    destruct (classify_add_pointee ce1 ce2 t1 t2 H1 H2) as (Hpi & Hpl & Hip & Hlp).
    unfold sem_binary_operation, sem_add, sem_add_ptr_int, sem_add_ptr_long.
    destruct (classify_add t1 t2) eqn:Hc; try reflexivity.
    + rewrite (Hpi ty si eq_refl). reflexivity.
    + rewrite (Hpl ty eq_refl). reflexivity.
    + rewrite (Hip ty si eq_refl). reflexivity.
    + rewrite (Hlp ty eq_refl). reflexivity.
  - destruct (classify_sub_pointee ce1 ce2 t1 t2 H) as (Hpi & Hpp & Hpl).
    unfold sem_binary_operation, sem_sub.
    destruct (classify_sub t1 t2) eqn:Hc; try reflexivity.
    + rewrite (Hpi ty si eq_refl). reflexivity.
    + rewrite (Hpp ty eq_refl). reflexivity.
    + rewrite (Hpl ty eq_refl). reflexivity.
Qed.

(** ** Agreement checks between two genvs *)

Section Checks.
Variables ge1 ge2 : Clight.genv.

Definition szb (t : type) : bool := Z.eqb (sizeof (genv_cenv ge1) t) (sizeof (genv_cenv ge2) t).
Definition albb (t : type) : bool :=
  Z.eqb (alignof_blockcopy (genv_cenv ge1) t) (alignof_blockcopy (genv_cenv ge2) t).
Definition alb (t : type) : bool := Z.eqb (alignof (genv_cenv ge1) t) (alignof (genv_cenv ge2) t).

Definition fieldb (t : type) (i : ident) : bool :=
  match t with
  | Tstruct id _ =>
    match (genv_cenv ge1)!id, (genv_cenv ge2)!id with
    | Some c1, Some c2 =>
      match field_offset (genv_cenv ge1) i (co_members c1),
            field_offset (genv_cenv ge2) i (co_members c2) with
      | OK (d1, Full), OK (d2, Full) => Z.eqb d1 d2
      | _, _ => false
      end
    | _, _ => false
    end
  | _ => false
  end.

Fixpoint expr_okb (a : expr) : bool :=
  match a with
  | Econst_int _ _ | Econst_float _ _ | Econst_single _ _ | Econst_long _ _ => true
  | Evar id _ => match Genv.find_symbol ge1 id with None => true | Some _ => false end
  | Etempvar _ _ => true
  | Ederef a1 _ => expr_okb a1
  | Efield a1 i _ => expr_okb a1 && fieldb (typeof a1) i
  | Eaddrof a1 _ => expr_okb a1
  | Eunop _ a1 _ => expr_okb a1
  | Ebinop op a1 a2 _ =>
      expr_okb a1 && expr_okb a2 && binop_agreeb (genv_cenv ge1) (genv_cenv ge2) op (typeof a1) (typeof a2)
  | Ecast a1 _ => expr_okb a1
  | Esizeof t _ => szb t
  | Ealignof t _ => alb t
  end.

Definition exprs_okb (al : list expr) : bool := forallb expr_okb al.

(** A syntactically constant condition (the compiled form of a disabled
    assertion): only the branch that can run need satisfy the check. *)
Definition const_cond (a : expr) : option bool :=
  match a with
  | Econst_int n _ => Some (negb (Int.eq n Int.zero))
  | Eunop Onotbool (Econst_int n _) _ => Some (Int.eq n Int.zero)
  | _ => None
  end.

Fixpoint stmt_okb (C V : list ident) (s : statement) : bool :=
  match s with
  | Sskip => true
  | Sassign a1 a2 => expr_okb a1 && expr_okb a2 && szb (typeof a1) && albb (typeof a1)
  | Sset _ a => expr_okb a
  | Scall _ (Evar id (Tfunction _ _ _)) al =>
      existsb (Pos.eqb id) C && negb (existsb (Pos.eqb id) V) && exprs_okb al
  | Scall _ _ _ => false
  | Sbuiltin _ _ _ _ => false
  | Ssequence s1 s2 => stmt_okb C V s1 && stmt_okb C V s2
  | Sifthenelse a s1 s2 =>
      expr_okb a &&
      match const_cond a with
      | Some true => stmt_okb C V s1
      | Some false => stmt_okb C V s2
      | None => stmt_okb C V s1 && stmt_okb C V s2
      end
  | Sloop s1 s2 => stmt_okb C V s1 && stmt_okb C V s2
  | Sbreak | Scontinue => true
  | Sreturn None => true
  | Sreturn (Some a) => expr_okb a
  | Sswitch _ _ => false
  | Slabel _ _ => false
  | Sgoto _ => false
  end.

Definition vars_okb (vars : list (ident * type)) : bool := forallb (fun p => szb (snd p)) vars.

Definition fundef_okb (C : list ident) (fd : fundef) : bool :=
  match fd with
  | Internal f => vars_okb (fn_vars f) && stmt_okb C (map fst (fn_vars f)) (fn_body f)
  | External _ _ _ _ => false
  end.

(** A callee name is transportable when both genvs define it by the same
    internal function and that function's body passes the check. *)
Definition callable (C : list ident) (id : ident) : Prop :=
  forall b1 fd, Genv.find_symbol ge1 id = Some b1 -> Genv.find_funct_ptr ge1 b1 = Some fd ->
    (exists b2, Genv.find_symbol ge2 id = Some b2 /\ Genv.find_funct_ptr ge2 b2 = Some fd) /\
    fundef_okb C fd = true.

Definition transportable (C : list ident) : Prop := forall id, In id C -> callable C id.

(** ** Expressions *)

Ltac kill_lvalue :=
  match goal with Hl : eval_lvalue _ _ _ _ _ _ _ _ |- _ => inversion Hl end.

Lemma const_cond_sound e le m a v b c :
  const_cond a = Some c -> eval_expr ge1 e le m a v -> bool_val v (typeof a) m = Some b -> b = c.
Proof.
  intros Hc Hv Hb. destruct a; simpl in Hc; try discriminate.
  - inversion Hc; subst. inversion Hv; subst; [|kill_lvalue].
    simpl in Hb. unfold bool_val in Hb.
    destruct (classify_bool t); simpl in Hb; try discriminate; inversion Hb; reflexivity.
  - destruct u; try discriminate. destruct a; try discriminate. inversion Hc; subst.
    inversion Hv; subst; [|kill_lvalue].
    match goal with Hi : eval_expr _ _ _ _ (Econst_int _ _) _ |- _ =>
      inversion Hi; subst; [|kill_lvalue] end.
    match goal with Hu : sem_unary_operation Onotbool _ _ _ = Some _ |- _ => rename Hu into H4 end.
    simpl in H4. unfold sem_notbool, bool_val in H4. simpl in Hb.
    destruct (classify_bool t0) eqn:Hc0; simpl in H4; try discriminate.
    inversion H4; subst. unfold bool_val in Hb.
    destruct (Int.eq i Int.zero) eqn:Hi; destruct (classify_bool t); cbn in Hb;
      try discriminate; inversion Hb; subst; vm_compute; reflexivity.
Qed.

Lemma szb_eq t : szb t = true -> sizeof (genv_cenv ge1) t = sizeof (genv_cenv ge2) t.
Proof. unfold szb; intros H; apply Z.eqb_eq; exact H. Qed.

Lemma alb_eq t : alb t = true -> alignof (genv_cenv ge1) t = alignof (genv_cenv ge2) t.
Proof. unfold alb; intros H; apply Z.eqb_eq; exact H. Qed.

Lemma albb_eq t : albb t = true ->
  alignof_blockcopy (genv_cenv ge1) t = alignof_blockcopy (genv_cenv ge2) t.
Proof. unfold albb; intros H; apply Z.eqb_eq; exact H. Qed.

Lemma eval_expr_transport e le m :
  (forall a v, eval_expr ge1 e le m a v -> expr_okb a = true -> eval_expr ge2 e le m a v) /\
  (forall a b ofs bf, eval_lvalue ge1 e le m a b ofs bf -> expr_okb a = true ->
     eval_lvalue ge2 e le m a b ofs bf).
Proof.
  apply (eval_expr_lvalue_ind ge1 e le m
    (fun a v => expr_okb a = true -> eval_expr ge2 e le m a v)
    (fun a b ofs bf => expr_okb a = true -> eval_lvalue ge2 e le m a b ofs bf)).
  - intros; constructor.
  - intros; constructor.
  - intros; constructor.
  - intros; constructor.
  - intros id ty v Hle _; constructor; exact Hle.
  - intros a ty loc ofs Hl IH Hok. simpl in Hok. constructor. apply IH; exact Hok.
  - intros op a ty v1 v Ha IH Hop Hok. simpl in Hok. econstructor; [apply IH; exact Hok|exact Hop].
  - intros op a1 a2 ty v1 v2 v Ha1 IH1 Ha2 IH2 Hop Hok. simpl in Hok.
    apply andb_prop in Hok as [Hok Hb]. apply andb_prop in Hok as [Hok1 Hok2].
    econstructor; [apply IH1; exact Hok1|apply IH2; exact Hok2|].
    rewrite <- (sem_binary_operation_agree (genv_cenv ge1) (genv_cenv ge2) op v1 (typeof a1) v2 (typeof a2) m Hb).
    exact Hop.
  - intros a ty v1 v Ha IH Hc Hok. simpl in Hok. econstructor; [apply IH; exact Hok|exact Hc].
  - intros ty1 ty Hok. simpl in Hok. rewrite (szb_eq _ Hok). constructor.
  - intros ty1 ty Hok. simpl in Hok. rewrite (alb_eq _ Hok). constructor.
  - intros a loc ofs bf v Hl IH Hd Hok. econstructor; [apply IH; exact Hok|exact Hd].
  - intros id l ty He _. constructor; exact He.
  - intros id l ty He Hs Hok. simpl in Hok. rewrite Hs in Hok. discriminate.
  - intros a ty l ofs Ha IH Hok. simpl in Hok. constructor. apply IH; exact Hok.
  - intros a i ty l ofs id co att delta bf Ha IH Ht Hco Hfo Hok. simpl in Hok.
    apply andb_prop in Hok as [Hok Hf]. rewrite Ht in Hf. unfold fieldb in Hf.
    rewrite Hco in Hf.
    destruct ((genv_cenv ge2)!id) as [c2|] eqn:Hco2; [|discriminate].
    rewrite Hfo in Hf.
    destruct (field_offset (genv_cenv ge2) i (co_members c2)) as [[d2 bf2]|] eqn:Hfo2; [|destruct bf; discriminate].
    destruct bf; [|discriminate]. destruct bf2; [|discriminate].
    apply Z.eqb_eq in Hf. subst d2.
    eapply eval_Efield_struct with (co := c2) (delta := delta); [apply IH; exact Hok|exact Ht|exact Hco2|exact Hfo2].
  - intros a i ty l ofs id co att delta bf Ha IH Ht Hco Hfo Hok. simpl in Hok.
    apply andb_prop in Hok as [Hok Hf]. rewrite Ht in Hf. discriminate.
Qed.

Lemma eval_exprlist_transport e le m al tys vs :
  eval_exprlist ge1 e le m al tys vs -> exprs_okb al = true -> eval_exprlist ge2 e le m al tys vs.
Proof.
  induction 1; intros Hok; [constructor|].
  simpl in Hok. apply andb_prop in Hok as [Ha Hl].
  econstructor; [apply (proj1 (eval_expr_transport e le m)); eauto|eauto|apply IHeval_exprlist; exact Hl].
Qed.

Lemma assign_loc_transport ty m b ofs bf v m' :
  assign_loc ge1 ty m b ofs bf v m' -> szb ty = true -> albb ty = true ->
  assign_loc ge2 ty m b ofs bf v m'.
Proof.
  intros H Hsz Hal.
  destruct H as [v chunk m' Hmode Hstore|b' ofs' bytes m' Hmode Hal1 Hal2 Hsep Hload Hstore|sz sg pos width v m' v' Hbf].
  - eapply assign_loc_value; eassumption.
  - eapply assign_loc_copy with (bytes := bytes); try eassumption;
      rewrite <- ?(szb_eq _ Hsz), <- ?(albb_eq _ Hal); assumption.
  - eapply assign_loc_bitfield; eassumption.
Qed.

(** ** Local environments and allocation *)

Definition edom (e : env) (vars : list (ident * type)) : Prop :=
  forall id b ty, e!id = Some (b, ty) -> In (id, ty) vars.

Lemma alloc_variables_dom e m vars e' m' :
  alloc_variables ge1 e m vars e' m' ->
  forall id b ty, e'!id = Some (b, ty) -> e!id = Some (b, ty) \/ In (id, ty) vars.
Proof.
  induction 1; intros id0 b0 ty0 Hx.
  - left; exact Hx.
  - destruct (IHalloc_variables id0 b0 ty0 Hx) as [H1|H1].
    + rewrite PTree.gsspec in H1. destruct (peq id0 id) as [->|Hne].
      * inversion H1; subst. right; left; reflexivity.
      * left; exact H1.
    + right; right; exact H1.
Qed.

Lemma alloc_variables_transport e m vars e' m' :
  alloc_variables ge1 e m vars e' m' -> vars_okb vars = true -> alloc_variables ge2 e m vars e' m'.
Proof.
  induction 1; intros Hok; [constructor|].
  simpl in Hok. apply andb_prop in Hok as [Hs Hr].
  econstructor; [|apply IHalloc_variables; exact Hr].
  rewrite <- (szb_eq _ Hs). exact H.
Qed.

Lemma blocks_of_env_agree e vars :
  edom e vars -> vars_okb vars = true ->
  blocks_of_env ge1 e = blocks_of_env ge2 e.
Proof.
  intros Hd Hv. unfold blocks_of_env. apply map_ext_in. intros [id [b ty]] Hin.
  apply PTree.elements_complete in Hin. apply Hd in Hin.
  assert (Hs : szb ty = true).
  { unfold vars_okb in Hv. rewrite forallb_forall in Hv.
    exact (Hv (id, ty) Hin). }
  unfold block_of_binding. rewrite (szb_eq _ Hs). reflexivity.
Qed.

Lemma find_funct_ptr_of_funct b fd :
  Genv.find_funct ge1 (Vptr b Ptrofs.zero) = Some fd -> Genv.find_funct_ptr ge1 b = Some fd.
Proof. unfold Genv.find_funct. rewrite pred_dec_true by reflexivity. auto. Qed.

(** ** The main theorem *)

Theorem transport_main (C : list ident) (HC : transportable C) :
  (forall e le m s t le' m' out, Clight2.exec_stmt ge1 e le m s t le' m' out ->
     forall vars, edom e vars -> stmt_okb C (map fst vars) s = true ->
     Clight2.exec_stmt ge2 e le m s t le' m' out) /\
  (forall m fd args t m' res, Clight2.eval_funcall ge1 m fd args t m' res ->
     fundef_okb C fd = true -> Clight2.eval_funcall ge2 m fd args t m' res).
Proof.
  apply (exec_stmt_funcall_ind function_entry2 ge1
    (fun e le m s t le' m' out => forall vars, edom e vars -> stmt_okb C (map fst vars) s = true ->
       Clight2.exec_stmt ge2 e le m s t le' m' out)
    (fun m fd args t m' res => fundef_okb C fd = true -> Clight2.eval_funcall ge2 m fd args t m' res)).
  - intros; constructor.
  - intros e le m a1 a2 loc ofs bf v2 v m' Hl Hr Hc Ha vars Hd Hok. simpl in Hok.
    apply andb_prop in Hok as [Hok Hal]. apply andb_prop in Hok as [Hok Hsz].
    apply andb_prop in Hok as [Hok1 Hok2].
    econstructor.
    + apply (proj2 (eval_expr_transport e le m)); eassumption.
    + apply (proj1 (eval_expr_transport e le m)); eassumption.
    + exact Hc.
    + eapply assign_loc_transport; eassumption.
  - intros e le m id a v Ha vars Hd Hok. simpl in Hok.
    constructor. apply (proj1 (eval_expr_transport e le m)); eassumption.
  - intros e le m optid a al tyargs tyres cconv vf vargs f t m' vres Hcl Ha Hal Hf Hty Hcall IH vars Hd Hok.
    destruct a; try (simpl in Hok; discriminate).
    destruct t0; try (simpl in Hok; discriminate).
    simpl in Hok. apply andb_prop in Hok as [Hok Hals]. apply andb_prop in Hok as [HinC HnV].
    assert (Hnone : e!i = None).
    { destruct (e!i) as [[bb tt]|] eqn:Hei; [|reflexivity]. exfalso.
      apply Hd in Hei. apply (in_map fst) in Hei. simpl in Hei.
      apply negb_true_iff in HnV. apply not_true_iff_false in HnV. apply HnV.
      apply existsb_exists. exists i. split; [exact Hei|apply Pos.eqb_refl]. }
    assert (HinC' : In i C).
    { apply existsb_exists in HinC. destruct HinC as [x [Hx Hxe]].
      apply Pos.eqb_eq in Hxe. subst x. exact Hx. }
    inversion Ha; subst.
    match goal with Hlv : eval_lvalue ge1 e le m (Evar i _) _ _ _ |- _ =>
      inversion Hlv; subst end.
    + congruence.
    + match goal with Hdr : deref_loc _ m _ _ _ _ |- _ =>
        inversion Hdr; subst; try discriminate end.
      epose proof (HC _ HinC' _ f ltac:(eassumption) (find_funct_ptr_of_funct _ f Hf)) as Hcallable.
      destruct Hcallable as [[b2 [Hs2 Hf2]] Hokf].
      eapply exec_Scall with (vf := Vptr b2 Ptrofs.zero).
      * exact Hcl.
      * eapply eval_Elvalue.
        -- apply eval_Evar_global; [exact Hnone|exact Hs2].
        -- apply deref_loc_reference; reflexivity.
      * eapply eval_exprlist_transport; eassumption.
      * unfold Genv.find_funct. rewrite pred_dec_true by reflexivity. exact Hf2.
      * exact Hty.
      * apply IH. exact Hokf.
  - intros; simpl in *; discriminate.
  - intros e le m s1 s2 t1 le1 m1 t2 le2 m2 out Hs1 IH1 Hs2 IH2 vars Hd Hok. simpl in Hok.
    apply andb_prop in Hok as [Ho1 Ho2].
    econstructor; [eapply IH1; eassumption|eapply IH2; eassumption].
  - intros e le m s1 s2 t1 le1 m1 out Hs1 IH1 Hne vars Hd Hok. simpl in Hok.
    apply andb_prop in Hok as [Ho1 Ho2].
    eapply exec_Sseq_2; [eapply IH1; eassumption|exact Hne].
  - intros e le m a s1 s2 v1 b t le' m' out Ha Hb Hs IH vars Hd Hok. simpl in Hok.
    apply andb_prop in Hok as [Hoa Hbr].
    econstructor.
    + apply (proj1 (eval_expr_transport e le m)); eassumption.
    + exact Hb.
    + apply IH with (vars := vars); [exact Hd|].
      destruct (const_cond a) as [c|] eqn:Hcc.
      * assert (Hbc : b = c) by (eapply const_cond_sound; eassumption). subst c.
        destruct b; exact Hbr.
      * apply andb_prop in Hbr as [Hb1 Hb2]. destruct b; assumption.
  - intros; constructor.
  - intros e le m a v Ha vars Hd Hok. simpl in Hok.
    constructor. apply (proj1 (eval_expr_transport e le m)); eassumption.
  - intros; constructor.
  - intros; constructor.
  - intros e le m s1 s2 t le' m' out' out Hs IH Hbr vars Hd Hok. simpl in Hok.
    apply andb_prop in Hok as [Ho1 Ho2].
    eapply exec_Sloop_stop1; [eapply IH; eassumption|exact Hbr].
  - intros e le m s1 s2 t1 le1 m1 out1 t2 le2 m2 out2 out Hs1 IH1 Hnc Hs2 IH2 Hbr vars Hd Hok. simpl in Hok.
    apply andb_prop in Hok as [Ho1 Ho2].
    eapply exec_Sloop_stop2; [eapply IH1; eassumption|exact Hnc|eapply IH2; eassumption|exact Hbr].
  - intros e le m s1 s2 t1 le1 m1 out1 t2 le2 m2 t3 le3 m3 out Hs1 IH1 Hnc Hs2 IH2 Hl IH3 vars Hd Hok.
    pose proof Hok as Hok'. simpl in Hok. apply andb_prop in Hok as [Ho1 Ho2].
    eapply exec_Sloop_loop; [eapply IH1; eassumption|exact Hnc|eapply IH2; eassumption|eapply IH3; eassumption].
  - intros; simpl in *; discriminate.
  - intros m f vargs t e le1 le2 m1 m2 out vres m3 Hentry Hexec IH Hres Hfree Hok.
    simpl in Hok. apply andb_prop in Hok as [Hv Hbody].
    inversion Hentry as [HN1 HN2 HDj Halloc Hbind]; subst.
    assert (Hdom : edom e (fn_vars f)).
    { intros id b ty He. destruct (alloc_variables_dom _ _ _ _ _ Halloc id b ty He) as [H1|H1];
        [rewrite PTree.gempty in H1; discriminate|exact H1]. }
    econstructor.
    + econstructor; try eassumption. eapply alloc_variables_transport; eassumption.
    + eapply IH with (vars := fn_vars f); [exact Hdom|exact Hbody].
    + exact Hres.
    + rewrite <- (blocks_of_env_agree e (fn_vars f) Hdom Hv). exact Hfree.
  - intros; simpl in *; discriminate.
Qed.

Lemma transportable_of_entries (L : list (ident * function)) :
  (forall id f, In (id, f) L -> exists b1 b2,
     Genv.find_symbol ge1 id = Some b1 /\ Genv.find_funct_ptr ge1 b1 = Some (Internal f) /\
     Genv.find_symbol ge2 id = Some b2 /\ Genv.find_funct_ptr ge2 b2 = Some (Internal f)) ->
  (forall id f, In (id, f) L -> fundef_okb (map fst L) (Internal f) = true) ->
  transportable (map fst L).
Proof.
  intros HE HO id Hin b1 fd Hs Hf.
  apply in_map_iff in Hin as [[id' f] [Heq Hin]]. simpl in Heq; subst id'.
  destruct (HE id f Hin) as (b1' & b2 & Hs1 & Hf1 & Hs2 & Hf2).
  rewrite Hs in Hs1. inversion Hs1; subst b1'.
  rewrite Hf in Hf1. inversion Hf1; subst fd.
  split; [exists b2; auto | exact (HO id f Hin)].
Qed.

(** The user-facing form: a call of a checked helper in [ge1] is a call in [ge2]. *)
Theorem transport_funcall (L : list (ident * function))
    (HE : forall id f, In (id, f) L -> exists b1 b2,
     Genv.find_symbol ge1 id = Some b1 /\ Genv.find_funct_ptr ge1 b1 = Some (Internal f) /\
     Genv.find_symbol ge2 id = Some b2 /\ Genv.find_funct_ptr ge2 b2 = Some (Internal f))
    (HO : forall id f, In (id, f) L -> fundef_okb (map fst L) (Internal f) = true)
    id f (Hin : In (id, f) L) m args t m' res :
  Clight2.eval_funcall ge1 m (Internal f) args t m' res ->
  Clight2.eval_funcall ge2 m (Internal f) args t m' res.
Proof.
  intros H. eapply (proj2 (transport_main (map fst L) (transportable_of_entries L HE HO)));
    [exact H|exact (HO id f Hin)].
Qed.
End Checks.
