(** Execution transport with explicit local-variable binding. A local name
    may also occur in the global symbol table; no global-variable access is
    transported. The caller's entry establishes the full local domain. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps Errors Memory Values.
From compcert Require Import Globalenvs Events ClightBigstep.
Import ListNotations.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 10.
Require Import C.jet_transport.


Section LocalTransport.
Variables ge1 ge2:Clight.genv.
Fixpoint locals_expr_okb (V:list ident) (a : expr) : bool :=
  match a with
  | Econst_int _ _ | Econst_float _ _ | Econst_single _ _ | Econst_long _ _ => true
  | Evar id _ => existsb (Pos.eqb id) V || match Genv.find_symbol ge1 id with None => true | Some _ => false end
  | Etempvar _ _ => true
  | Ederef a1 _ => locals_expr_okb V a1
  | Efield a1 i _ => locals_expr_okb V a1 && fieldb ge1 ge2 (typeof a1) i
  | Eaddrof a1 _ => locals_expr_okb V a1
  | Eunop _ a1 _ => locals_expr_okb V a1
  | Ebinop op a1 a2 _ =>
      locals_expr_okb V a1 && locals_expr_okb V a2 && binop_agreeb (genv_cenv ge1) (genv_cenv ge2) op (typeof a1) (typeof a2)
  | Ecast a1 _ => locals_expr_okb V a1
  | Esizeof t _ => szb ge1 ge2 t
  | Ealignof t _ => alb ge1 ge2 t
  end.

Definition locals_exprs_okb (V:list ident) (al : list expr) : bool := forallb (locals_expr_okb V) al.

Fixpoint locals_stmt_okb (C V : list ident) (s : statement) : bool :=
  match s with
  | Sskip => true
  | Sassign a1 a2 => locals_expr_okb V a1 && locals_expr_okb V a2 && szb ge1 ge2 (typeof a1) && albb ge1 ge2 (typeof a1)
  | Sset _ a => locals_expr_okb V a
  | Scall _ (Evar id (Tfunction _ _ _)) al =>
      existsb (Pos.eqb id) C && negb (existsb (Pos.eqb id) V) && locals_exprs_okb V al
  | Scall _ _ _ => false
  | Sbuiltin _ _ _ _ => false
  | Ssequence s1 s2 => locals_stmt_okb C V s1 && locals_stmt_okb C V s2
  | Sifthenelse a s1 s2 =>
      locals_expr_okb V a &&
      match const_cond a with
      | Some true => locals_stmt_okb C V s1
      | Some false => locals_stmt_okb C V s2
      | None => locals_stmt_okb C V s1 && locals_stmt_okb C V s2
      end
  | Sloop s1 s2 => locals_stmt_okb C V s1 && locals_stmt_okb C V s2
  | Sbreak | Scontinue => true
  | Sreturn None => true
  | Sreturn (Some a) => locals_expr_okb V a
  | Sswitch _ _ => false
  | Slabel _ _ => false
  | Sgoto _ => false
  end.

Definition locals_vars_okb (vars : list (ident * type)) : bool := forallb (fun p => szb ge1 ge2 (snd p)) vars.

Definition locals_fundef_okb (C : list ident) (fd : fundef) : bool :=
  match fd with
  | Internal f => locals_vars_okb (fn_vars f) && locals_stmt_okb C (map fst (fn_vars f)) (fn_body f)
  | External _ _ _ _ => false
  end.

(** A callee name is locals_transportable when both genvs define it by the same
    internal function and that function's body passes the check. *)
Definition locals_callable (C : list ident) (id : ident) : Prop :=
  forall b1 fd, Genv.find_symbol ge1 id = Some b1 -> Genv.find_funct_ptr ge1 b1 = Some fd ->
    (exists b2, Genv.find_symbol ge2 id = Some b2 /\ Genv.find_funct_ptr ge2 b2 = Some fd) /\
    locals_fundef_okb C fd = true.

Definition locals_transportable (C : list ident) : Prop := forall id, In id C -> locals_callable C id.

Lemma locals_eval_expr_transport e le m V (Bound:forall id,In id V ->exists b ty,e!id=Some (b,ty)) :
  (forall a v, eval_expr ge1 e le m a v -> locals_expr_okb V a = true -> eval_expr ge2 e le m a v) /\
  (forall a b ofs bf, eval_lvalue ge1 e le m a b ofs bf -> locals_expr_okb V a = true ->
     eval_lvalue ge2 e le m a b ofs bf).
Proof.
  apply (eval_expr_lvalue_ind ge1 e le m
    (fun a v => locals_expr_okb V a = true -> eval_expr ge2 e le m a v)
    (fun a b ofs bf => locals_expr_okb V a = true -> eval_lvalue ge2 e le m a b ofs bf)).
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
  - intros ty1 ty Hok. simpl in Hok. rewrite (szb_eq ge1 ge2 _ Hok). constructor.
  - intros ty1 ty Hok. simpl in Hok. rewrite (alb_eq ge1 ge2 _ Hok). constructor.
  - intros a loc ofs bf v Hl IH Hd Hok. econstructor; [apply IH; exact Hok|exact Hd].
  - intros id l ty He _. constructor; exact He.
  - intros id l ty He Hs Hok. simpl in Hok. rewrite Hs in Hok.
    apply orb_true_iff in Hok as [Local|Impossible];[|discriminate].
    apply existsb_exists in Local as (other & Member & Same).
    apply Pos.eqb_eq in Same;subst other.
    destruct (Bound id Member) as (bl & tyl & Present);congruence.
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

Lemma locals_eval_exprlist_transport e le m V (Bound:forall id,In id V ->exists b ty,e!id=Some (b,ty)) al tys vs :
  eval_exprlist ge1 e le m al tys vs -> locals_exprs_okb V al = true -> eval_exprlist ge2 e le m al tys vs.
Proof.
  induction 1; intros Hok; [constructor|].
  simpl in Hok. apply andb_prop in Hok as [Ha Hl].
  econstructor; [apply (proj1 (locals_eval_expr_transport e le m V Bound)); eauto|eauto|apply IHeval_exprlist; exact Hl].
Qed.


Lemma locals_alloc_variables_bound e m vars ef mf:
 alloc_variables ge1 e m vars ef mf ->forall id,
 (exists b ty,e!id=Some (b,ty)) \/ In id (map fst vars) ->
 exists b ty,ef!id=Some (b,ty).
Proof.
 induction 1;intros key Present.
 - destruct Present as [Present|[]];exact Present.
 - apply IHalloc_variables.
   destruct Present as [(old & oldty & Found)|[Same|Rest]].
   + left;destruct (peq key id) as [->|Different].
     * exists b1,ty;apply PTree.gss.
     * exists old,oldty;rewrite PTree.gso by exact Different;exact Found.
   + left;subst key;exists b1,ty;apply PTree.gss.
   + right;exact Rest.
Qed.
Theorem locals_transport_main (C : list ident) (HC : locals_transportable C) :
  (forall e le m s t le' m' out, Clight2.exec_stmt ge1 e le m s t le' m' out ->
     forall vars, edom e vars -> (forall id,In id (map fst vars) ->exists b ty,e!id=Some (b,ty)) -> locals_stmt_okb C (map fst vars) s = true ->
     Clight2.exec_stmt ge2 e le m s t le' m' out) /\
  (forall m fd args t m' res, Clight2.eval_funcall ge1 m fd args t m' res ->
     locals_fundef_okb C fd = true -> Clight2.eval_funcall ge2 m fd args t m' res).
Proof.
  apply (exec_stmt_funcall_ind function_entry2 ge1
    (fun e le m s t le' m' out => forall vars, edom e vars -> (forall id,In id (map fst vars) ->exists b ty,e!id=Some (b,ty)) -> locals_stmt_okb C (map fst vars) s = true ->
       Clight2.exec_stmt ge2 e le m s t le' m' out)
    (fun m fd args t m' res => locals_fundef_okb C fd = true -> Clight2.eval_funcall ge2 m fd args t m' res)).
  - intros; constructor.
  - intros e le m a1 a2 loc ofs bf v2 v m' Hl Hr Hc Ha vars Hd Bound Hok. simpl in Hok.
    apply andb_prop in Hok as [Hok Hal]. apply andb_prop in Hok as [Hok Hsz].
    apply andb_prop in Hok as [Hok1 Hok2].
    econstructor.
    + apply (proj2 (locals_eval_expr_transport e le m (map fst vars) Bound)); eassumption.
    + apply (proj1 (locals_eval_expr_transport e le m (map fst vars) Bound)); eassumption.
    + exact Hc.
    + eapply (assign_loc_transport ge1 ge2); eassumption.
  - intros e le m id a v Ha vars Hd Bound Hok. simpl in Hok.
    constructor. apply (proj1 (locals_eval_expr_transport e le m (map fst vars) Bound)); eassumption.
  - intros e le m optid a al tyargs tyres cconv vf vargs f t m' vres Hcl Ha Hal Hf Hty Hcall IH vars Hd Bound Hok.
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
      epose proof (HC _ HinC' _ f ltac:(eassumption) (find_funct_ptr_of_funct ge1 _ f Hf)) as Hcallable.
      destruct Hcallable as [[b2 [Hs2 Hf2]] Hokf].
      eapply exec_Scall with (vf := Vptr b2 Ptrofs.zero).
      * exact Hcl.
      * eapply eval_Elvalue.
        -- apply eval_Evar_global; [exact Hnone|exact Hs2].
        -- apply deref_loc_reference; reflexivity.
      * eapply locals_eval_exprlist_transport; eassumption.
      * unfold Genv.find_funct. rewrite pred_dec_true by reflexivity. exact Hf2.
      * exact Hty.
      * apply IH. exact Hokf.
  - intros; simpl in *; discriminate.
  - intros e le m s1 s2 t1 le1 m1 t2 le2 m2 out Hs1 IH1 Hs2 IH2 vars Hd Bound Hok. simpl in Hok.
    apply andb_prop in Hok as [Ho1 Ho2].
    econstructor; [eapply IH1; eassumption|eapply IH2; eassumption].
  - intros e le m s1 s2 t1 le1 m1 out Hs1 IH1 Hne vars Hd Bound Hok. simpl in Hok.
    apply andb_prop in Hok as [Ho1 Ho2].
    eapply exec_Sseq_2; [eapply IH1; eassumption|exact Hne].
  - intros e le m a s1 s2 v1 b t le' m' out Ha Hb Hs IH vars Hd Bound Hok. simpl in Hok.
    apply andb_prop in Hok as [Hoa Hbr].
    econstructor.
    + apply (proj1 (locals_eval_expr_transport e le m (map fst vars) Bound)); eassumption.
    + exact Hb.
    + apply IH with (vars := vars); [exact Hd|exact Bound|].
      destruct (const_cond a) as [c|] eqn:Hcc.
      * assert (Hbc : b = c) by (eapply const_cond_sound; eassumption). subst c.
        destruct b; exact Hbr.
      * apply andb_prop in Hbr as [Hb1 Hb2]. destruct b; assumption.
  - intros; constructor.
  - intros e le m a v Ha vars Hd Bound Hok. simpl in Hok.
    constructor. apply (proj1 (locals_eval_expr_transport e le m (map fst vars) Bound)); eassumption.
  - intros; constructor.
  - intros; constructor.
  - intros e le m s1 s2 t le' m' out' out Hs IH Hbr vars Hd Bound Hok. simpl in Hok.
    apply andb_prop in Hok as [Ho1 Ho2].
    eapply exec_Sloop_stop1; [eapply IH; eassumption|exact Hbr].
  - intros e le m s1 s2 t1 le1 m1 out1 t2 le2 m2 out2 out Hs1 IH1 Hnc Hs2 IH2 Hbr vars Hd Bound Hok. simpl in Hok.
    apply andb_prop in Hok as [Ho1 Ho2].
    eapply exec_Sloop_stop2; [eapply IH1; eassumption|exact Hnc|eapply IH2; eassumption|exact Hbr].
  - intros e le m s1 s2 t1 le1 m1 out1 t2 le2 m2 t3 le3 m3 out Hs1 IH1 Hnc Hs2 IH2 Hl IH3 vars Hd Bound Hok.
    pose proof Hok as Hok'. simpl in Hok. apply andb_prop in Hok as [Ho1 Ho2].
    eapply exec_Sloop_loop; [eapply IH1; eassumption|exact Hnc|eapply IH2; eassumption|eapply IH3; eassumption].
  - intros; simpl in *; discriminate.
  - intros m f vargs t e le1 le2 m1 m2 out vres m3 Hentry Hexec IH Hres Hfree Hok.
    simpl in Hok. apply andb_prop in Hok as [Hv Hbody].
    inversion Hentry as [HN1 HN2 HDj Halloc Hbind]; subst.
    assert (Hdom : edom e (fn_vars f)).
    { intros id b ty He. destruct (alloc_variables_dom ge1 _ _ _ _ _ Halloc id b ty He) as [H1|H1];
        [rewrite PTree.gempty in H1; discriminate|exact H1]. }
    econstructor.
    + econstructor; try eassumption. eapply (alloc_variables_transport ge1 ge2); eassumption.
    + eapply IH with (vars := fn_vars f); [exact Hdom| |exact Hbody].
      intros id Member;eapply locals_alloc_variables_bound;[exact Halloc|right;exact Member].
    + exact Hres.
    + rewrite <- (blocks_of_env_agree ge1 ge2 e (fn_vars f) Hdom Hv). exact Hfree.
  - intros; simpl in *; discriminate.
Qed.

Lemma locals_transportable_of_entries (L : list (ident * function)) :
  (forall id f, In (id, f) L -> exists b1 b2,
     Genv.find_symbol ge1 id = Some b1 /\ Genv.find_funct_ptr ge1 b1 = Some (Internal f) /\
     Genv.find_symbol ge2 id = Some b2 /\ Genv.find_funct_ptr ge2 b2 = Some (Internal f)) ->
  (forall id f, In (id, f) L -> locals_fundef_okb (map fst L) (Internal f) = true) ->
  locals_transportable (map fst L).
Proof.
  intros HE HO id Hin b1 fd Hs Hf.
  apply in_map_iff in Hin as [[id' f] [Heq Hin]]. simpl in Heq; subst id'.
  destruct (HE id f Hin) as (b1' & b2 & Hs1 & Hf1 & Hs2 & Hf2).
  rewrite Hs in Hs1. inversion Hs1; subst b1'.
  rewrite Hf in Hf1. inversion Hf1; subst fd.
  split; [exists b2; auto | exact (HO id f Hin)].
Qed.

(** The user-facing form: a call of a checked helper in [ge1] is a call in [ge2]. *)
Theorem locals_transport_funcall (L : list (ident * function))
    (HE : forall id f, In (id, f) L -> exists b1 b2,
     Genv.find_symbol ge1 id = Some b1 /\ Genv.find_funct_ptr ge1 b1 = Some (Internal f) /\
     Genv.find_symbol ge2 id = Some b2 /\ Genv.find_funct_ptr ge2 b2 = Some (Internal f))
    (HO : forall id f, In (id, f) L -> locals_fundef_okb (map fst L) (Internal f) = true)
    id f (Hin : In (id, f) L) m args t m' res :
  Clight2.eval_funcall ge1 m (Internal f) args t m' res ->
  Clight2.eval_funcall ge2 m (Internal f) args t m' res.
Proof.
  intros H. eapply (proj2 (locals_transport_main (map fst L) (locals_transportable_of_entries L HE HO)));
    [exact H|exact (HO id f Hin)].
Qed.
End LocalTransport.
